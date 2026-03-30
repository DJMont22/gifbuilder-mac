
import json
import os
import queue
import re
import shutil
import sys
import threading
import traceback
import tempfile
import zipfile
from dataclasses import dataclass, replace
from typing import Any, Dict, List, Optional, Tuple

import tkinter as tk
from tkinter import ttk, filedialog, messagebox

try:
    from PIL import Image, ImageTk, ImageEnhance, ImageOps
except Exception as exc:
    raise SystemExit(
        "This app requires Pillow.\nInstall it with:\n\n    pip install pillow\n"
        f"\nImport error: {exc}"
    )

try:
    import cv2
    CV2_IMPORT_ERROR: Optional[Exception] = None
except Exception as exc:
    cv2 = None
    CV2_IMPORT_ERROR = exc


APP_TITLE = "GIF Builder Studio"
APP_ICON_FILENAME = "gbs icon.ico"
PREVIEW_SIZE = (520, 320)
PREVIEW_REFRESH_DELAY_MS = 140
SLIDER_PREVIEW_REFRESH_DELAY_MS = 260
VIDEO_IMPORT_MAX_FRAMES = 500
PROJECT_ARCHIVE_VERSION = 1
EXPORT_SIZE_PRESETS: Dict[str, Optional[Tuple[int, int]]] = {
    "original": None,
    "custom": None,
    "256 x 256": (256, 256),
    "320 x 240": (320, 240),
    "480 x 270": (480, 270),
    "512 x 512": (512, 512),
    "640 x 360": (640, 360),
    "640 x 480": (640, 480),
    "720 x 480": (720, 480),
    "800 x 600": (800, 600),
    "1024 x 1024": (1024, 1024),
}
SUPPORTED_IMAGE_TYPES = [
    ("Image files", "*.png *.jpg *.jpeg *.bmp *.webp *.gif"),
    ("PNG", "*.png"),
    ("JPEG", "*.jpg *.jpeg"),
    ("BMP", "*.bmp"),
    ("WEBP", "*.webp"),
    ("GIF", "*.gif"),
    ("All files", "*.*"),
]
SUPPORTED_VIDEO_TYPES = [
    ("Video files", "*.mp4 *.mov *.avi *.mkv *.wmv *.m4v *.webm"),
    ("MP4", "*.mp4"),
    ("MOV", "*.mov"),
    ("AVI", "*.avi"),
    ("MKV", "*.mkv"),
    ("WMV", "*.wmv"),
    ("WEBM", "*.webm"),
    ("All files", "*.*"),
]
SUPPORTED_PROJECT_TYPES = [
    ("GIF Builder Studio Projects", "*.gbs"),
    ("All files", "*.*"),
]


def install_exception_popup() -> None:
    def handle_exception(exc_type, exc_value, exc_tb):
        tb = "".join(traceback.format_exception(exc_type, exc_value, exc_tb))
        try:
            root = tk._default_root
            if root is not None:
                messagebox.showerror("Unhandled Error", tb)
            else:
                sys.stderr.write(tb)
        except Exception:
            sys.stderr.write(tb)

    sys.excepthook = handle_exception


@dataclass
class FrameItem:
    path: str
    display_name: Optional[str] = None


@dataclass(frozen=True)
class ImageCacheEntry:
    mtime_ns: int
    size: int
    image: Image.Image


@dataclass(frozen=True)
class RenderSettings:
    frame_paths: Tuple[str, ...]
    duration_ms: int
    resize_mode: str
    export_size: Optional[Tuple[int, int]]
    bg_rgba: Tuple[int, int, int, int]
    enable_effects: bool
    reverse_order: bool
    pingpong: bool
    grayscale: bool
    flip_h: bool
    flip_v: bool
    brightness: Optional[float]
    contrast: Optional[float]
    sharpness: Optional[float]
    rotate_degrees: int


@dataclass(frozen=True)
class PreviewRenderJob:
    request_id: int
    settings: RenderSettings
    preview_size: Tuple[int, int]
    autoplay_if_new: bool
    force_play: bool


class GIFBuilderApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title(APP_TITLE)
        self.root.geometry("1280x820")
        self.root.minsize(1120, 760)
        self._apply_window_icon(self.root)

        self.frames: List[FrameItem] = []
        self.preview_frames: List[ImageTk.PhotoImage] = []
        self.preview_index = 0
        self.preview_after_id = None
        self.preview_refresh_after_id = None
        self.preview_playing = False
        self.preview_request_id = 0
        self.preview_result_after_id = None
        self.current_preview_signature: Optional[Tuple[int, RenderSettings, Tuple[int, int]]] = None
        self.last_export_path: Optional[str] = None
        self.effect_control_widgets: List[ttk.Widget] = []
        self.image_cache: Dict[str, ImageCacheEntry] = {}
        self.image_cache_lock = threading.Lock()
        self.preview_job_lock = threading.Lock()
        self.pending_preview_job: Optional[PreviewRenderJob] = None
        self.preview_job_event = threading.Event()
        self.preview_stop_event = threading.Event()
        self.preview_result_queue: "queue.Queue[Tuple[int, Optional[List[Image.Image]], Optional[str], bool, bool, int]]" = queue.Queue()
        self.preview_worker = threading.Thread(target=self._preview_worker_loop, name="gif-preview-renderer", daemon=True)
        self.preview_worker.start()
        self.session_tempdir = tempfile.mkdtemp(prefix="gif_builder_studio_")
        self.imported_video_counter = 0
        self.current_project_path: Optional[str] = None
        self.loaded_video_path: Optional[str] = None
        self.loaded_video_info: Optional[Dict[str, float | int | str]] = None
        self.video_picker_window: Optional[tk.Toplevel] = None
        self.video_picker_capture = None
        self.video_picker_after_id = None
        self.video_picker_play_after_id = None
        self.video_picker_playing = False
        self.video_picker_target = "start"
        self.video_picker_play_button = None
        self.video_picker_pause_button = None
        self.video_picker_preview_photo: Optional[ImageTk.PhotoImage] = None
        self.busy_dialog: Optional[tk.Toplevel] = None
        self.busy_dialog_after_id = None
        self.busy_spinner_angle = 0
        self.busy_spinner_canvas: Optional[tk.Canvas] = None
        self.busy_spinner_arc = None
        self.busy_progressbar: Optional[ttk.Progressbar] = None

        self._build_style()
        self._build_variables()
        self._build_ui()
        self._register_preview_traces()
        self._bind_shortcuts()
        self._update_ui_state()
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)
        self.preview_result_after_id = self.root.after(40, self._poll_preview_results)
        self.root.after_idle(self._maximize_window)

    def _build_style(self) -> None:
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except Exception:
            pass

    def _find_app_icon_path(self) -> Optional[str]:
        candidate_dirs: List[str] = []
        launched_path = sys.argv[0] if sys.argv else ""
        if launched_path:
            candidate_dirs.append(os.path.dirname(os.path.abspath(launched_path)))
        executable_path = getattr(sys, "executable", "")
        if executable_path:
            candidate_dirs.append(os.path.dirname(os.path.abspath(executable_path)))
        candidate_dirs.append(os.path.dirname(os.path.abspath(__file__)))
        candidate_dirs.append(os.getcwd())

        seen: set[str] = set()
        for base_dir in candidate_dirs:
            if not base_dir or base_dir in seen:
                continue
            seen.add(base_dir)
            icon_path = os.path.join(base_dir, APP_ICON_FILENAME)
            if os.path.exists(icon_path):
                return icon_path
        return None

    def _apply_window_icon(self, window) -> None:
        icon_path = self._find_app_icon_path()
        if not icon_path:
            return
        try:
            window.iconbitmap(icon_path)
        except Exception:
            try:
                window.wm_iconbitmap(icon_path)
            except Exception:
                pass

    def _build_variables(self) -> None:
        self.duration_ms_var = tk.IntVar(value=120)
        self.loop_forever_var = tk.BooleanVar(value=True)
        self.loop_count_var = tk.IntVar(value=0)
        self.resize_mode_var = tk.StringVar(value="original")
        self.export_size_preset_var = tk.StringVar(value="original")
        self.export_width_var = tk.IntVar(value=0)
        self.export_height_var = tk.IntVar(value=0)
        self.bg_hex_var = tk.StringVar(value="#000000")
        self.autoplay_var = tk.BooleanVar(value=True)

        # Effects are off unless enabled.
        self.enable_effects_var = tk.BooleanVar(value=False)
        self.reverse_order_var = tk.BooleanVar(value=False)
        self.pingpong_var = tk.BooleanVar(value=False)
        self.grayscale_var = tk.BooleanVar(value=False)
        self.flip_h_var = tk.BooleanVar(value=False)
        self.flip_v_var = tk.BooleanVar(value=False)

        self.enable_brightness_var = tk.BooleanVar(value=False)
        self.brightness_var = tk.DoubleVar(value=1.0)
        self.brightness_text_var = tk.StringVar(value="1.00")

        self.enable_contrast_var = tk.BooleanVar(value=False)
        self.contrast_var = tk.DoubleVar(value=1.0)
        self.contrast_text_var = tk.StringVar(value="1.00")

        self.enable_sharpness_var = tk.BooleanVar(value=False)
        self.sharpness_var = tk.DoubleVar(value=1.0)
        self.sharpness_text_var = tk.StringVar(value="1.00")

        self.enable_rotate_var = tk.BooleanVar(value=False)
        self.rotate_var = tk.IntVar(value=0)

        self.video_path_var = tk.StringVar(value="No video selected")
        self.video_info_var = tk.StringVar(value=self._default_video_info_text())
        self.video_start_var = tk.DoubleVar(value=0.0)
        self.video_end_var = tk.DoubleVar(value=2.0)
        self.video_sample_fps_var = tk.DoubleVar(value=10.0)
        self.video_picker_time_var = tk.DoubleVar(value=0.0)
        self.video_picker_info_var = tk.StringVar(value="Choose a video to preview timestamps.")
        self.video_clip_info_var = tk.StringVar(value="Clip: start 00:00.00 | end 00:02.00 | length 2.00s")
        self.busy_label_var = tk.StringVar(value="")
        self.busy_progress_var = tk.StringVar(value="")
        self.busy_percent_var = tk.StringVar(value="0%")

        self.status_var = tk.StringVar(value="Add images to begin.")
        self.preview_info_var = tk.StringVar(value="Preview: no frames loaded")

    def _build_ui(self) -> None:
        outer = ttk.Frame(self.root, padding=10)
        outer.pack(fill="both", expand=True)

        left = ttk.Frame(outer)
        left.pack(side="left", fill="both", padx=(0, 10))

        right = ttk.Frame(outer)
        right.pack(side="left", fill="both", expand=True)

        self._build_left_panel(left)
        self._build_right_panel(right)

        status = ttk.Label(self.root, textvariable=self.status_var, anchor="w", padding=(10, 6))
        status.pack(fill="x", side="bottom")

    def _build_left_panel(self, parent: ttk.Frame) -> None:
        notebook = ttk.Notebook(parent)
        notebook.pack(fill="both", expand=True)

        frames_tab = ttk.Frame(notebook, padding=0)
        video_tab = ttk.Frame(notebook, padding=0)
        notebook.add(frames_tab, text="Frames")
        notebook.add(video_tab, text="Video Clip Import")

        self._build_frames_panel(frames_tab)
        self._build_video_import_panel(video_tab)

    def _build_frames_panel(self, parent: ttk.Frame) -> None:
        files_card = ttk.LabelFrame(parent, text="Frames / Image Order", padding=8)
        files_card.pack(fill="both", expand=True)

        add_row = ttk.Frame(files_card)
        add_row.pack(fill="x", pady=(0, 8))

        ttk.Button(add_row, text="Add Images", command=self.add_images).pack(side="left", padx=(0, 6))
        ttk.Button(add_row, text="Add Folder", command=self.add_folder).pack(side="left", padx=(0, 6))
        ttk.Button(add_row, text="Choose Video", command=self.choose_video).pack(side="left", padx=(0, 6))
        ttk.Button(add_row, text="Remove Selected", command=self.remove_selected).pack(side="left", padx=(0, 6))
        ttk.Button(add_row, text="Clear", command=self.clear_frames).pack(side="left")

        list_frame = ttk.Frame(files_card)
        list_frame.pack(fill="both", expand=True)

        self.listbox = tk.Listbox(
            list_frame,
            selectmode=tk.EXTENDED,
            activestyle="dotbox",
            width=42,
            height=28
        )
        self.listbox.pack(side="left", fill="both", expand=True)
        self.listbox.bind("<<ListboxSelect>>", lambda e: self.schedule_preview_refresh())

        yscroll = ttk.Scrollbar(list_frame, orient="vertical", command=self.listbox.yview)
        yscroll.pack(side="left", fill="y")
        self.listbox.config(yscrollcommand=yscroll.set)

        order_row = ttk.Frame(files_card)
        order_row.pack(fill="x", pady=(8, 0))

        ttk.Button(order_row, text="Top", command=self.move_top).pack(side="left", padx=(0, 6))
        ttk.Button(order_row, text="Up", command=self.move_up).pack(side="left", padx=(0, 6))
        ttk.Button(order_row, text="Down", command=self.move_down).pack(side="left", padx=(0, 6))
        ttk.Button(order_row, text="Bottom", command=self.move_bottom).pack(side="left")

        tips = ttk.Label(
            files_card,
            text="Tip: choose images, reorder them, preview the animation, then export to GIF.",
            wraplength=320,
            justify="left"
        )
        tips.pack(fill="x", pady=(10, 0))

    def _build_video_import_panel(self, parent: ttk.Frame) -> None:
        card = ttk.LabelFrame(parent, text="Video Clip Import", padding=8)
        card.pack(fill="both", expand=True)

        top_row = ttk.Frame(card)
        top_row.pack(fill="x", pady=(0, 6))
        ttk.Button(top_row, text="Browse Video", command=self.choose_video).pack(side="left")

        path_label = ttk.Label(card, textvariable=self.video_path_var, wraplength=360, justify="left")
        path_label.pack(fill="x", pady=(0, 8))

        info_label = ttk.Label(card, textvariable=self.video_info_var, wraplength=360, justify="left")
        info_label.pack(fill="x", pady=(0, 8))

        row1 = ttk.Frame(card)
        row1.pack(fill="x", pady=(0, 6))
        ttk.Label(row1, text="Start (sec):").pack(side="left")
        ttk.Entry(row1, textvariable=self.video_start_var, width=8).pack(side="left", padx=(6, 12))
        ttk.Button(row1, text="Pick Start", command=lambda: self.open_timestamp_picker("start")).pack(side="left")

        row1b = ttk.Frame(card)
        row1b.pack(fill="x", pady=(0, 6))
        ttk.Label(row1b, text="End (sec):").pack(side="left")
        ttk.Entry(row1b, textvariable=self.video_end_var, width=8).pack(side="left", padx=(6, 12))
        ttk.Button(row1b, text="Pick End", command=lambda: self.open_timestamp_picker("end")).pack(side="left")

        row2 = ttk.Frame(card)
        row2.pack(fill="x", pady=(0, 6))
        ttk.Label(row2, text="Sample FPS:").pack(side="left")
        ttk.Entry(row2, textvariable=self.video_sample_fps_var, width=8).pack(side="left", padx=(6, 0))

        import_tip = ttk.Label(
            card,
            text="Pick a start and end time, then import the chopped clip as PNG frames for GIF export.",
            wraplength=360,
            justify="left"
        )
        import_tip.pack(fill="x", pady=(0, 8))

        ttk.Label(card, textvariable=self.video_clip_info_var).pack(anchor="w", pady=(0, 8))

        ttk.Button(card, text="Import Clip Frames", command=self.import_video_clip).pack(anchor="w")

    def _build_right_panel(self, parent: ttk.Frame) -> None:
        preview_card = ttk.LabelFrame(parent, text="Live Preview", padding=8)
        preview_card.pack(fill="both", expand=True)

        self.preview_label = ttk.Label(preview_card, anchor="center")
        self.preview_label.pack(fill="both", expand=True)
        self.preview_label.bind("<Configure>", lambda e: self.schedule_preview_refresh())

        preview_controls = ttk.Frame(preview_card)
        preview_controls.pack(fill="x", pady=(8, 0))

        ttk.Button(preview_controls, text="Play", command=self.start_preview).pack(side="left", padx=(0, 6))
        ttk.Button(preview_controls, text="Pause", command=self.stop_preview).pack(side="left", padx=(0, 6))
        ttk.Button(preview_controls, text="Refresh Preview", command=self.refresh_preview).pack(side="left", padx=(0, 8))
        ttk.Checkbutton(preview_controls, text="Autoplay", variable=self.autoplay_var).pack(side="left")
        ttk.Label(preview_controls, textvariable=self.preview_info_var).pack(side="right")

        settings_wrap = ttk.Frame(parent)
        settings_wrap.pack(fill="x", pady=(10, 0))

        export_card = ttk.LabelFrame(settings_wrap, text="Export Settings", padding=8)
        export_card.pack(fill="x")

        row1 = ttk.Frame(export_card)
        row1.pack(fill="x", pady=(0, 6))

        ttk.Label(row1, text="Frame Duration (ms):").pack(side="left")
        ttk.Spinbox(row1, from_=20, to=5000, increment=10, textvariable=self.duration_ms_var, width=8).pack(side="left", padx=(6, 18))

        ttk.Checkbutton(row1, text="Loop Forever", variable=self.loop_forever_var, command=self._update_ui_state).pack(side="left")
        ttk.Label(row1, text="Loop Count:").pack(side="left", padx=(18, 6))
        self.loop_count_spin = ttk.Spinbox(row1, from_=0, to=999, increment=1, textvariable=self.loop_count_var, width=6)
        self.loop_count_spin.pack(side="left")

        row2 = ttk.Frame(export_card)
        row2.pack(fill="x", pady=(0, 6))

        ttk.Label(row2, text="Resize Mode:").pack(side="left")
        resize_menu = ttk.OptionMenu(
            row2,
            self.resize_mode_var,
            self.resize_mode_var.get(),
            "original",
            "fit_within",
            "stretch",
            command=lambda *_: self._on_resize_mode_changed()
        )
        resize_menu.pack(side="left", padx=(6, 18))

        ttk.Label(row2, text="Size Preset:").pack(side="left")
        self.export_size_preset_combo = ttk.Combobox(
            row2,
            textvariable=self.export_size_preset_var,
            values=list(EXPORT_SIZE_PRESETS.keys()),
            state="readonly",
            width=12,
        )
        self.export_size_preset_combo.pack(side="left", padx=(6, 18))
        self.export_size_preset_combo.bind("<<ComboboxSelected>>", self._on_export_size_preset_changed)

        ttk.Label(row2, text="Width:").pack(side="left")
        self.width_spin = ttk.Spinbox(row2, from_=0, to=8000, increment=1, textvariable=self.export_width_var, width=8)
        self.width_spin.pack(side="left", padx=(6, 18))

        ttk.Label(row2, text="Height:").pack(side="left")
        self.height_spin = ttk.Spinbox(row2, from_=0, to=8000, increment=1, textvariable=self.export_height_var, width=8)
        self.height_spin.pack(side="left", padx=(6, 18))

        ttk.Label(row2, text="Padding BG:").pack(side="left")
        ttk.Entry(row2, textvariable=self.bg_hex_var, width=10).pack(side="left", padx=(6, 0))

        effects_card = ttk.LabelFrame(parent, text="Optional Effects (only used if enabled)", padding=8)
        effects_card.pack(fill="x", pady=(10, 0))

        top_fx = ttk.Frame(effects_card)
        top_fx.pack(fill="x", pady=(0, 6))
        ttk.Checkbutton(top_fx, text="Enable Effects", variable=self.enable_effects_var, command=self._on_effect_option_toggled).pack(side="left")
        self.reverse_order_check = ttk.Checkbutton(top_fx, text="Reverse Order", variable=self.reverse_order_var, command=self._on_effect_option_toggled)
        self.reverse_order_check.pack(side="left", padx=(14, 0))
        self.pingpong_check = ttk.Checkbutton(top_fx, text="Ping-Pong", variable=self.pingpong_var, command=self._on_effect_option_toggled)
        self.pingpong_check.pack(side="left", padx=(14, 0))
        self.grayscale_check = ttk.Checkbutton(top_fx, text="Grayscale", variable=self.grayscale_var, command=self._on_effect_option_toggled)
        self.grayscale_check.pack(side="left", padx=(14, 0))

        row_fx_2 = ttk.Frame(effects_card)
        row_fx_2.pack(fill="x", pady=(0, 6))
        self.flip_h_check = ttk.Checkbutton(row_fx_2, text="Flip Horizontal", variable=self.flip_h_var, command=self._on_effect_option_toggled)
        self.flip_h_check.pack(side="left")
        self.flip_v_check = ttk.Checkbutton(row_fx_2, text="Flip Vertical", variable=self.flip_v_var, command=self._on_effect_option_toggled)
        self.flip_v_check.pack(side="left", padx=(14, 0))

        row_fx_3 = ttk.Frame(effects_card)
        row_fx_3.pack(fill="x", pady=(0, 6))
        self.brightness_check = ttk.Checkbutton(row_fx_3, text="Brightness", variable=self.enable_brightness_var, command=self._on_effect_option_toggled)
        self.brightness_check.pack(side="left")
        self.brightness_scale = ttk.Scale(
            row_fx_3,
            from_=0.2,
            to=3.0,
            variable=self.brightness_var,
            orient="horizontal",
            command=self._on_brightness_slider
        )
        self.brightness_scale.pack(side="left", fill="x", expand=True, padx=(8, 14))
        self.brightness_scale.bind("<ButtonRelease-1>", lambda e: self.schedule_preview_refresh(delay_ms=10))
        self.brightness_value_label = ttk.Label(row_fx_3, textvariable=self.brightness_text_var, width=5, anchor="e")
        self.brightness_value_label.pack(side="left")

        row_fx_4 = ttk.Frame(effects_card)
        row_fx_4.pack(fill="x", pady=(0, 6))
        self.contrast_check = ttk.Checkbutton(row_fx_4, text="Contrast", variable=self.enable_contrast_var, command=self._on_effect_option_toggled)
        self.contrast_check.pack(side="left")
        self.contrast_scale = ttk.Scale(
            row_fx_4,
            from_=0.2,
            to=3.0,
            variable=self.contrast_var,
            orient="horizontal",
            command=self._on_contrast_slider
        )
        self.contrast_scale.pack(side="left", fill="x", expand=True, padx=(18, 14))
        self.contrast_scale.bind("<ButtonRelease-1>", lambda e: self.schedule_preview_refresh(delay_ms=10))
        self.contrast_value_label = ttk.Label(row_fx_4, textvariable=self.contrast_text_var, width=5, anchor="e")
        self.contrast_value_label.pack(side="left")

        row_fx_5 = ttk.Frame(effects_card)
        row_fx_5.pack(fill="x", pady=(0, 6))
        self.sharpness_check = ttk.Checkbutton(row_fx_5, text="Sharpness", variable=self.enable_sharpness_var, command=self._on_effect_option_toggled)
        self.sharpness_check.pack(side="left")
        self.sharpness_scale = ttk.Scale(
            row_fx_5,
            from_=0.0,
            to=5.0,
            variable=self.sharpness_var,
            orient="horizontal",
            command=self._on_sharpness_slider
        )
        self.sharpness_scale.pack(side="left", fill="x", expand=True, padx=(12, 14))
        self.sharpness_scale.bind("<ButtonRelease-1>", lambda e: self.schedule_preview_refresh(delay_ms=10))
        self.sharpness_value_label = ttk.Label(row_fx_5, textvariable=self.sharpness_text_var, width=5, anchor="e")
        self.sharpness_value_label.pack(side="left")

        row_fx_6 = ttk.Frame(effects_card)
        row_fx_6.pack(fill="x")
        self.rotate_check = ttk.Checkbutton(row_fx_6, text="Rotate", variable=self.enable_rotate_var, command=self._on_effect_option_toggled)
        self.rotate_check.pack(side="left")
        self.rotate_spin = ttk.Spinbox(row_fx_6, from_=-360, to=360, increment=1, textvariable=self.rotate_var, width=8)
        self.rotate_spin.pack(side="left", padx=(8, 0))
        ttk.Label(row_fx_6, text="degrees").pack(side="left", padx=(6, 0))

        self.effect_control_widgets = [
            self.reverse_order_check,
            self.pingpong_check,
            self.grayscale_check,
            self.flip_h_check,
            self.flip_v_check,
            self.brightness_check,
            self.contrast_check,
            self.sharpness_check,
            self.rotate_check,
        ]

        project_row = ttk.Frame(parent)
        project_row.pack(fill="x", pady=(10, 0))
        ttk.Button(project_row, text="Open GBS", command=self.open_project).pack(side="left", padx=(0, 6))
        ttk.Button(project_row, text="Save GBS", command=self.save_project).pack(side="left")
        ttk.Button(project_row, text="New", command=self.new_project).pack(side="left", padx=(6, 0))

        action_row = ttk.Frame(parent)
        action_row.pack(fill="x", pady=(8, 0))
        ttk.Button(action_row, text="Export GIF", command=self.export_gif).pack(side="left", padx=(0, 6))
        ttk.Button(action_row, text="Export PNG Frames", command=self.export_png_frames).pack(side="left")

    def _bind_shortcuts(self) -> None:
        self.root.bind("<Delete>", lambda e: self.remove_selected())
        self.root.bind("<Control-o>", lambda e: self.add_images())
        self.root.bind("<Control-s>", lambda e: self.save_project())
        self.root.bind("<Control-e>", lambda e: self.export_gif())

    def _on_effect_option_toggled(self) -> None:
        self._update_ui_state()
        self.schedule_preview_refresh(delay_ms=10)

    def _suggest_export_size(self) -> Tuple[int, int]:
        if self.frames:
            try:
                with Image.open(self.frames[0].path) as img:
                    if getattr(img, "is_animated", False):
                        img.seek(0)
                    return (max(1, int(img.width)), max(1, int(img.height)))
            except Exception:
                pass
        return (320, 240)

    def _sync_export_size_preset(self) -> None:
        mode = self.resize_mode_var.get()
        if mode == "original":
            if self.export_size_preset_var.get() != "original":
                self.export_size_preset_var.set("original")
            return

        width = max(0, int(self.export_width_var.get()))
        height = max(0, int(self.export_height_var.get()))
        for preset_name, size in EXPORT_SIZE_PRESETS.items():
            if preset_name in {"original", "custom"} or size is None:
                continue
            if size == (width, height):
                if self.export_size_preset_var.get() != preset_name:
                    self.export_size_preset_var.set(preset_name)
                return

        if self.export_size_preset_var.get() != "custom":
            self.export_size_preset_var.set("custom")

    def _apply_export_size_preset(self, preset_name: str) -> None:
        preset_size = EXPORT_SIZE_PRESETS.get(preset_name)
        if preset_name == "original":
            self.resize_mode_var.set("original")
        elif preset_name == "custom":
            if self.resize_mode_var.get() == "original":
                self.resize_mode_var.set("fit_within")
            if int(self.export_width_var.get()) <= 0 or int(self.export_height_var.get()) <= 0:
                width, height = self._suggest_export_size()
                self.export_width_var.set(width)
                self.export_height_var.set(height)
        elif preset_size is not None:
            if self.resize_mode_var.get() == "original":
                self.resize_mode_var.set("fit_within")
            self.export_width_var.set(preset_size[0])
            self.export_height_var.set(preset_size[1])
        self._update_ui_state()

    def _on_export_size_preset_changed(self, _event=None) -> None:
        self._apply_export_size_preset(self.export_size_preset_var.get())

    def _on_resize_mode_changed(self) -> None:
        if self.resize_mode_var.get() != "original" and self.export_size_preset_var.get() == "original":
            self.export_size_preset_var.set("custom")
            if int(self.export_width_var.get()) <= 0 or int(self.export_height_var.get()) <= 0:
                width, height = self._suggest_export_size()
                self.export_width_var.set(width)
                self.export_height_var.set(height)
        self._sync_export_size_preset()
        self._update_ui_state()

    def _update_ui_state(self) -> None:
        loop_forever = self.loop_forever_var.get()
        self.loop_count_spin.state(["disabled"] if loop_forever else ["!disabled"])

        resize_mode = self.resize_mode_var.get()
        preset_name = self.export_size_preset_var.get()
        enable_size = resize_mode in {"fit_within", "stretch"} and preset_name == "custom"
        if enable_size:
            self.width_spin.state(["!disabled"])
            self.height_spin.state(["!disabled"])
        else:
            self.width_spin.state(["disabled"])
            self.height_spin.state(["disabled"])

        effects_enabled = self.enable_effects_var.get()
        for widget in self.effect_control_widgets:
            widget.state(["!disabled"] if effects_enabled else ["disabled"])

        self.brightness_scale.state(["!disabled"] if effects_enabled and self.enable_brightness_var.get() else ["disabled"])
        self.contrast_scale.state(["!disabled"] if effects_enabled and self.enable_contrast_var.get() else ["disabled"])
        self.sharpness_scale.state(["!disabled"] if effects_enabled and self.enable_sharpness_var.get() else ["disabled"])
        self.rotate_spin.state(["!disabled"] if effects_enabled and self.enable_rotate_var.get() else ["disabled"])

    def _register_preview_traces(self) -> None:
        preview_vars = [
            self.duration_ms_var,
            self.resize_mode_var,
            self.export_size_preset_var,
            self.export_width_var,
            self.export_height_var,
            self.bg_hex_var,
            self.autoplay_var,
            self.enable_effects_var,
            self.reverse_order_var,
            self.pingpong_var,
            self.grayscale_var,
            self.flip_h_var,
            self.flip_v_var,
            self.enable_brightness_var,
            self.enable_contrast_var,
            self.enable_sharpness_var,
            self.enable_rotate_var,
            self.rotate_var,
        ]
        for var in preview_vars:
            var.trace_add("write", self._schedule_preview_refresh_from_trace)

        self.brightness_var.trace_add("write", self._update_slider_labels_from_trace)
        self.contrast_var.trace_add("write", self._update_slider_labels_from_trace)
        self.sharpness_var.trace_add("write", self._update_slider_labels_from_trace)
        self.export_width_var.trace_add("write", self._sync_export_size_preset_from_trace)
        self.export_height_var.trace_add("write", self._sync_export_size_preset_from_trace)
        self.resize_mode_var.trace_add("write", self._sync_export_size_preset_from_trace)
        self._sync_slider_labels()
        self.video_start_var.trace_add("write", lambda *_args: self._sync_video_clip_info())
        self.video_end_var.trace_add("write", lambda *_args: self._sync_video_clip_info())
        self._sync_export_size_preset()
        self._sync_video_clip_info()

    def _schedule_preview_refresh_from_trace(self, *_args) -> None:
        self.schedule_preview_refresh()

    def _update_slider_labels_from_trace(self, *_args) -> None:
        self._sync_slider_labels()

    def _sync_export_size_preset_from_trace(self, *_args) -> None:
        self._sync_export_size_preset()

    def _sync_slider_labels(self) -> None:
        self.brightness_text_var.set(f"{float(self.brightness_var.get()):.2f}")
        self.contrast_text_var.set(f"{float(self.contrast_var.get()):.2f}")
        self.sharpness_text_var.set(f"{float(self.sharpness_var.get()):.2f}")

    def _on_brightness_slider(self, value: str) -> None:
        self.brightness_text_var.set(f"{float(value):.2f}")
        self.schedule_preview_refresh(delay_ms=SLIDER_PREVIEW_REFRESH_DELAY_MS)

    def _on_contrast_slider(self, value: str) -> None:
        self.contrast_text_var.set(f"{float(value):.2f}")
        self.schedule_preview_refresh(delay_ms=SLIDER_PREVIEW_REFRESH_DELAY_MS)

    def _on_sharpness_slider(self, value: str) -> None:
        self.sharpness_text_var.set(f"{float(value):.2f}")
        self.schedule_preview_refresh(delay_ms=SLIDER_PREVIEW_REFRESH_DELAY_MS)

    def schedule_preview_refresh(self, delay_ms: int = PREVIEW_REFRESH_DELAY_MS) -> None:
        if self.preview_refresh_after_id is not None:
            try:
                self.root.after_cancel(self.preview_refresh_after_id)
            except Exception:
                pass
        self.preview_refresh_after_id = self.root.after(delay_ms, self.refresh_preview)

    def _invalidate_preview_requests(self) -> None:
        self.preview_request_id += 1
        with self.preview_job_lock:
            self.pending_preview_job = None
            self.preview_job_event.clear()
        self.current_preview_signature = None

    def _queue_preview_render(self, *, force_play: bool = False) -> None:
        if self.preview_refresh_after_id is not None:
            try:
                self.root.after_cancel(self.preview_refresh_after_id)
            except Exception:
                pass
            self.preview_refresh_after_id = None

        if not self.frames:
            self._invalidate_preview_requests()
            self.stop_preview()
            self._clear_preview("Preview: no frames loaded")
            return

        settings = self._capture_render_settings()
        preview_size = self._get_preview_target_size()
        signature = (len(settings.frame_paths), settings, preview_size)
        if not force_play and signature == self.current_preview_signature and self.preview_frames:
            return

        self.preview_request_id += 1
        request_id = self.preview_request_id
        had_preview_frames = bool(self.preview_frames)
        self.current_preview_signature = signature
        self.preview_info_var.set(f"Preview: rendering {len(settings.frame_paths)} frame(s)...")

        job = PreviewRenderJob(
            request_id=request_id,
            settings=settings,
            preview_size=preview_size,
            autoplay_if_new=self.autoplay_var.get() and not had_preview_frames,
            force_play=force_play,
        )
        with self.preview_job_lock:
            self.pending_preview_job = job
            self.preview_job_event.set()

    def _preview_worker_loop(self) -> None:
        while not self.preview_stop_event.is_set():
            self.preview_job_event.wait(timeout=0.1)
            if self.preview_stop_event.is_set():
                return
            if not self.preview_job_event.is_set():
                continue

            with self.preview_job_lock:
                job = self.pending_preview_job
                self.pending_preview_job = None
                if self.pending_preview_job is None:
                    self.preview_job_event.clear()

            if job is None:
                continue

            try:
                rendered = self._build_preview_images(job.settings, job.preview_size)
                self.preview_result_queue.put((job.request_id, rendered, None, job.autoplay_if_new, job.force_play, job.settings.duration_ms))
            except Exception as exc:
                self.preview_result_queue.put((job.request_id, None, str(exc), job.autoplay_if_new, job.force_play, job.settings.duration_ms))

    def _poll_preview_results(self) -> None:
        latest = None
        while True:
            try:
                latest = self.preview_result_queue.get_nowait()
            except queue.Empty:
                break

            request_id, frames, error, autoplay_if_new, force_play, duration_ms = latest
            if request_id != self.preview_request_id:
                continue
            self._apply_preview_result(request_id, frames, error, autoplay_if_new, force_play, duration_ms)

        if not self.preview_stop_event.is_set():
            self.preview_result_after_id = self.root.after(40, self._poll_preview_results)

    def _apply_preview_result(
        self,
        request_id: int,
        frames: Optional[List[Image.Image]],
        error: Optional[str],
        autoplay_if_new: bool,
        force_play: bool,
        duration_ms: int,
    ) -> None:
        if request_id != self.preview_request_id:
            return

        if error is not None:
            if not self.preview_frames:
                self._clear_preview(f"Preview error: {error}")
            self.preview_info_var.set(f"Preview error: {error}")
            self.status_var.set(f"Preview error: {error}")
            return

        preview_frames: List[ImageTk.PhotoImage] = []
        for img in frames or []:
            preview_frames.append(ImageTk.PhotoImage(img))

        should_play = force_play or self.preview_playing or autoplay_if_new
        self.stop_preview()
        self.preview_frames = preview_frames
        self.preview_index = 0
        self.preview_info_var.set(f"Preview: {len(self.preview_frames)} frame(s) at {duration_ms} ms")

        if self.preview_frames:
            self.preview_label.configure(image=self.preview_frames[0], text="")
            self.preview_label.image = self.preview_frames[0]
        else:
            self._clear_preview("Preview: no frames loaded")
            return

        if should_play:
            self.start_preview()

    def _clear_preview(self, info_text: str) -> None:
        self.preview_frames = []
        self.preview_label.configure(image="", text="")
        self.preview_label.image = None
        self.preview_info_var.set(info_text)

    def _on_close(self) -> None:
        self._close_timestamp_picker()
        self._close_busy_dialog()
        self.preview_stop_event.set()
        self.preview_job_event.set()
        if self.preview_refresh_after_id is not None:
            try:
                self.root.after_cancel(self.preview_refresh_after_id)
            except Exception:
                pass
            self.preview_refresh_after_id = None
        if self.preview_result_after_id is not None:
            try:
                self.root.after_cancel(self.preview_result_after_id)
            except Exception:
                pass
            self.preview_result_after_id = None
        self.stop_preview()
        shutil.rmtree(self.session_tempdir, ignore_errors=True)
        self.root.destroy()

    def _prune_image_cache(self) -> None:
        active_paths = {item.path for item in self.frames}
        with self.image_cache_lock:
            stale_paths = [path for path in self.image_cache if path not in active_paths]
            for path in stale_paths:
                del self.image_cache[path]

    def _default_video_info_text(self) -> str:
        if cv2 is None:
            return "Install OpenCV to import video clips. Example: pip install opencv-python"
        return "Choose a video, then set start, end, and sample FPS."

    def _format_seconds(self, seconds: float) -> str:
        seconds = max(0.0, float(seconds))
        minutes = int(seconds // 60)
        remainder = seconds - (minutes * 60)
        return f"{minutes:02d}:{remainder:05.2f}"

    def _frame_label(self, item: FrameItem) -> str:
        return item.display_name or os.path.basename(item.path)

    def _sanitize_project_member_name(self, name: str, fallback: str) -> str:
        candidate = os.path.basename(name).strip() or fallback
        invalid_chars = '<>:"/\\|?*'
        cleaned = "".join("_" if ch in invalid_chars or ord(ch) < 32 else ch for ch in candidate)
        return cleaned or fallback

    def _has_loaded_content(self) -> bool:
        return bool(self.frames or self.loaded_video_path or self.current_project_path)

    def _confirm_replace_editor(self, incoming_label: str) -> bool:
        if not self._has_loaded_content():
            return True
        return messagebox.askyesno(
            "Start Fresh",
            f"Loading a new {incoming_label} will clear the current editor and reset the controls.\n\nContinue?"
        )

    def _reset_session_tempdir(self) -> None:
        shutil.rmtree(self.session_tempdir, ignore_errors=True)
        self.session_tempdir = tempfile.mkdtemp(prefix="gif_builder_studio_")

    def _clear_loaded_frames(self, *, reset_temp_assets: bool = False) -> None:
        if self.preview_refresh_after_id is not None:
            try:
                self.root.after_cancel(self.preview_refresh_after_id)
            except Exception:
                pass
            self.preview_refresh_after_id = None

        self.stop_preview()
        self._invalidate_preview_requests()
        self.frames.clear()
        self.listbox.delete(0, "end")
        with self.image_cache_lock:
            self.image_cache.clear()
        if reset_temp_assets:
            self._reset_session_tempdir()
        self._clear_preview("Preview: no frames loaded")

    def _clear_loaded_video(self) -> None:
        self._close_timestamp_picker()
        self.loaded_video_path = None
        self.loaded_video_info = None
        self.video_path_var.set("No video selected")
        self.video_info_var.set(self._default_video_info_text())
        self.video_start_var.set(0.0)
        self.video_end_var.set(2.0)
        self.video_sample_fps_var.set(10.0)
        self.video_picker_time_var.set(0.0)
        self.video_picker_info_var.set("Choose a video to preview timestamps.")
        self._sync_video_clip_info()

    def _apply_default_editor_settings(self) -> None:
        self.duration_ms_var.set(120)
        self.loop_forever_var.set(True)
        self.loop_count_var.set(0)
        self.resize_mode_var.set("original")
        self.export_size_preset_var.set("original")
        self.export_width_var.set(0)
        self.export_height_var.set(0)
        self.bg_hex_var.set("#000000")
        self.autoplay_var.set(True)

        self.enable_effects_var.set(False)
        self.reverse_order_var.set(False)
        self.pingpong_var.set(False)
        self.grayscale_var.set(False)
        self.flip_h_var.set(False)
        self.flip_v_var.set(False)

        self.enable_brightness_var.set(False)
        self.brightness_var.set(1.0)
        self.enable_contrast_var.set(False)
        self.contrast_var.set(1.0)
        self.enable_sharpness_var.set(False)
        self.sharpness_var.set(1.0)
        self.enable_rotate_var.set(False)
        self.rotate_var.set(0)
        self.last_export_path = None
        self._sync_slider_labels()
        self._update_ui_state()

    def _reset_editor_fresh(self) -> None:
        self._clear_loaded_video()
        self._clear_loaded_frames(reset_temp_assets=True)
        self._apply_default_editor_settings()
        self.current_project_path = None
        self.status_var.set("Editor reset. Load images, video, or a .GBS project.")

    def _format_video_info_text(self, info: Dict[str, float | int | str]) -> str:
        duration = float(info.get("duration", 0.0) or 0.0)
        source_fps = float(info.get("fps", 0.0) or 0.0)
        width = int(info.get("width", 0) or 0)
        height = int(info.get("height", 0) or 0)
        backend = str(info.get("backend", "unknown"))
        frame_count = int(info.get("frame_count", 0) or 0)
        duration_text = f"{duration:.2f}s" if duration > 0 else "unknown duration"
        fps_text = f"{source_fps:.2f} fps" if source_fps > 0 else "unknown fps"
        frame_text = f"{frame_count} frames" if frame_count > 0 else "frame count unknown"
        return f"{width}x{height} | {duration_text} | {fps_text} | {frame_text} | backend: {backend}"

    def _set_loaded_video_source(self, path: str, info: Dict[str, float | int | str]) -> None:
        self.loaded_video_path = path
        self.loaded_video_info = info
        self.video_path_var.set(os.path.basename(path))
        self.video_info_var.set(self._format_video_info_text(info))

    def _set_editor_frames(self, items: List[FrameItem], status_text: str) -> None:
        self.frames = list(items)
        self._rebuild_listbox(indices=list(range(len(self.frames))) if self.frames else None)
        if self.frames:
            self.listbox.see(len(self.frames) - 1)
            self.refresh_preview()
        else:
            self._clear_preview("Preview: no frames loaded")
        self.status_var.set(status_text)

    def _collect_project_settings(self) -> Dict[str, Any]:
        return {
            "duration_ms": int(self.duration_ms_var.get()),
            "loop_forever": bool(self.loop_forever_var.get()),
            "loop_count": int(self.loop_count_var.get()),
            "resize_mode": str(self.resize_mode_var.get()),
            "export_size_preset": str(self.export_size_preset_var.get()),
            "export_width": int(self.export_width_var.get()),
            "export_height": int(self.export_height_var.get()),
            "bg_hex": str(self.bg_hex_var.get()),
            "autoplay": bool(self.autoplay_var.get()),
            "enable_effects": bool(self.enable_effects_var.get()),
            "reverse_order": bool(self.reverse_order_var.get()),
            "pingpong": bool(self.pingpong_var.get()),
            "grayscale": bool(self.grayscale_var.get()),
            "flip_h": bool(self.flip_h_var.get()),
            "flip_v": bool(self.flip_v_var.get()),
            "enable_brightness": bool(self.enable_brightness_var.get()),
            "brightness": float(self.brightness_var.get()),
            "enable_contrast": bool(self.enable_contrast_var.get()),
            "contrast": float(self.contrast_var.get()),
            "enable_sharpness": bool(self.enable_sharpness_var.get()),
            "sharpness": float(self.sharpness_var.get()),
            "enable_rotate": bool(self.enable_rotate_var.get()),
            "rotate": int(self.rotate_var.get()),
        }

    def _apply_project_settings(self, settings: Dict[str, Any]) -> None:
        try:
            self.duration_ms_var.set(max(20, int(settings.get("duration_ms", 120))))
            self.loop_forever_var.set(bool(settings.get("loop_forever", True)))
            self.loop_count_var.set(max(0, int(settings.get("loop_count", 0))))
            self.resize_mode_var.set(str(settings.get("resize_mode", "original")))
            preset_name = str(settings.get("export_size_preset", "original"))
            if preset_name not in EXPORT_SIZE_PRESETS:
                preset_name = "original"
            self.export_size_preset_var.set(preset_name)
            self.export_width_var.set(max(0, int(settings.get("export_width", 0))))
            self.export_height_var.set(max(0, int(settings.get("export_height", 0))))
            self.bg_hex_var.set(str(settings.get("bg_hex", "#000000")))
            self.autoplay_var.set(bool(settings.get("autoplay", True)))

            self.enable_effects_var.set(bool(settings.get("enable_effects", False)))
            self.reverse_order_var.set(bool(settings.get("reverse_order", False)))
            self.pingpong_var.set(bool(settings.get("pingpong", False)))
            self.grayscale_var.set(bool(settings.get("grayscale", False)))
            self.flip_h_var.set(bool(settings.get("flip_h", False)))
            self.flip_v_var.set(bool(settings.get("flip_v", False)))

            self.enable_brightness_var.set(bool(settings.get("enable_brightness", False)))
            self.brightness_var.set(float(settings.get("brightness", 1.0)))
            self.enable_contrast_var.set(bool(settings.get("enable_contrast", False)))
            self.contrast_var.set(float(settings.get("contrast", 1.0)))
            self.enable_sharpness_var.set(bool(settings.get("enable_sharpness", False)))
            self.sharpness_var.set(float(settings.get("sharpness", 1.0)))
            self.enable_rotate_var.set(bool(settings.get("enable_rotate", False)))
            self.rotate_var.set(int(settings.get("rotate", 0)))
        except Exception as exc:
            raise ValueError(f"Project settings are invalid: {exc}") from exc

        self._sync_slider_labels()
        self._sync_export_size_preset()
        self._update_ui_state()

    def _collect_project_video_state(self) -> Dict[str, Any]:
        return {
            "source_path": self.loaded_video_path,
            "display_name": str(self.video_path_var.get()),
            "start_sec": float(self.video_start_var.get()),
            "end_sec": float(self.video_end_var.get()),
            "sample_fps": float(self.video_sample_fps_var.get()),
        }

    def _apply_project_video_state(self, video_state: Dict[str, Any]) -> None:
        start_sec = float(video_state.get("start_sec", 0.0) or 0.0)
        end_sec = float(video_state.get("end_sec", 2.0) or 2.0)
        sample_fps = float(video_state.get("sample_fps", 10.0) or 10.0)
        self.video_start_var.set(max(0.0, start_sec))
        self.video_end_var.set(max(self.video_start_var.get() + 0.1, end_sec))
        self.video_sample_fps_var.set(max(0.1, sample_fps))

        source_path = str(video_state.get("source_path") or "")
        display_name = str(video_state.get("display_name") or "")
        if source_path and os.path.exists(source_path) and cv2 is not None:
            try:
                info = self._read_video_info(source_path)
                self._set_loaded_video_source(source_path, info)
            except Exception:
                self.loaded_video_path = None
                self.loaded_video_info = None
                self.video_path_var.set(display_name or os.path.basename(source_path))
                self.video_info_var.set("Project loaded. Choose the original video again if you want live trim playback.")
        elif display_name and display_name != "No video selected":
            self.loaded_video_path = None
            self.loaded_video_info = None
            self.video_path_var.set(display_name)
            self.video_info_var.set("Project loaded. Choose the original video again if you want live trim playback.")
        else:
            self.loaded_video_path = None
            self.loaded_video_info = None
            self.video_path_var.set("No video selected")
            self.video_info_var.set(self._default_video_info_text())

        self._sync_video_clip_info()

    def _read_project_manifest(self, path: str) -> Dict[str, Any]:
        try:
            with zipfile.ZipFile(path, "r") as archive:
                try:
                    with archive.open("manifest.json", "r") as handle:
                        manifest = json.loads(handle.read().decode("utf-8"))
                except KeyError as exc:
                    raise ValueError("This .GBS file is missing manifest.json.") from exc
                except json.JSONDecodeError as exc:
                    raise ValueError("This .GBS file has an invalid manifest.") from exc

                if not isinstance(manifest, dict):
                    raise ValueError("This .GBS file has an invalid manifest format.")

                if str(manifest.get("format") or "") != "GIF Builder Studio Project":
                    raise ValueError("That file is not a GIF Builder Studio project.")

                version = int(manifest.get("version", 0) or 0)
                if version <= 0 or version > PROJECT_ARCHIVE_VERSION:
                    raise ValueError(f"Unsupported .GBS version: {version}")

                frames = manifest.get("frames", [])
                if not isinstance(frames, list):
                    raise ValueError("This .GBS file has an invalid frame list.")

                for entry in frames:
                    if not isinstance(entry, dict):
                        raise ValueError("This .GBS file has an invalid frame entry.")
                    archive_path = str(entry.get("archive_path") or "").replace("\\", "/")
                    if not archive_path or archive_path.startswith("/") or ".." in archive_path.split("/"):
                        raise ValueError("This .GBS file contains an unsafe frame path.")
                    try:
                        archive.getinfo(archive_path)
                    except KeyError as exc:
                        raise ValueError(f"Missing frame inside .GBS project: {archive_path}") from exc

                return manifest
        except zipfile.BadZipFile as exc:
            raise ValueError("That file is not a valid .GBS project archive.") from exc

    def _write_project_archive(self, path: str) -> None:
        manifest: Dict[str, Any] = {
            "format": "GIF Builder Studio Project",
            "version": PROJECT_ARCHIVE_VERSION,
            "app_title": APP_TITLE,
            "settings": self._collect_project_settings(),
            "video": self._collect_project_video_state(),
            "frames": [],
        }

        with zipfile.ZipFile(path, "w", compression=zipfile.ZIP_DEFLATED) as archive:
            frame_entries: List[Dict[str, Any]] = []
            for index, item in enumerate(self.frames):
                if not os.path.exists(item.path):
                    raise FileNotFoundError(f"Missing frame file: {item.path}")
                label = self._frame_label(item)
                source_ext = os.path.splitext(item.path)[1] or os.path.splitext(label)[1] or ".png"
                fallback_name = f"frame_{index:04d}{source_ext}"
                member_name = self._sanitize_project_member_name(label, fallback_name)
                archive_name = f"frames/{index:04d}/{member_name}"
                archive.write(item.path, archive_name)
                frame_entries.append({
                    "archive_path": archive_name,
                    "display_name": label,
                })

            manifest["frames"] = frame_entries
            archive.writestr("manifest.json", json.dumps(manifest, indent=2))

    def _load_project_archive(self, path: str, manifest: Optional[Dict[str, Any]] = None) -> None:
        project_manifest = manifest if manifest is not None else self._read_project_manifest(path)
        settings = project_manifest.get("settings", {})
        video_state = project_manifest.get("video", {})
        if not isinstance(settings, dict) or not isinstance(video_state, dict):
            raise ValueError("This .GBS file has invalid project data.")

        staging_dir = tempfile.mkdtemp(prefix="gbs_project_stage_")
        staged_items: List[Tuple[str, str]] = []
        try:
            with zipfile.ZipFile(path, "r") as archive:
                for entry in project_manifest.get("frames", []):
                    archive_name = str(entry.get("archive_path") or "").replace("\\", "/")
                    staged_path = os.path.join(staging_dir, *archive_name.split("/"))
                    os.makedirs(os.path.dirname(staged_path), exist_ok=True)
                    with archive.open(archive_name, "r") as source_handle, open(staged_path, "wb") as target_handle:
                        shutil.copyfileobj(source_handle, target_handle)
                    staged_items.append((staged_path, str(entry.get("display_name") or os.path.basename(staged_path))))

            self._reset_editor_fresh()
            extracted_items: List[FrameItem] = []
            project_dir = tempfile.mkdtemp(prefix="gbs_project_", dir=self.session_tempdir)
            for staged_path, display_name in staged_items:
                final_path = os.path.join(project_dir, os.path.basename(staged_path))
                shutil.move(staged_path, final_path)
                extracted_items.append(FrameItem(path=final_path, display_name=display_name))
        finally:
            shutil.rmtree(staging_dir, ignore_errors=True)

        self._apply_project_settings(settings)
        self._apply_project_video_state(video_state)
        self.current_project_path = path
        self._set_editor_frames(extracted_items, f"Opened project: {path}")

    def save_project(self) -> None:
        if not self.frames and not self.loaded_video_path:
            messagebox.showwarning(
                "Nothing To Save",
                "Load images, import a video clip, or choose a video before saving a .GBS project."
            )
            return

        out_path = self.current_project_path
        if not out_path:
            out_path = filedialog.asksaveasfilename(
                title="Save GIF Builder Studio Project",
                defaultextension=".gbs",
                filetypes=SUPPORTED_PROJECT_TYPES,
            )
        if not out_path:
            return

        try:
            self._write_project_archive(out_path)
        except Exception as exc:
            messagebox.showerror("Save Failed", str(exc))
            self.status_var.set(f"Project save failed: {exc}")
            return

        self.current_project_path = out_path
        self.status_var.set(f"Saved project: {out_path}")

    def open_project(self) -> None:
        path = filedialog.askopenfilename(
            title="Open GIF Builder Studio Project",
            filetypes=SUPPORTED_PROJECT_TYPES,
        )
        if not path:
            return

        try:
            manifest = self._read_project_manifest(path)
        except Exception as exc:
            messagebox.showerror("Open Failed", str(exc))
            return

        if not self._confirm_replace_editor("project"):
            return

        try:
            self._load_project_archive(path, manifest)
        except Exception as exc:
            messagebox.showerror("Open Failed", str(exc))
            self.status_var.set(f"Project open failed: {exc}")

    def new_project(self) -> None:
        if self._has_loaded_content() and not messagebox.askyesno(
            "New Project",
            "Start a fresh project and clear the current frames, video selection, and project state?"
        ):
            return
        self._reset_editor_fresh()
        self.status_var.set("Started a fresh project.")

    def _set_busy_progress_state(
        self,
        *,
        progress_value: Optional[int] = None,
        progress_total: Optional[int] = None,
        indeterminate: Optional[bool] = None,
    ) -> None:
        if self.busy_progressbar is None:
            return

        use_indeterminate = bool(indeterminate)
        if indeterminate is None:
            use_indeterminate = not (
                progress_value is not None and progress_total is not None and progress_total > 0
            )

        try:
            self.busy_progressbar.stop()
        except Exception:
            pass

        if use_indeterminate:
            self.busy_progressbar.configure(mode="indeterminate", maximum=100.0, value=0.0)
            self.busy_progressbar.start(10)
            self.busy_percent_var.set("Working...")
            return

        current = max(0, int(progress_value or 0))
        total = max(1, int(progress_total or 1))
        percent = max(0.0, min(100.0, (current / total) * 100.0))
        self.busy_progressbar.configure(mode="determinate", maximum=100.0, value=percent)
        self.busy_percent_var.set(f"{percent:.0f}%")

    def _show_busy_dialog(
        self,
        message: str,
        progress_text: str = "",
        *,
        progress_value: Optional[int] = None,
        progress_total: Optional[int] = None,
        indeterminate: Optional[bool] = None,
    ) -> None:
        if self.busy_dialog is not None:
            self.busy_label_var.set(message)
            self.busy_progress_var.set(progress_text)
            self._set_busy_progress_state(
                progress_value=progress_value,
                progress_total=progress_total,
                indeterminate=indeterminate,
            )
            try:
                self.busy_dialog.update()
            except Exception:
                self.root.update_idletasks()
            return

        dialog = tk.Toplevel(self.root)
        self._apply_window_icon(dialog)
        dialog.title("Working...")
        dialog.geometry("340x220")
        dialog.minsize(340, 220)
        dialog.maxsize(460, 260)
        dialog.resizable(False, False)
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.lift()

        body = ttk.Frame(dialog, padding=16)
        body.pack(fill="both", expand=True)

        spinner = tk.Canvas(body, width=52, height=52, highlightthickness=0, bd=0)
        spinner.pack(pady=(0, 12))
        self.busy_spinner_canvas = spinner
        self.busy_spinner_arc = spinner.create_arc(
            6, 6, 46, 46,
            start=self.busy_spinner_angle,
            extent=280,
            style="arc",
            width=5,
            outline="#2f7de1",
        )
        spinner.create_text(26, 26, text="...", fill="#2f7de1", font=("Segoe UI", 10, "bold"))

        ttk.Label(body, textvariable=self.busy_label_var, anchor="center", justify="center", wraplength=280).pack(fill="x")
        progressbar = ttk.Progressbar(body, mode="determinate", length=220, maximum=100.0, value=0.0)
        progressbar.pack(fill="x", pady=(10, 0))
        self.busy_progressbar = progressbar
        ttk.Label(
            body,
            textvariable=self.busy_percent_var,
            anchor="center",
            justify="center",
            font=("Segoe UI", 12, "bold"),
        ).pack(fill="x", pady=(8, 0))
        ttk.Label(body, textvariable=self.busy_progress_var, anchor="center", justify="center", wraplength=280).pack(fill="x", pady=(8, 0))

        dialog.protocol("WM_DELETE_WINDOW", lambda: None)
        self.busy_dialog = dialog
        self.busy_label_var.set(message)
        self.busy_progress_var.set(progress_text)
        self._set_busy_progress_state(
            progress_value=progress_value,
            progress_total=progress_total,
            indeterminate=indeterminate,
        )
        self._animate_busy_dialog()
        try:
            dialog.update()
        except Exception:
            self.root.update_idletasks()

    def _animate_busy_dialog(self) -> None:
        if self.busy_dialog is None or self.busy_spinner_canvas is None or self.busy_spinner_arc is None:
            return

        self.busy_spinner_angle = (self.busy_spinner_angle + 18) % 360
        self.busy_spinner_canvas.itemconfigure(self.busy_spinner_arc, start=self.busy_spinner_angle)
        self.busy_dialog_after_id = self.root.after(60, self._animate_busy_dialog)

    def _update_busy_dialog(
        self,
        message: Optional[str] = None,
        progress_text: Optional[str] = None,
        *,
        progress_value: Optional[int] = None,
        progress_total: Optional[int] = None,
        indeterminate: Optional[bool] = None,
    ) -> None:
        if self.busy_dialog is None:
            return
        if message is not None:
            self.busy_label_var.set(message)
        if progress_text is not None:
            self.busy_progress_var.set(progress_text)
        self._set_busy_progress_state(
            progress_value=progress_value,
            progress_total=progress_total,
            indeterminate=indeterminate,
        )
        try:
            self.busy_dialog.update()
        except Exception:
            self.root.update_idletasks()

    def _close_busy_dialog(self) -> None:
        if self.busy_dialog_after_id is not None:
            try:
                self.root.after_cancel(self.busy_dialog_after_id)
            except Exception:
                pass
            self.busy_dialog_after_id = None

        if self.busy_dialog is not None:
            try:
                self.busy_dialog.grab_release()
            except Exception:
                pass
            try:
                self.busy_dialog.destroy()
            except Exception:
                pass
            self.busy_dialog = None

        if self.busy_progressbar is not None:
            try:
                self.busy_progressbar.stop()
            except Exception:
                pass
            self.busy_progressbar = None

        self.busy_spinner_canvas = None
        self.busy_spinner_arc = None

    def _sync_video_clip_info(self) -> None:
        try:
            start = max(0.0, float(self.video_start_var.get()))
        except Exception:
            start = 0.0
        try:
            end = max(0.0, float(self.video_end_var.get()))
        except Exception:
            end = start
        length = max(0.0, end - start)
        self.video_clip_info_var.set(
            f"Clip: start {self._format_seconds(start)} | end {self._format_seconds(end)} | length {length:.2f}s"
        )

    def _require_video_support(self) -> bool:
        if cv2 is not None:
            return True

        detail = f"\n\nImport error: {CV2_IMPORT_ERROR}" if CV2_IMPORT_ERROR is not None else ""
        messagebox.showerror(
            "OpenCV Required",
            "Video import needs OpenCV.\n\nInstall it with:\n\n    pip install opencv-python"
            f"{detail}"
        )
        return False

    def _open_video_capture(self, path: str):
        if cv2 is None:
            raise RuntimeError("OpenCV is not installed.")

        attempted_backends: List[Tuple[int, str]] = []
        if sys.platform.startswith("win") and hasattr(cv2, "CAP_MSMF"):
            attempted_backends.append((cv2.CAP_MSMF, "MSMF"))
        attempted_backends.append((cv2.CAP_ANY, "Auto"))

        last_error = "Could not open the video file."
        for backend, backend_name in attempted_backends:
            capture = cv2.VideoCapture(path, backend)
            if capture.isOpened():
                return capture
            capture.release()
            last_error = f"Could not open the video with backend: {backend_name}."

        raise ValueError(last_error)

    def _video_backend_name(self, capture) -> str:
        try:
            return str(capture.getBackendName())
        except Exception:
            return "unknown"

    def _close_timestamp_picker(self) -> None:
        self._pause_video_picker_playback()
        if self.video_picker_after_id is not None:
            try:
                self.root.after_cancel(self.video_picker_after_id)
            except Exception:
                pass
            self.video_picker_after_id = None

        if self.video_picker_capture is not None:
            try:
                self.video_picker_capture.release()
            except Exception:
                pass
            self.video_picker_capture = None

        if self.video_picker_window is not None:
            try:
                self.video_picker_window.destroy()
            except Exception:
                pass
            self.video_picker_window = None

        self.video_picker_play_button = None
        self.video_picker_pause_button = None
        self.video_picker_preview_photo = None

    def _schedule_timestamp_preview_update(self, _value: Optional[str] = None) -> None:
        if self.video_picker_after_id is not None:
            try:
                self.root.after_cancel(self.video_picker_after_id)
            except Exception:
                pass
        self.video_picker_after_id = self.root.after(80, self._update_timestamp_preview)

    def _update_video_picker_play_buttons(self) -> None:
        if self.video_picker_play_button is not None:
            self.video_picker_play_button.state(["disabled"] if self.video_picker_playing else ["!disabled"])
        if self.video_picker_pause_button is not None:
            self.video_picker_pause_button.state(["!disabled"] if self.video_picker_playing else ["disabled"])

    def _start_video_picker_playback(self) -> None:
        if self.video_picker_window is None or self.video_picker_capture is None:
            return
        if self.video_picker_playing:
            return
        self.video_picker_playing = True
        self._update_video_picker_play_buttons()
        self._tick_video_picker_playback()

    def _pause_video_picker_playback(self) -> None:
        self.video_picker_playing = False
        if self.video_picker_play_after_id is not None:
            try:
                self.root.after_cancel(self.video_picker_play_after_id)
            except Exception:
                pass
            self.video_picker_play_after_id = None
        self._update_video_picker_play_buttons()

    def _on_video_picker_scrub(self, _value: Optional[str] = None) -> None:
        self._pause_video_picker_playback()
        self._schedule_timestamp_preview_update()

    def _read_frame_from_capture(self, capture, timestamp_sec: float):
        timestamp_sec = max(0.0, float(timestamp_sec))
        capture.set(cv2.CAP_PROP_POS_MSEC, timestamp_sec * 1000.0)
        ok, frame = capture.read()
        if ok and frame is not None:
            return frame

        source_fps = 0.0
        try:
            source_fps = float(capture.get(cv2.CAP_PROP_FPS) or 0.0)
        except Exception:
            source_fps = 0.0

        if source_fps > 0:
            capture.set(cv2.CAP_PROP_POS_FRAMES, int(round(timestamp_sec * source_fps)))
            ok, frame = capture.read()
            if ok and frame is not None:
                return frame

        raise ValueError("Could not read a frame at that timestamp.")

    def _render_timestamp_preview(self, timestamp: float) -> None:
        if self.video_picker_window is None or self.video_picker_capture is None:
            return

        try:
            timestamp = max(0.0, float(timestamp))
            frame = self._read_frame_from_capture(self.video_picker_capture, timestamp)
            rgba = cv2.cvtColor(frame, cv2.COLOR_BGR2RGBA)
            image = Image.fromarray(rgba, "RGBA")
            image.thumbnail((540, 320), Image.Resampling.LANCZOS)
            self.video_picker_preview_photo = ImageTk.PhotoImage(image)
            self.video_picker_preview_label.configure(image=self.video_picker_preview_photo, text="")
            self.video_picker_preview_label.image = self.video_picker_preview_photo
            prefix = "Playing | " if self.video_picker_playing else ""
            self.video_picker_info_var.set(f"{prefix}Timestamp: {self._format_seconds(timestamp)}")
        except Exception as exc:
            self.video_picker_preview_label.configure(image="", text="")
            self.video_picker_preview_label.image = None
            self.video_picker_info_var.set(f"Preview error: {exc}")

    def _update_timestamp_preview(self) -> None:
        self.video_picker_after_id = None
        if self.video_picker_window is None:
            return
        timestamp = max(0.0, float(self.video_picker_time_var.get()))
        self._render_timestamp_preview(timestamp)

    def _tick_video_picker_playback(self) -> None:
        self.video_picker_play_after_id = None
        if not self.video_picker_playing or self.video_picker_window is None or self.video_picker_capture is None:
            return

        current_time = max(0.0, float(self.video_picker_time_var.get()))
        duration = float(self.loaded_video_info.get("duration", 0.0) or 0.0) if self.loaded_video_info is not None else 0.0
        native_fps = float(self.loaded_video_info.get("fps", 0.0) or 0.0) if self.loaded_video_info is not None else 0.0
        playback_fps = native_fps if native_fps > 0 else max(1.0, float(self.video_sample_fps_var.get()))
        playback_fps = max(1.0, min(playback_fps, 60.0))
        frame_step = 1.0 / playback_fps

        max_time = duration
        if max_time <= 0 and hasattr(self, "video_picker_scale"):
            try:
                max_time = float(self.video_picker_scale.cget("to"))
            except Exception:
                max_time = current_time + 10.0
        if max_time <= 0:
            max_time = current_time + 10.0

        next_time = current_time + frame_step
        if next_time >= max_time:
            next_time = max_time
            self.video_picker_time_var.set(round(next_time, 3))
            self._render_timestamp_preview(next_time)
            self._pause_video_picker_playback()
            return

        self.video_picker_time_var.set(round(next_time, 3))
        self._render_timestamp_preview(next_time)
        delay_ms = max(15, min(120, int(round(frame_step * 1000.0))))
        self.video_picker_play_after_id = self.root.after(delay_ms, self._tick_video_picker_playback)

    def _apply_picker_time(self, target: str) -> None:
        timestamp = round(max(0.0, float(self.video_picker_time_var.get())), 3)
        total_duration = 0.0
        if self.loaded_video_info is not None:
            total_duration = float(self.loaded_video_info.get("duration", 0.0) or 0.0)

        current_start = max(0.0, float(self.video_start_var.get()))
        current_end = max(0.0, float(self.video_end_var.get()))
        current_length = max(0.5, current_end - current_start)

        if target == "start":
            new_start = timestamp
            new_end = current_end
            if new_end <= new_start:
                new_end = new_start + current_length
                if total_duration > 0:
                    new_end = min(total_duration, new_end)
                if new_end <= new_start and total_duration > 0:
                    new_start = max(0.0, total_duration - current_length)
                    new_end = total_duration
            self.video_start_var.set(round(new_start, 3))
            self.video_end_var.set(round(max(new_start + 0.1, new_end), 3))
            self.status_var.set(f"Selected start time: {self._format_seconds(float(self.video_start_var.get()))}")
        else:
            new_end = timestamp
            new_start = current_start
            if new_end <= new_start:
                new_start = max(0.0, new_end - current_length)
            self.video_start_var.set(round(max(0.0, new_start), 3))
            self.video_end_var.set(round(max(float(self.video_start_var.get()) + 0.1, new_end), 3))
            self.status_var.set(f"Selected end time: {self._format_seconds(float(self.video_end_var.get()))}")

        if total_duration > 0 and float(self.video_end_var.get()) > total_duration:
            self.video_end_var.set(round(total_duration, 3))
        self._sync_video_clip_info()
        if self.video_picker_window is not None:
            self.video_picker_target = target
            self.video_picker_window.title(
                f"Pick Video {'Start' if target == 'start' else 'End'} Timestamp"
            )
            self.video_picker_window.lift()
            self.video_picker_window.focus_force()
        self.video_picker_info_var.set(
            f"Timestamp: {self._format_seconds(timestamp)} | {self.video_clip_info_var.get()}"
        )

    def _import_clip_from_picker(self) -> None:
        self.import_video_clip(close_picker_on_success=True)

    def open_timestamp_picker(self, target: str = "start") -> None:
        if not self._require_video_support():
            return
        if not self.loaded_video_path:
            self.choose_video(show_picker=False)
            if not self.loaded_video_path:
                return

        self.video_picker_target = target
        if self.video_picker_window is not None:
            self._pause_video_picker_playback()
            self.video_picker_window.title(f"Pick Video {'Start' if target == 'start' else 'End'} Timestamp")
            initial_time = float(self.video_start_var.get()) if target == "start" else float(self.video_end_var.get())
            self.video_picker_time_var.set(max(0.0, initial_time))
            if hasattr(self, "video_picker_scale") and self.loaded_video_info is not None:
                duration = float(self.loaded_video_info.get("duration", 0.0) or 0.0)
                slider_max = duration if duration > 0 else max(10.0, float(self.video_picker_time_var.get()) + 10.0)
                self.video_picker_scale.configure(to=slider_max)
            self._schedule_timestamp_preview_update()
            self.video_picker_window.lift()
            self.video_picker_window.focus_force()
            return

        try:
            capture = self._open_video_capture(self.loaded_video_path)
        except Exception as exc:
            messagebox.showerror("Video Open Failed", str(exc))
            return

        duration = 0.0
        if self.loaded_video_info is not None:
            duration = float(self.loaded_video_info.get("duration", 0.0) or 0.0)

        window = tk.Toplevel(self.root)
        self._apply_window_icon(window)
        window.title(f"Pick Video {'Start' if target == 'start' else 'End'} Timestamp")
        window.geometry("780x620")
        window.minsize(720, 560)
        window.transient(self.root)

        self.video_picker_window = window
        self.video_picker_capture = capture
        initial_time = float(self.video_start_var.get()) if target == "start" else float(self.video_end_var.get())
        self.video_picker_time_var.set(max(0.0, initial_time))
        self.video_picker_info_var.set("Loading preview...")
        self.video_picker_playing = False

        body = ttk.Frame(window, padding=10)
        body.pack(fill="both", expand=True)

        self.video_picker_preview_label = ttk.Label(body, anchor="center")
        self.video_picker_preview_label.pack(fill="both", expand=True)

        controls = ttk.Frame(body)
        controls.pack(fill="x", pady=(10, 0))
        ttk.Label(controls, text="Timestamp (sec):").pack(side="left")
        time_entry = ttk.Entry(controls, textvariable=self.video_picker_time_var, width=10)
        time_entry.pack(side="left", padx=(6, 8))
        time_entry.bind("<Return>", lambda e: self._on_video_picker_scrub())
        time_entry.bind("<FocusOut>", lambda e: self._on_video_picker_scrub())

        slider_max = duration if duration > 0 else max(10.0, float(self.video_picker_time_var.get()) + 10.0)
        self.video_picker_scale = ttk.Scale(
            controls,
            from_=0.0,
            to=slider_max,
            variable=self.video_picker_time_var,
            orient="horizontal",
            command=self._on_video_picker_scrub,
        )
        self.video_picker_scale.pack(side="left", fill="x", expand=True)

        ttk.Label(body, textvariable=self.video_picker_info_var).pack(anchor="w", pady=(8, 0))

        playback_row = ttk.Frame(body)
        playback_row.pack(fill="x", pady=(10, 0))
        self.video_picker_play_button = ttk.Button(playback_row, text="Play", command=self._start_video_picker_playback)
        self.video_picker_play_button.pack(side="left")
        self.video_picker_pause_button = ttk.Button(playback_row, text="Pause", command=self._pause_video_picker_playback)
        self.video_picker_pause_button.pack(side="left", padx=(8, 0))

        buttons_top = ttk.Frame(body)
        buttons_top.pack(fill="x", pady=(8, 0))
        ttk.Button(buttons_top, text="Use as Start", command=lambda: self._apply_picker_time("start")).pack(side="left")
        ttk.Button(buttons_top, text="Use as End", command=lambda: self._apply_picker_time("end")).pack(side="left", padx=(8, 0))

        buttons_bottom = ttk.Frame(body)
        buttons_bottom.pack(fill="x", pady=(8, 0))
        ttk.Button(buttons_bottom, text="Import Clip Into Editor", command=self._import_clip_from_picker).pack(side="left")
        ttk.Button(buttons_bottom, text="Close", command=self._close_timestamp_picker).pack(side="left", padx=(8, 0))

        window.protocol("WM_DELETE_WINDOW", self._close_timestamp_picker)
        self._update_video_picker_play_buttons()
        self._schedule_timestamp_preview_update()

    def _read_video_info(self, path: str) -> Dict[str, float | int | str]:
        capture = self._open_video_capture(path)
        try:
            fps = float(capture.get(cv2.CAP_PROP_FPS) or 0.0)
            frame_count = int(capture.get(cv2.CAP_PROP_FRAME_COUNT) or 0)
            width = int(capture.get(cv2.CAP_PROP_FRAME_WIDTH) or 0)
            height = int(capture.get(cv2.CAP_PROP_FRAME_HEIGHT) or 0)
            duration = (frame_count / fps) if fps > 0 and frame_count > 0 else 0.0
            return {
                "fps": fps,
                "frame_count": frame_count,
                "width": width,
                "height": height,
                "duration": duration,
                "backend": self._video_backend_name(capture),
            }
        finally:
            capture.release()

    def choose_video(self, show_picker: bool = True) -> None:
        if not self._require_video_support():
            return

        self._close_timestamp_picker()
        path = filedialog.askopenfilename(title="Choose Video", filetypes=SUPPORTED_VIDEO_TYPES)
        if not path:
            return

        if not self._confirm_replace_editor("video"):
            return

        try:
            self._show_busy_dialog(
                "Loading video clip...",
                "Reading video information",
                indeterminate=True,
            )
            info = self._read_video_info(path)
        except Exception as exc:
            self._close_busy_dialog()
            messagebox.showerror("Video Load Failed", str(exc))
            return
        finally:
            self._close_busy_dialog()

        self._reset_editor_fresh()
        self._set_loaded_video_source(path, info)
        self.video_start_var.set(0.0)

        duration = float(info.get("duration", 0.0) or 0.0)
        source_fps = float(info.get("fps", 0.0) or 0.0)
        if duration > 0:
            self.video_end_var.set(round(min(3.0, duration), 2))
        else:
            self.video_end_var.set(2.0)
        if source_fps > 0:
            self.video_sample_fps_var.set(round(min(12.0, source_fps), 2))

        self._sync_video_clip_info()
        self.status_var.set(f"Loaded video: {path}")
        if show_picker:
            self.open_timestamp_picker("start")

    def import_video_clip(self, close_picker_on_success: bool = False) -> None:
        if not self._require_video_support():
            return
        if not self.loaded_video_path:
            self.choose_video(show_picker=True)
            return

        video_path = self.loaded_video_path
        assert video_path is not None

        try:
            start_sec = max(0.0, float(self.video_start_var.get()))
            end_sec = float(self.video_end_var.get())
            sample_fps = float(self.video_sample_fps_var.get())
        except Exception:
            messagebox.showerror("Invalid Video Settings", "Start, End, and Sample FPS must be numbers.")
            return

        if end_sec <= start_sec:
            messagebox.showerror("Invalid Video Settings", "End time must be greater than start time.")
            return
        if sample_fps <= 0:
            messagebox.showerror("Invalid Video Settings", "Sample FPS must be greater than 0.")
            return

        if self.loaded_video_info is None:
            try:
                self.loaded_video_info = self._read_video_info(video_path)
            except Exception as exc:
                messagebox.showerror("Video Load Failed", str(exc))
                return

        total_duration = float(self.loaded_video_info.get("duration", 0.0) or 0.0)
        if total_duration > 0 and start_sec >= total_duration:
            messagebox.showerror("Invalid Start Time", "Start time must be inside the video duration.")
            return

        effective_end = end_sec
        if total_duration > 0:
            effective_end = min(end_sec, total_duration)
            if effective_end <= start_sec:
                messagebox.showerror("Invalid Clip Range", "The selected start/end range is outside the video duration.")
                return

        effective_length = effective_end - start_sec
        sample_count = max(1, int(round(effective_length * sample_fps)))
        clipped_by_limit = False
        if sample_count > VIDEO_IMPORT_MAX_FRAMES:
            sample_count = VIDEO_IMPORT_MAX_FRAMES
            clipped_by_limit = True

        try:
            capture = self._open_video_capture(video_path)
        except Exception as exc:
            messagebox.showerror("Video Open Failed", str(exc))
            return

        video_base = os.path.splitext(os.path.basename(video_path))[0]
        source_fps = float(self.loaded_video_info.get("fps", 0.0) or 0.0)
        staging_dir = tempfile.mkdtemp(prefix="gbs_video_clip_stage_")
        imported_paths: List[str] = []

        try:
            self.status_var.set(f"Importing {sample_count} frame(s) from video...")
            self._show_busy_dialog(
                "Importing video clip...",
                f"0 / {sample_count} frame(s)",
                progress_value=0,
                progress_total=sample_count,
            )

            for index in range(sample_count):
                sample_time = start_sec + (index / sample_fps)
                if sample_time >= effective_end:
                    break

                capture.set(cv2.CAP_PROP_POS_MSEC, sample_time * 1000.0)
                ok, frame = capture.read()

                if not ok and source_fps > 0:
                    capture.set(cv2.CAP_PROP_POS_FRAMES, int(round(sample_time * source_fps)))
                    ok, frame = capture.read()

                if not ok or frame is None:
                    if imported_paths:
                        break
                    raise ValueError("Could not read frames from the selected clip range.")

                rgba = cv2.cvtColor(frame, cv2.COLOR_BGR2RGBA)
                image = Image.fromarray(rgba, "RGBA")
                out_path = os.path.join(staging_dir, f"{video_base}_{index:04d}.png")
                image.save(out_path)
                imported_paths.append(out_path)
                self._update_busy_dialog(
                    progress_text=f"{len(imported_paths)} / {sample_count} frame(s)",
                    progress_value=len(imported_paths),
                    progress_total=sample_count,
                )
        except Exception as exc:
            self._close_busy_dialog()
            messagebox.showerror("Video Import Failed", str(exc))
            return
        finally:
            capture.release()
            self._close_busy_dialog()

        if not imported_paths:
            shutil.rmtree(staging_dir, ignore_errors=True)
            messagebox.showerror("Video Import Failed", "No frames were imported from that clip.")
            return

        self.imported_video_counter += 1
        imported_items: List[FrameItem] = []
        try:
            self._clear_loaded_frames(reset_temp_assets=True)
            self.current_project_path = None

            clip_dir = os.path.join(self.session_tempdir, f"video_clip_{self.imported_video_counter:04d}")
            os.makedirs(clip_dir, exist_ok=True)
            for path in imported_paths:
                final_path = os.path.join(clip_dir, os.path.basename(path))
                shutil.move(path, final_path)
                imported_items.append(FrameItem(path=final_path, display_name=os.path.basename(final_path)))
        except Exception as exc:
            messagebox.showerror(
                "Video Import Failed",
                f"Imported clip frames could not be loaded into the editor.\n\n{exc}"
            )
            self.status_var.set(f"Video import failed: {exc}")
            return
        finally:
            shutil.rmtree(staging_dir, ignore_errors=True)
        if not imported_items:
            messagebox.showerror("Video Import Failed", "The clip imported, but the editor could not adopt the new frames.")
            return

        status = f"Imported {len(imported_paths)} frame(s) from video."
        if clipped_by_limit:
            status += f" Limited to the first {VIDEO_IMPORT_MAX_FRAMES} sampled frames."
        self._set_editor_frames(imported_items, status)
        self._sync_video_clip_info()
        if close_picker_on_success:
            self._close_timestamp_picker()
        messagebox.showinfo("Clip Imported", f"Imported {len(imported_paths)} frame(s) into the editor.")

    def _maximize_window(self) -> None:
        try:
            if sys.platform.startswith("win"):
                self.root.state("zoomed")
                return
            self.root.attributes("-zoomed", True)
        except Exception:
            pass

    def add_images(self) -> None:
        paths = filedialog.askopenfilenames(title="Choose Images", filetypes=SUPPORTED_IMAGE_TYPES)
        if not paths:
            return
        if not self._confirm_replace_editor("image set"):
            return
        self._reset_editor_fresh()
        items = [FrameItem(path=path, display_name=os.path.basename(path)) for path in paths]
        self._set_editor_frames(items, f"Loaded {len(paths)} image(s).")

    def add_folder(self) -> None:
        folder = filedialog.askdirectory(title="Choose Folder")
        if not folder:
            return

        exts = {".png", ".jpg", ".jpeg", ".bmp", ".webp", ".gif"}
        files = []
        for name in sorted(os.listdir(folder)):
            full = os.path.join(folder, name)
            if os.path.isfile(full) and os.path.splitext(name.lower())[1] in exts:
                files.append(full)

        if not files:
            messagebox.showinfo("No Images Found", "No supported images were found in that folder.")
            return

        if not self._confirm_replace_editor("image folder"):
            return
        self._reset_editor_fresh()
        items = [FrameItem(path=path, display_name=os.path.basename(path)) for path in files]
        self._set_editor_frames(items, f"Loaded {len(files)} image(s) from folder.")

    def remove_selected(self) -> None:
        indices = list(self.listbox.curselection())
        if not indices:
            return
        for index in reversed(indices):
            del self.frames[index]
            self.listbox.delete(index)
        self._prune_image_cache()
        self.status_var.set(f"Removed {len(indices)} selected item(s).")
        self.refresh_preview()

    def clear_frames(self) -> None:
        if not self.frames and not self.loaded_video_path and not self.current_project_path:
            return
        if not messagebox.askyesno("Clear All", "Reset the editor and remove the current frames, video selection, and project state?"):
            return
        self._reset_editor_fresh()
        self.status_var.set("Editor cleared and reset.")

    def _selected_indices(self) -> List[int]:
        return list(self.listbox.curselection())

    def move_up(self) -> None:
        indices = self._selected_indices()
        if not indices or indices[0] == 0:
            return
        for i in indices:
            self.frames[i - 1], self.frames[i] = self.frames[i], self.frames[i - 1]
        self._rebuild_listbox(indices=[i - 1 for i in indices])
        self.refresh_preview()

    def move_down(self) -> None:
        indices = self._selected_indices()
        if not indices or indices[-1] == len(self.frames) - 1:
            return
        for i in reversed(indices):
            self.frames[i + 1], self.frames[i] = self.frames[i], self.frames[i + 1]
        self._rebuild_listbox(indices=[i + 1 for i in indices])
        self.refresh_preview()

    def move_top(self) -> None:
        indices = self._selected_indices()
        if not indices:
            return
        selected = [self.frames[i] for i in indices]
        remaining = [self.frames[i] for i in range(len(self.frames)) if i not in set(indices)]
        self.frames = selected + remaining
        self._rebuild_listbox(indices=list(range(len(selected))))
        self.refresh_preview()

    def move_bottom(self) -> None:
        indices = self._selected_indices()
        if not indices:
            return
        selected_set = set(indices)
        remaining = [self.frames[i] for i in range(len(self.frames)) if i not in selected_set]
        selected = [self.frames[i] for i in indices]
        start = len(remaining)
        self.frames = remaining + selected
        self._rebuild_listbox(indices=list(range(start, start + len(selected))))
        self.refresh_preview()

    def _rebuild_listbox(self, indices: Optional[List[int]] = None) -> None:
        self.listbox.delete(0, "end")
        for item in self.frames:
            self.listbox.insert("end", self._frame_label(item))
        if indices:
            for i in indices:
                self.listbox.select_set(i)

    def _load_image_from_disk(self, path: str) -> Image.Image:
        with Image.open(path) as img:
            if getattr(img, "is_animated", False):
                img.seek(0)
            return img.convert("RGBA")

    def _load_image(self, path: str) -> Image.Image:
        stat = os.stat(path)
        with self.image_cache_lock:
            cached = self.image_cache.get(path)
            if cached is not None and cached.mtime_ns == stat.st_mtime_ns and cached.size == stat.st_size:
                return cached.image.copy()

        loaded = self._load_image_from_disk(path)
        with self.image_cache_lock:
            self.image_cache[path] = ImageCacheEntry(
                mtime_ns=stat.st_mtime_ns,
                size=stat.st_size,
                image=loaded.copy(),
            )
        return loaded

    def _resolve_export_size(self) -> Optional[Tuple[int, int]]:
        mode = self.resize_mode_var.get()
        if mode == "original":
            return None
        width = max(0, int(self.export_width_var.get()))
        height = max(0, int(self.export_height_var.get()))
        if width == 0 or height == 0:
            raise ValueError("Width and Height must both be greater than 0 for fit/stretch resize modes.")
        return (width, height)

    def _capture_render_settings(self) -> RenderSettings:
        resize_mode = self.resize_mode_var.get()
        bg_rgba = self._parse_hex_color(self.bg_hex_var.get()) if resize_mode == "fit_within" else (0, 0, 0, 255)
        enable_effects = self.enable_effects_var.get()
        return RenderSettings(
            frame_paths=tuple(item.path for item in self.frames),
            duration_ms=max(20, int(self.duration_ms_var.get())),
            resize_mode=resize_mode,
            export_size=self._resolve_export_size(),
            bg_rgba=bg_rgba,
            enable_effects=enable_effects,
            reverse_order=self.reverse_order_var.get(),
            pingpong=self.pingpong_var.get(),
            grayscale=self.grayscale_var.get(),
            flip_h=self.flip_h_var.get(),
            flip_v=self.flip_v_var.get(),
            brightness=float(self.brightness_var.get()) if enable_effects and self.enable_brightness_var.get() else None,
            contrast=float(self.contrast_var.get()) if enable_effects and self.enable_contrast_var.get() else None,
            sharpness=float(self.sharpness_var.get()) if enable_effects and self.enable_sharpness_var.get() else None,
            rotate_degrees=int(self.rotate_var.get()) if enable_effects and self.enable_rotate_var.get() else 0,
        )

    def _apply_effects(self, img: Image.Image, settings: RenderSettings) -> Image.Image:
        if not settings.enable_effects:
            return img

        out = img.copy()

        if settings.flip_h:
            out = ImageOps.mirror(out)
        if settings.flip_v:
            out = ImageOps.flip(out)
        if settings.rotate_degrees != 0:
            out = out.rotate(settings.rotate_degrees, expand=True, resample=Image.Resampling.BICUBIC)
        if settings.grayscale:
            out = ImageOps.grayscale(out).convert("RGBA")
        if settings.brightness is not None:
            out = ImageEnhance.Brightness(out).enhance(settings.brightness)
        if settings.contrast is not None:
            out = ImageEnhance.Contrast(out).enhance(settings.contrast)
        if settings.sharpness is not None:
            out = ImageEnhance.Sharpness(out).enhance(settings.sharpness)
        return out

    def _resize_for_export(self, img: Image.Image, settings: RenderSettings) -> Image.Image:
        if settings.export_size is None:
            return img

        tw, th = settings.export_size

        if settings.resize_mode == "stretch":
            return img.resize((tw, th), Image.Resampling.LANCZOS)

        if settings.resize_mode == "fit_within":
            base = Image.new("RGBA", (tw, th), settings.bg_rgba)
            fitted = img.copy()
            fitted.thumbnail((tw, th), Image.Resampling.LANCZOS)
            x = (tw - fitted.width) // 2
            y = (th - fitted.height) // 2
            base.alpha_composite(fitted, (x, y))
            return base

        return img

    def _parse_hex_color(self, value: str) -> Tuple[int, int, int, int]:
        value = value.strip()
        if not value.startswith("#"):
            raise ValueError("Padding BG color must be a hex value like #000000")
        hex_part = value[1:]
        if len(hex_part) == 6:
            r = int(hex_part[0:2], 16)
            g = int(hex_part[2:4], 16)
            b = int(hex_part[4:6], 16)
            return (r, g, b, 255)
        if len(hex_part) == 8:
            r = int(hex_part[0:2], 16)
            g = int(hex_part[2:4], 16)
            b = int(hex_part[4:6], 16)
            a = int(hex_part[6:8], 16)
            return (r, g, b, a)
        raise ValueError("Padding BG color must be #RRGGBB or #RRGGBBAA")

    def _normalize_frame_sizes(self, frames: List[Image.Image]) -> List[Image.Image]:
        if not frames:
            return frames

        widths = {img.width for img in frames}
        heights = {img.height for img in frames}
        if len(widths) == 1 and len(heights) == 1:
            return frames

        canvas_size = (max(widths), max(heights))
        normalized: List[Image.Image] = []
        for img in frames:
            canvas = Image.new("RGBA", canvas_size, (0, 0, 0, 0))
            offset = ((canvas_size[0] - img.width) // 2, (canvas_size[1] - img.height) // 2)
            canvas.alpha_composite(img, offset)
            normalized.append(canvas)
        return normalized

    def _build_frames_from_settings(self, settings: RenderSettings) -> List[Image.Image]:
        if not settings.frame_paths:
            raise ValueError("No frames loaded.")

        raw_paths = list(settings.frame_paths)
        if settings.enable_effects and settings.reverse_order:
            raw_paths = list(reversed(raw_paths))

        built: List[Image.Image] = []
        for path in raw_paths:
            img = self._load_image(path)
            img = self._apply_effects(img, settings)
            img = self._resize_for_export(img, settings)
            built.append(img)

        if settings.enable_effects and settings.pingpong and len(built) > 1:
            built = built + built[-2:0:-1]

        return self._normalize_frame_sizes(built)

    def _scaled_settings_for_preview(self, settings: RenderSettings, preview_size: Tuple[int, int]) -> RenderSettings:
        if settings.export_size is None:
            return settings

        target_w, target_h = settings.export_size
        preview_w, preview_h = preview_size
        scale = min(1.0, preview_w / max(1, target_w), preview_h / max(1, target_h))
        if scale >= 1.0:
            return settings

        return replace(
            settings,
            export_size=(
                max(1, int(target_w * scale)),
                max(1, int(target_h * scale)),
            ),
        )

    def _build_preview_images(self, settings: RenderSettings, preview_size: Tuple[int, int]) -> List[Image.Image]:
        preview_settings = self._scaled_settings_for_preview(settings, preview_size)
        built = self._build_frames_from_settings(preview_settings)
        preview_frames: List[Image.Image] = []
        for img in built:
            frame = img.copy()
            frame.thumbnail(preview_size, Image.Resampling.LANCZOS)
            preview_frames.append(frame)
        return preview_frames

    def _build_export_frames(self) -> List[Image.Image]:
        return self._build_frames_from_settings(self._capture_render_settings())

    def _get_preview_target_size(self) -> Tuple[int, int]:
        width = max(160, self.preview_label.winfo_width() - 12)
        height = max(120, self.preview_label.winfo_height() - 12)
        if width <= 160 or height <= 120:
            return PREVIEW_SIZE
        return (width, height)

    def refresh_preview(self, force_play: bool = False) -> None:
        try:
            self._queue_preview_render(force_play=force_play)
        except Exception as exc:
            if not self.preview_frames:
                self._clear_preview(f"Preview error: {exc}")
            self.preview_info_var.set(f"Preview error: {exc}")
            self.status_var.set(f"Preview error: {exc}")

    def start_preview(self) -> None:
        if not self.preview_frames:
            self.refresh_preview(force_play=True)
            return
        if self.preview_playing:
            return
        self.preview_playing = True
        self._tick_preview()

    def _tick_preview(self) -> None:
        if not self.preview_playing or not self.preview_frames:
            return
        self.preview_label.configure(image=self.preview_frames[self.preview_index])
        self.preview_label.image = self.preview_frames[self.preview_index]
        self.preview_index = (self.preview_index + 1) % len(self.preview_frames)
        delay = max(20, int(self.duration_ms_var.get()))
        self.preview_after_id = self.root.after(delay, self._tick_preview)

    def stop_preview(self) -> None:
        self.preview_playing = False
        if self.preview_after_id is not None:
            try:
                self.root.after_cancel(self.preview_after_id)
            except Exception:
                pass
            self.preview_after_id = None

    def export_gif(self) -> None:
        if not self.frames:
            messagebox.showwarning("No Frames", "Please add images before exporting.")
            return

        out_path = filedialog.asksaveasfilename(
            title="Export GIF",
            defaultextension=".gif",
            filetypes=[("GIF files", "*.gif")]
        )
        if not out_path:
            return

        try:
            frames = self._build_export_frames()
            rgba_frames = []
            for frame in frames:
                if frame.mode != "RGBA":
                    frame = frame.convert("RGBA")
                rgba_frames.append(frame)

            duration = max(20, int(self.duration_ms_var.get()))
            loop = 0 if self.loop_forever_var.get() else max(0, int(self.loop_count_var.get()))

            first, rest = rgba_frames[0], rgba_frames[1:]
            first.save(
                out_path,
                save_all=True,
                append_images=rest,
                duration=duration,
                loop=loop,
                optimize=False,
                disposal=2
            )

            self.last_export_path = out_path
            self.status_var.set(f"Exported GIF: {out_path}")
            messagebox.showinfo("Export Complete", f"Saved GIF to:\n\n{out_path}")
        except Exception as exc:
            tb = traceback.format_exc()
            messagebox.showerror("Export Failed", f"{exc}\n\n{tb}")
            self.status_var.set(f"Export failed: {exc}")

    def export_png_frames(self) -> None:
        if not self.frames:
            messagebox.showwarning("No Frames", "Please load images or import a video clip first.")
            return

        out_dir = filedialog.askdirectory(title="Choose Folder For PNG Frames")
        if not out_dir:
            return

        existing_sequence_files = [
            name for name in os.listdir(out_dir)
            if re.fullmatch(r"gbs_frame_\d{4}\.png", name)
        ]
        if existing_sequence_files and not messagebox.askyesno(
            "Replace Existing PNG Frames",
            f"{len(existing_sequence_files)} existing exported frame file(s) were found in that folder.\n\nReplace them?"
        ):
            return

        try:
            frames = self._build_export_frames()
            self._show_busy_dialog(
                "Exporting PNG frames...",
                f"0 / {len(frames)} frame(s)",
                progress_value=0,
                progress_total=len(frames),
            )
            for name in existing_sequence_files:
                os.remove(os.path.join(out_dir, name))
            for index, frame in enumerate(frames, start=1):
                out_path = os.path.join(out_dir, f"gbs_frame_{index:04d}.png")
                frame.save(out_path, format="PNG")
                self._update_busy_dialog(
                    progress_text=f"{index} / {len(frames)} frame(s)",
                    progress_value=index,
                    progress_total=len(frames),
                )
        except Exception as exc:
            self._close_busy_dialog()
            tb = traceback.format_exc()
            messagebox.showerror("PNG Export Failed", f"{exc}\n\n{tb}")
            self.status_var.set(f"PNG export failed: {exc}")
            return
        finally:
            self._close_busy_dialog()

        self.status_var.set(f"Exported {len(frames)} PNG frame(s) to: {out_dir}")
        messagebox.showinfo("PNG Frames Exported", f"Saved {len(frames)} PNG frame(s) to:\n\n{out_dir}")


def run_self_test() -> int:
    try:
        tmpdir = tempfile.mkdtemp(prefix="gif_builder_selftest_")
        paths = []
        specs = [
            ((320, 180), (10, 20, 80)),
            ((260, 240), (20, 60, 140)),
            ((420, 210), (60, 120, 220)),
        ]
        for i, (size, color) in enumerate(specs):
            img = Image.new("RGBA", size, color + (255,))
            path = os.path.join(tmpdir, f"frame_{i:03d}.png")
            img.save(path)
            paths.append(path)

        class Dummy:
            pass

        root = tk.Tk()
        root.withdraw()
        app = GIFBuilderApp(root)
        app.frames = [FrameItem(path=p, display_name=os.path.basename(p)) for p in paths]
        app._rebuild_listbox()
        app.enable_effects_var.set(True)
        app.enable_rotate_var.set(True)
        app.rotate_var.set(18)
        app.enable_brightness_var.set(True)
        app.brightness_var.set(1.1)
        app.export_size_preset_var.set("640 x 360")
        app._apply_export_size_preset("640 x 360")
        app.video_path_var.set("selftest_clip.mp4")
        app.video_start_var.set(1.25)
        app.video_end_var.set(2.75)
        app.video_sample_fps_var.set(12.0)
        flip_source = Image.new("RGBA", (2, 1), (0, 0, 0, 0))
        flip_source.putpixel((0, 0), (255, 0, 0, 255))
        flip_source.putpixel((1, 0), (0, 0, 255, 255))
        flip_settings = RenderSettings(
            frame_paths=tuple(),
            duration_ms=120,
            resize_mode="original",
            export_size=None,
            bg_rgba=(0, 0, 0, 255),
            enable_effects=True,
            reverse_order=False,
            pingpong=False,
            grayscale=False,
            flip_h=True,
            flip_v=False,
            brightness=None,
            contrast=None,
            sharpness=None,
            rotate_degrees=0,
        )
        flipped = app._apply_effects(flip_source, flip_settings)
        assert flipped.getpixel((0, 0)) == (0, 0, 255, 255)
        preview_settings = app._capture_render_settings()
        preview = app._build_preview_images(preview_settings, (240, 160))
        assert len(preview) == 3
        built = app._build_export_frames()
        assert len(built) == 3
        assert len({img.size for img in built}) == 1
        project_path = os.path.join(tmpdir, "test_project.gbs")
        app._write_project_archive(project_path)
        assert os.path.exists(project_path) and os.path.getsize(project_path) > 0
        manifest = app._read_project_manifest(project_path)
        app._load_project_archive(project_path, manifest)
        assert len(app.frames) == 3
        assert app.current_project_path == project_path
        assert app.export_size_preset_var.get() == "640 x 360"
        assert int(app.export_width_var.get()) == 640
        assert int(app.export_height_var.get()) == 360
        assert abs(float(app.video_start_var.get()) - 1.25) < 0.01
        assert abs(float(app.video_end_var.get()) - 2.75) < 0.01

        out = os.path.join(tmpdir, "test.gif")
        first, rest = built[0], built[1:]
        first.save(out, save_all=True, append_images=rest, duration=100, loop=0, optimize=False, disposal=2)
        assert os.path.exists(out) and os.path.getsize(out) > 0
        app._on_close()
        print(f"SELF-TEST OK: {out}")
        return 0
    except Exception:
        traceback.print_exc()
        return 1


def main() -> int:
    install_exception_popup()

    if "--self-test" in sys.argv:
        return run_self_test()

    root = tk.Tk()
    app = GIFBuilderApp(root)
    root.mainloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
