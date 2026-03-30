from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path


APP_NAME = "GIF Builder Studio"
DEFAULT_BUNDLE_ID = os.environ.get("BUNDLE_ID", "com.example.gifbuilderstudio")
TARGET_ARCH = os.environ.get("TARGET_ARCH", "arm64")
ROOT = Path(__file__).resolve().parents[1]
DIST = ROOT / "dist"
BUILD = ROOT / "build"
ICON_ICNS = ROOT / "assets" / "gbs_icon.icns"
ICON_PNG = ROOT / "assets" / "gbs_icon.png"
LICENSES = ROOT / "THIRD_PARTY_LICENSES.txt"
ENTRY_CANDIDATES = [
    os.environ.get("ENTRY_SCRIPT", "").strip(),
    "gif_builder_studio_mac_ready.py",
    "gif_builder_studio.py",
]


def run(cmd: list[str]) -> None:
    print("+", " ".join(cmd))
    subprocess.run(cmd, check=True, cwd=ROOT)


def remove_if_exists(path: Path) -> None:
    if path.is_dir():
        shutil.rmtree(path)
    elif path.exists():
        path.unlink()


def find_entry_script() -> Path:
    for candidate in ENTRY_CANDIDATES:
        if not candidate:
            continue
        path = ROOT / candidate
        if path.exists() and path.is_file():
            return path
    available = sorted(p.name for p in ROOT.glob("*.py"))
    raise SystemExit(
        "Could not find a build entry script. Expected one of: "
        f"{', '.join([c for c in ENTRY_CANDIDATES if c])}. "
        f"Python files found in repo root: {available}"
    )


def main() -> int:
    entry = find_entry_script()
    print(f"Using entry script: {entry.name}")

    remove_if_exists(BUILD)
    remove_if_exists(DIST)
    spec_file = ROOT / f"{APP_NAME}.spec"
    remove_if_exists(spec_file)

    cmd = [
        sys.executable,
        "-m",
        "PyInstaller",
        str(entry),
        "--noconfirm",
        "--clean",
        "--windowed",
        "--onedir",
        "--name",
        APP_NAME,
        "--target-arch",
        TARGET_ARCH,
        "--argv-emulation",
        "--osx-bundle-identifier",
        DEFAULT_BUNDLE_ID,
    ]

    if ICON_ICNS.exists():
        cmd += ["--icon", str(ICON_ICNS)]
    elif ICON_PNG.exists():
        cmd += ["--icon", str(ICON_PNG)]

    if ICON_PNG.exists():
        cmd += ["--add-data", f"{ICON_PNG}{os.pathsep}."]
    if LICENSES.exists():
        cmd += ["--add-data", f"{LICENSES}{os.pathsep}."]

    run(cmd)

    app_bundle = DIST / f"{APP_NAME}.app"
    if not app_bundle.exists():
        raise SystemExit(f"Build did not produce expected app bundle: {app_bundle}")

    print(f"Built: {app_bundle}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
