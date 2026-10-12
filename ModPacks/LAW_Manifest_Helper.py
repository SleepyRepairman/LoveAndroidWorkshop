#!/usr/bin/env python3
"""
Love Android Workshop Manifest Helper v10
I made this script with ChatGPT to help compile mods. If you encounter any issue with it please contact me on discord.
"""

from __future__ import annotations

import io
import json
import os
import re
import shutil
import struct
import time
import uuid
import zipfile
import zlib
from dataclasses import dataclass, field
from pathlib import Path
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
from typing import Dict, List, Optional, Tuple

try:
    from PIL import Image as PILImage
except ImportError:
    PILImage = None


APP_TITLE = "LAW Manifest Helper"
FORMAT_VERSION = 1
CONFIG_FILE_NAME = "manifest_helper_config.json"
CROP_CACHE_FILE_NAME = "manifest_helper_crop_cache.json"
PNG_WRITE_COMPRESSION_LEVEL = 3

VERSION_RE = re.compile(r"^\d+(?:\.\d+){1,3}$")
VALID_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.-]{0,63}$")

EYES_FOLDERS = ["Eyes", "Pupils"]
PUBIC_HAIR_FOLDERS = ["PubicHair", "Pubic Hair"]

MULTIPART_CONFIG = {
    "Head": {
        "manifest_key": "head",
        "folders": ["Head", "Heads"],
    },
    "Hair": {
        "manifest_key": "hair",
        "folders": ["Hair"],
    },
    "Body": {
        "manifest_key": "body",
        "folders": ["Body"],
    },
    "ClothTop": {
        "manifest_key": "clothesTop",
        "folders": ["ClothTop", "ClothesTop", "Top"],
    },
    "ClothBottom": {
        "manifest_key": "clothesBottom",
        "folders": ["ClothBottom", "ClothesBottom", "Bottom"],
    },
}

TAB_ORDER = ["Eyes", "PubicHair", "Head", "Hair", "Body", "ClothTop", "ClothBottom"]

MULTIPART_SIZE_VARIANTS = ("Small", "Medium", "Big")
SIZE_VARIANT_CATEGORIES = {"Body", "ClothTop"}

MULTIPART_CANVAS_WIDTH = 4000
MULTIPART_CANVAS_HEIGHT = 4000
MULTIPART_CROP_PADDING = 8
PNG_SIGNATURE = b"\x89PNG\r\n\x1a\n"


def natural_key(value: str):
    return [
        int(part) if part.isdigit() else part.casefold()
        for part in re.split(r"(\d+)", value)
    ]


def to_posix_relative(path: Path, root: Path) -> str:
    return path.resolve().relative_to(root.resolve()).as_posix()


def valid_id(value: str) -> bool:
    return bool(VALID_ID_RE.fullmatch(value or ""))


def parse_compatible_bodies_text(value: str) -> List[str]:
    result: List[str] = []
    seen = set()

    for raw in re.split(r"[,;\n]+", value or ""):
        token = raw.strip()

        if not token:
            continue

        folded = token.casefold()

        if folded in seen:
            continue

        seen.add(folded)
        result.append(token)

    return result


def format_compatible_bodies(value) -> str:
    if not isinstance(value, list):
        return ""

    return ", ".join(
        str(item).strip()
        for item in value
        if str(item).strip()
    )


def valid_compatible_body(value: str) -> bool:
    token = (value or "").strip()

    if token == "*":
        return True

    if ":" not in token:
        return valid_id(token)

    mod_id, body_id = token.split(":", 1)
    return valid_id(mod_id) and valid_id(body_id)


def normalize_part_stem(file_stem: str, resource_id: str) -> str:
    if resource_id and file_stem.casefold().endswith(resource_id.casefold()):
        stripped = file_stem[: len(file_stem) - len(resource_id)]
        if stripped:
            return stripped

    return file_stem


def split_multipart_size_variant(stem: str) -> Tuple[str, Optional[str]]:
    """
    ShirtChest_Small -> ("ShirtChest", "Small")
    ShirtChest_Medium -> ("ShirtChest", "Medium")
    ShirtChest_Big -> ("ShirtChest", "Big")
    ShirtChest -> ("ShirtChest", None)
    """
    match = re.match(r"^(.*)_(Small|Medium|Big)$", stem, re.IGNORECASE)

    if not match:
        return stem, None

    base = match.group(1)
    raw_size = match.group(2).casefold()

    for size in MULTIPART_SIZE_VARIANTS:
        if size.casefold() == raw_size:
            return base, size

    return stem, None


def split_body_variation(stem: str) -> Tuple[str, Optional[str]]:
    """
    BodyV1 -> ("BodyV1", None)
    BodyV1-LowerOnly -> ("BodyV1", "LowerOnly")
    BodyV1_Small-Turn -> ("BodyV1_Small", "Turn")

    The first '-' starts the body variation. Everything after it is kept as
    the variation id, allowing names such as Turn-Back if desired.
    """
    if "-" not in stem:
        return stem, None

    base, variation = stem.split("-", 1)
    variation = variation.strip()

    if not variation:
        return stem, None

    return base, variation


def parse_multipart_part_stem(category: str, file_stem: str, resource_id: str):
    """Return (logical_stem, base_part_key, part_key, size, variation).

    For Body, variation is parsed after size:
        BodyV1_Small-Turn -> logical BodyV1, base key Body, part key Body-Turn,
                             size Small, variation Turn.
    """
    working_stem = file_stem
    variation = None

    if category == "Body":
        working_stem, variation = split_body_variation(working_stem)

    size = None
    logical_stem = working_stem

    if category in SIZE_VARIANT_CATEGORIES:
        logical_stem, size = split_multipart_size_variant(working_stem)

    base_part_key = normalize_part_stem(logical_stem, resource_id)
    part_key = base_part_key

    if variation:
        part_key += "-" + variation

    return logical_stem, base_part_key, part_key, size, variation


def looks_left(stem: str) -> bool:
    s = stem.casefold()
    return (
        "left" in s
        or "eyeleft" in s
        or s.endswith("_l")
        or s.endswith("-l")
        or s.endswith(".l")
    )


def looks_right(stem: str) -> bool:
    s = stem.casefold()
    return (
        "right" in s
        or "eyeright" in s
        or s.endswith("_r")
        or s.endswith("-r")
        or s.endswith(".r")
    )




class PngCropError(Exception):
    pass


@dataclass(frozen=True)
class CropInfo:
    canvas_width: int
    canvas_height: int
    x: int
    y: int
    width: int
    height: int

    @property
    def bottom_offset(self) -> int:
        return self.canvas_height - self.y - self.height

    @property
    def runtime_bytes_rgba32(self) -> int:
        return self.width * self.height * 4


def _paeth_predictor(a: int, b: int, c: int) -> int:
    p = a + b - c
    pa = abs(p - a)
    pb = abs(p - b)
    pc = abs(p - c)

    if pa <= pb and pa <= pc:
        return a
    if pb <= pc:
        return b
    return c


def _png_chunks(data: bytes):
    if not data.startswith(PNG_SIGNATURE):
        raise PngCropError("Invalid PNG signature.")

    offset = len(PNG_SIGNATURE)

    while offset < len(data):
        if offset + 12 > len(data):
            raise PngCropError("Truncated PNG chunk.")

        length = struct.unpack(">I", data[offset:offset + 4])[0]
        chunk_type = data[offset + 4:offset + 8]
        chunk_start = offset + 8
        chunk_end = chunk_start + length
        crc_end = chunk_end + 4

        if crc_end > len(data):
            raise PngCropError("Truncated PNG chunk data.")

        yield chunk_type, data[chunk_start:chunk_end]
        offset = crc_end

        if chunk_type == b"IEND":
            break


def _png_chunk(chunk_type: bytes, payload: bytes) -> bytes:
    crc = zlib.crc32(chunk_type)
    crc = zlib.crc32(payload, crc) & 0xFFFFFFFF
    return struct.pack(">I", len(payload)) + chunk_type + payload + struct.pack(">I", crc)


def _decode_png_8bit(path: Path):
    data = path.read_bytes()
    chunks = list(_png_chunks(data))

    ihdr = next((payload for kind, payload in chunks if kind == b"IHDR"), None)
    if ihdr is None or len(ihdr) != 13:
        raise PngCropError("PNG is missing a valid IHDR chunk.")

    width, height, bit_depth, color_type, compression, filter_method, interlace = struct.unpack(">IIBBBBB", ihdr)

    if bit_depth != 8:
        raise PngCropError(f"Only 8-bit PNGs are supported for auto-cropping (got {bit_depth}-bit).")

    if interlace != 0:
        raise PngCropError("Interlaced PNGs are not supported for auto-cropping. Export as non-interlaced PNG.")

    if compression != 0 or filter_method != 0:
        raise PngCropError("Unsupported PNG compression/filter method.")

    channels_by_type = {0: 1, 2: 3, 3: 1, 4: 2, 6: 4}
    if color_type not in channels_by_type:
        raise PngCropError(f"Unsupported PNG color type: {color_type}.")

    bpp = channels_by_type[color_type]
    row_bytes = width * bpp
    compressed = b"".join(payload for kind, payload in chunks if kind == b"IDAT")

    try:
        raw = zlib.decompress(compressed)
    except zlib.error as exc:
        raise PngCropError(f"Could not decompress PNG: {exc}") from exc

    expected = height * (row_bytes + 1)
    if len(raw) != expected:
        raise PngCropError(f"Unexpected PNG data size: expected {expected}, got {len(raw)}.")

    rows = []
    previous = bytearray(row_bytes)
    pos = 0

    for _ in range(height):
        filter_type = raw[pos]
        pos += 1
        encoded = raw[pos:pos + row_bytes]
        pos += row_bytes
        row = bytearray(row_bytes)

        if filter_type == 0:
            row[:] = encoded
        elif filter_type == 1:
            for i, value in enumerate(encoded):
                left = row[i - bpp] if i >= bpp else 0
                row[i] = (value + left) & 0xFF
        elif filter_type == 2:
            for i, value in enumerate(encoded):
                row[i] = (value + previous[i]) & 0xFF
        elif filter_type == 3:
            for i, value in enumerate(encoded):
                left = row[i - bpp] if i >= bpp else 0
                up = previous[i]
                row[i] = (value + ((left + up) >> 1)) & 0xFF
        elif filter_type == 4:
            for i, value in enumerate(encoded):
                left = row[i - bpp] if i >= bpp else 0
                up = previous[i]
                up_left = previous[i - bpp] if i >= bpp else 0
                row[i] = (value + _paeth_predictor(left, up, up_left)) & 0xFF
        else:
            raise PngCropError(f"Unsupported PNG row filter: {filter_type}.")

        rows.append(bytes(row))
        previous = row

    chunk_map = {}
    for kind, payload in chunks:
        chunk_map.setdefault(kind, []).append(payload)

    return width, height, color_type, bpp, rows, chunk_map



def _read_png_header(path: Path):
    with path.open("rb") as stream:
        header = stream.read(33)

    if len(header) < 33 or not header.startswith(PNG_SIGNATURE):
        raise PngCropError("Invalid PNG signature.")

    chunk_length = struct.unpack(">I", header[8:12])[0]
    chunk_type = header[12:16]

    if chunk_type != b"IHDR" or chunk_length != 13:
        raise PngCropError("PNG is missing a valid IHDR chunk.")

    return struct.unpack(">IIBBBBB", header[16:29])


def _analyze_png_crop_pillow(path: Path, padding: int) -> CropInfo:
    width, height, bit_depth, _color_type, compression, filter_method, interlace = _read_png_header(path)

    if bit_depth != 8:
        raise PngCropError(f"Only 8-bit PNGs are supported for auto-cropping (got {bit_depth}-bit).")

    if interlace != 0:
        raise PngCropError("Interlaced PNGs are not supported for auto-cropping. Export as non-interlaced PNG.")

    if compression != 0 or filter_method != 0:
        raise PngCropError("Unsupported PNG compression/filter method.")

    if width != MULTIPART_CANVAS_WIDTH or height != MULTIPART_CANVAS_HEIGHT:
        raise PngCropError(
            f"Multipart source PNG must be {MULTIPART_CANVAS_WIDTH}x{MULTIPART_CANVAS_HEIGHT}; "
            f"got {width}x{height}."
        )

    with PILImage.open(path) as image:
        image.load()

        if "A" in image.getbands():
            alpha = image.getchannel("A")
        elif image.mode == "P" and "transparency" in image.info:
            alpha = image.convert("RGBA").getchannel("A")
        else:
            # No alpha / transparency means the whole image is visible.
            alpha = None

        if alpha is None:
            bbox = (0, 0, width, height)
        else:
            bbox = alpha.getbbox()

    if bbox is None:
        raise PngCropError("PNG is fully transparent.")

    left, top, right, bottom = bbox

    x0 = max(0, left - padding)
    y0 = max(0, top - padding)
    x1 = min(width, right + padding)
    y1 = min(height, bottom + padding)

    return CropInfo(
        canvas_width=width,
        canvas_height=height,
        x=x0,
        y=y0,
        width=x1 - x0,
        height=y1 - y0,
    )


def _build_cropped_png_pillow(path: Path, crop: CropInfo) -> bytes:
    width, height, bit_depth, _color_type, compression, filter_method, interlace = _read_png_header(path)

    if bit_depth != 8:
        raise PngCropError(f"Only 8-bit PNGs are supported for auto-cropping (got {bit_depth}-bit).")

    if interlace != 0:
        raise PngCropError("Interlaced PNGs are not supported for auto-cropping. Export as non-interlaced PNG.")

    if compression != 0 or filter_method != 0:
        raise PngCropError("Unsupported PNG compression/filter method.")

    if width != crop.canvas_width or height != crop.canvas_height:
        raise PngCropError("Source PNG dimensions changed after crop analysis.")

    with PILImage.open(path) as image:
        image.load()
        cropped = image.crop(
            (
                crop.x,
                crop.y,
                crop.x + crop.width,
                crop.y + crop.height,
            )
        )

        output = io.BytesIO()
        cropped.save(
            output,
            format="PNG",
            optimize=False,
            compress_level=PNG_WRITE_COMPRESSION_LEVEL,
        )
        return output.getvalue()

def analyze_png_crop(path: Path, padding: int = MULTIPART_CROP_PADDING) -> CropInfo:
    if PILImage is not None:
        return _analyze_png_crop_pillow(path, padding)

    width, height, color_type, bpp, rows, chunk_map = _decode_png_8bit(path)

    if width != MULTIPART_CANVAS_WIDTH or height != MULTIPART_CANVAS_HEIGHT:
        raise PngCropError(
            f"Multipart source PNG must be {MULTIPART_CANVAS_WIDTH}x{MULTIPART_CANVAS_HEIGHT}; "
            f"got {width}x{height}."
        )

    transparent_palette = chunk_map.get(b"tRNS", [b""])[0]
    transparent_gray = None
    transparent_rgb = None

    if color_type == 0 and transparent_palette:
        transparent_gray = struct.unpack(">H", transparent_palette[:2])[0]
    elif color_type == 2 and len(transparent_palette) >= 6:
        transparent_rgb = struct.unpack(">HHH", transparent_palette[:6])

    min_x = width
    min_y = height
    max_x = -1
    max_y = -1

    for y, row in enumerate(rows):
        row_min = None
        row_max = None

        if color_type == 6:
            for x, alpha in enumerate(row[3::4]):
                if alpha:
                    if row_min is None:
                        row_min = x
                    row_max = x
        elif color_type == 4:
            for x, alpha in enumerate(row[1::2]):
                if alpha:
                    if row_min is None:
                        row_min = x
                    row_max = x
        elif color_type == 3:
            for x, palette_index in enumerate(row):
                alpha = transparent_palette[palette_index] if palette_index < len(transparent_palette) else 255
                if alpha:
                    if row_min is None:
                        row_min = x
                    row_max = x
        elif color_type == 2 and transparent_rgb is not None:
            tr, tg, tb = transparent_rgb
            for x in range(width):
                i = x * 3
                visible = not (row[i] == tr and row[i + 1] == tg and row[i + 2] == tb)
                if visible:
                    if row_min is None:
                        row_min = x
                    row_max = x
        elif color_type == 0 and transparent_gray is not None:
            for x, value in enumerate(row):
                if value != transparent_gray:
                    if row_min is None:
                        row_min = x
                    row_max = x
        else:
            row_min = 0
            row_max = width - 1

        if row_min is None:
            continue

        min_x = min(min_x, row_min)
        max_x = max(max_x, row_max)
        min_y = min(min_y, y)
        max_y = max(max_y, y)

    if max_x < 0 or max_y < 0:
        raise PngCropError("PNG is fully transparent.")

    x0 = max(0, min_x - padding)
    y0 = max(0, min_y - padding)
    x1 = min(width, max_x + 1 + padding)
    y1 = min(height, max_y + 1 + padding)

    return CropInfo(
        canvas_width=width,
        canvas_height=height,
        x=x0,
        y=y0,
        width=x1 - x0,
        height=y1 - y0,
    )


def build_cropped_png(path: Path, crop: CropInfo) -> bytes:
    if PILImage is not None:
        return _build_cropped_png_pillow(path, crop)

    width, height, color_type, bpp, rows, chunk_map = _decode_png_8bit(path)

    if width != crop.canvas_width or height != crop.canvas_height:
        raise PngCropError("Source PNG dimensions changed after crop analysis.")

    x0 = crop.x * bpp
    x1 = (crop.x + crop.width) * bpp
    raw_rows = bytearray()

    for y in range(crop.y, crop.y + crop.height):
        raw_rows.append(0)
        raw_rows.extend(rows[y][x0:x1])

    ihdr = struct.pack(
        ">IIBBBBB",
        crop.width,
        crop.height,
        8,
        color_type,
        0,
        0,
        0,
    )

    output = bytearray(PNG_SIGNATURE)
    output.extend(_png_chunk(b"IHDR", ihdr))

    if color_type == 3:
        for payload in chunk_map.get(b"PLTE", []):
            output.extend(_png_chunk(b"PLTE", payload))

    for payload in chunk_map.get(b"tRNS", []):
        output.extend(_png_chunk(b"tRNS", payload))

    output.extend(_png_chunk(b"IDAT", zlib.compress(bytes(raw_rows), level=PNG_WRITE_COMPRESSION_LEVEL)))
    output.extend(_png_chunk(b"IEND", b""))

    return bytes(output)


@dataclass
class MultipartPartData:
    texture: str
    filename: str
    part_key: str
    template_var: tk.StringVar
    variants: Dict[str, str] = field(default_factory=dict)


@dataclass
class MultipartPoseData:
    pose_id: str
    parts: List[MultipartPartData] = field(default_factory=list)
    source_pose_id: str = ""   # for shared/virtual poses only


@dataclass
class MultipartResourceData:
    resource_id: str
    name_var: tk.StringVar
    fixed_var: tk.BooleanVar
    compatible_bodies_var: Optional[tk.StringVar] = None
    poses: List[MultipartPoseData] = field(default_factory=list)


@dataclass
class EyeResourceData:
    resource_id: str
    name_var: tk.StringVar
    fixed_var: tk.BooleanVar
    texture_options: List[str]
    left_var: tk.StringVar
    right_var: tk.StringVar


@dataclass
class PubicHairPoseData:
    pose_id: str
    texture_options: List[str]
    texture_var: tk.StringVar


@dataclass
class PubicHairResourceData:
    resource_id: str
    name_var: tk.StringVar
    fixed_var: tk.BooleanVar
    poses: List[PubicHairPoseData] = field(default_factory=list)


class ScrollableFrame(ttk.Frame):
    def __init__(self, parent):
        super().__init__(parent)

        self.canvas = tk.Canvas(self, highlightthickness=0)
        self.scrollbar = ttk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
        self.inner = ttk.Frame(self.canvas)

        self.inner.bind(
            "<Configure>",
            lambda _event: self.canvas.configure(scrollregion=self.canvas.bbox("all")),
        )

        self.window_id = self.canvas.create_window((0, 0), window=self.inner, anchor="nw")
        self.canvas.configure(yscrollcommand=self.scrollbar.set)

        self.canvas.bind(
            "<Configure>",
            lambda event: self.canvas.itemconfigure(self.window_id, width=event.width),
        )

        self.canvas.pack(side="left", fill="both", expand=True)
        self.scrollbar.pack(side="right", fill="y")

        self.canvas.bind(
            "<Enter>",
            lambda _event: self.canvas.bind_all("<MouseWheel>", self._on_mousewheel),
        )
        self.canvas.bind(
            "<Leave>",
            lambda _event: self.canvas.unbind_all("<MouseWheel>"),
        )

    def _on_mousewheel(self, event):
        try:
            self.canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        except tk.TclError:
            pass



class OperationProgressDialog:
    def __init__(self, parent, title: str, total: int):
        self.parent = parent
        self.total = max(1, total)
        self.start_time = time.perf_counter()

        self.window = tk.Toplevel(parent)
        self.window.title(title)
        self.window.geometry("620x190")
        self.window.resizable(False, False)
        self.window.transient(parent)
        self.window.grab_set()
        self.window.protocol("WM_DELETE_WINDOW", lambda: None)

        frame = ttk.Frame(self.window, padding=16)
        frame.pack(fill="both", expand=True)

        self.phase_var = tk.StringVar(value=title)
        self.detail_var = tk.StringVar(value="")
        self.time_var = tk.StringVar(value="Starting...")

        ttk.Label(frame, textvariable=self.phase_var, font=("", 11, "bold")).pack(anchor="w")
        ttk.Label(frame, textvariable=self.detail_var).pack(anchor="w", pady=(8, 10))

        self.progress = ttk.Progressbar(
            frame,
            mode="determinate",
            maximum=self.total,
            value=0,
        )
        self.progress.pack(fill="x")

        ttk.Label(frame, textvariable=self.time_var).pack(anchor="w", pady=(10, 0))

        self._pump()

    @staticmethod
    def _format_seconds(seconds: float) -> str:
        seconds = max(0, int(round(seconds)))

        if seconds < 60:
            return f"{seconds}s"

        minutes, seconds = divmod(seconds, 60)

        if minutes < 60:
            return f"{minutes}m {seconds:02d}s"

        hours, minutes = divmod(minutes, 60)
        return f"{hours}h {minutes:02d}m"

    def update(self, completed: int, phase: str, detail: str = ""):
        completed = max(0, min(completed, self.total))
        self.progress.configure(value=completed)
        self.phase_var.set(phase)
        self.detail_var.set(detail)

        elapsed = time.perf_counter() - self.start_time
        percent = completed / self.total * 100.0

        if completed > 0:
            eta = elapsed / completed * (self.total - completed)
            self.time_var.set(
                f"{completed}/{self.total}  •  {percent:.0f}%  •  "
                f"Elapsed {self._format_seconds(elapsed)}  •  "
                f"ETA {self._format_seconds(eta)}"
            )
        else:
            self.time_var.set(f"0/{self.total}  •  0%")

        self._pump()

    def _pump(self):
        try:
            self.window.update_idletasks()
            self.window.update()
        except tk.TclError:
            pass

    def close(self):
        try:
            self.window.grab_release()
            self.window.destroy()
        except tk.TclError:
            pass


class ManifestHelperApp(tk.Tk):
    def __init__(self):
        super().__init__()

        self.title(APP_TITLE)
        self.geometry("1240x880")
        self.minsize(1020, 720)

        self.script_dir = Path(__file__).resolve().parent
        self.config_path = self.script_dir / CONFIG_FILE_NAME
        self.crop_cache_path = self.script_dir / CROP_CACHE_FILE_NAME

        self.root_path: Optional[Path] = None
        self.existing_manifest: Dict = {}
        self._crop_cache: Dict[str, Tuple[int, int, CropInfo]] = {}
        self._crop_cache_dirty = False

        self.eye_data: List[EyeResourceData] = []
        self.pubic_hair_data: List[PubicHairResourceData] = []

        self.multipart_data: Dict[str, List[MultipartResourceData]] = {
            category: [] for category in MULTIPART_CONFIG
        }

        self.template_library: Dict[str, List[str]] = {
            category: [] for category in MULTIPART_CONFIG
        }

        self._load_config()
        self._load_crop_cache()
        self._build_ui()
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    # ------------------------------------------------------------------
    # UI
    # ------------------------------------------------------------------

    def _build_ui(self):
        root = ttk.Frame(self, padding=10)
        root.pack(fill="both", expand=True)

        folder_frame = ttk.LabelFrame(root, text="Mod Folder", padding=8)
        folder_frame.pack(fill="x")

        self.folder_var = tk.StringVar()

        ttk.Entry(folder_frame, textvariable=self.folder_var).pack(
            side="left",
            fill="x",
            expand=True,
            padx=(0, 8),
        )

        ttk.Button(
            folder_frame,
            text="Browse...",
            command=self.choose_folder,
        ).pack(side="left")

        ttk.Button(
            folder_frame,
            text="Scan / Rescan",
            command=self.scan_folder,
        ).pack(side="left", padx=(8, 0))

        meta = ttk.LabelFrame(root, text="Manifest", padding=8)
        meta.pack(fill="x", pady=(10, 0))

        self.id_var = tk.StringVar()
        self.name_var = tk.StringVar()
        self.version_var = tk.StringVar(value="1.0")
        self.min_game_version_var = tk.StringVar(value="0.55")
        self.author_var = tk.StringVar()
        self.preview_var = tk.StringVar(value="preview.png")

        self._meta_row(meta, 0, "ID", self.id_var, ("Generate UUID", self.generate_uuid))
        self._meta_row(meta, 1, "Name", self.name_var)
        self._meta_row(meta, 2, "Version", self.version_var)
        self._meta_row(meta, 3, "Min game version", self.min_game_version_var)
        self._meta_row(meta, 4, "Author", self.author_var)
        self._meta_row(meta, 5, "Preview", self.preview_var, ("Browse", self.choose_preview))

        ttk.Label(meta, text="Description").grid(
            row=6,
            column=0,
            sticky="nw",
            padx=(0, 8),
            pady=3,
        )

        self.description_text = tk.Text(meta, height=3, wrap="word")
        self.description_text.grid(
            row=6,
            column=1,
            columnspan=2,
            sticky="ew",
            pady=3,
        )

        meta.columnconfigure(1, weight=1)

        toolbar = ttk.Frame(root)
        toolbar.pack(fill="x", pady=(10, 0))

        ttk.Button(
            toolbar,
            text="Manage Multipart Templates",
            command=self.manage_templates,
        ).pack(side="left")

        self.propagate_var = tk.BooleanVar(value=True)

        ttk.Checkbutton(
            toolbar,
            text="Propagate template to the same part across poses",
            variable=self.propagate_var,
        ).pack(side="left", padx=(12, 0))

        self.status_var = tk.StringVar(value="Choose a mod folder.")

        ttk.Label(
            toolbar,
            textvariable=self.status_var,
        ).pack(side="right")

        self.notebook = ttk.Notebook(root)
        self.notebook.pack(fill="both", expand=True, pady=(8, 0))

        self.category_frames: Dict[str, ScrollableFrame] = {}

        for category in TAB_ORDER:
            frame = ScrollableFrame(self.notebook)
            self.category_frames[category] = frame
            self.notebook.add(frame, text=category)

        footer = ttk.Frame(root)
        footer.pack(fill="x", pady=(10, 0))

        ttk.Button(
            footer,
            text="Validate",
            command=self.validate_with_popup,
        ).pack(side="left")

        ttk.Button(
            footer,
            text="Save mod.json",
            command=self.save_manifest,
        ).pack(side="left", padx=(8, 0))

        ttk.Button(
            footer,
            text="Build ZIP...",
            command=self.build_zip,
        ).pack(side="left", padx=(8, 0))

        ttk.Button(
            footer,
            text="Open Mod Folder",
            command=self.open_mod_folder,
        ).pack(side="right")

    def _meta_row(self, parent, row, label, variable, extra_button=None):
        ttk.Label(parent, text=label).grid(
            row=row,
            column=0,
            sticky="w",
            padx=(0, 8),
            pady=3,
        )

        ttk.Entry(parent, textvariable=variable).grid(
            row=row,
            column=1,
            sticky="ew",
            pady=3,
        )

        if extra_button:
            text, command = extra_button

            ttk.Button(
                parent,
                text=text,
                command=command,
            ).grid(
                row=row,
                column=2,
                sticky="w",
                padx=(8, 0),
                pady=3,
            )

    # ------------------------------------------------------------------
    # TEMPLATE CONFIG
    # ------------------------------------------------------------------

    def _load_config(self):
        if not self.config_path.exists():
            return

        try:
            data = json.loads(self.config_path.read_text(encoding="utf-8"))
            libraries = data.get("templates", {})

            for category in MULTIPART_CONFIG:
                values = libraries.get(category, [])

                if isinstance(values, list):
                    self.template_library[category] = sorted(
                        {
                            str(value).strip()
                            for value in values
                            if str(value).strip()
                        },
                        key=natural_key,
                    )
        except Exception:
            pass

    def _save_config(self):
        data = {
            "templates": {
                category: sorted(set(values), key=natural_key)
                for category, values in self.template_library.items()
            }
        }

        self.config_path.write_text(
            json.dumps(data, indent=2),
            encoding="utf-8",
        )


    def _load_crop_cache(self):
        if not self.crop_cache_path.exists():
            return

        try:
            raw = json.loads(self.crop_cache_path.read_text(encoding="utf-8"))

            if not isinstance(raw, dict):
                return

            for key, value in raw.items():
                if not isinstance(value, dict):
                    continue

                try:
                    crop = CropInfo(
                        canvas_width=int(value["canvasWidth"]),
                        canvas_height=int(value["canvasHeight"]),
                        x=int(value["x"]),
                        y=int(value["y"]),
                        width=int(value["width"]),
                        height=int(value["height"]),
                    )
                    self._crop_cache[str(key)] = (
                        int(value["mtimeNs"]),
                        int(value["size"]),
                        crop,
                    )
                except (KeyError, TypeError, ValueError):
                    continue
        except Exception:
            # Cache corruption must never prevent the helper from starting.
            self._crop_cache.clear()

    def _save_crop_cache(self):
        if not self._crop_cache_dirty:
            return

        data = {}

        for key, (mtime_ns, size, crop) in self._crop_cache.items():
            data[key] = {
                "mtimeNs": int(mtime_ns),
                "size": int(size),
                "canvasWidth": crop.canvas_width,
                "canvasHeight": crop.canvas_height,
                "x": crop.x,
                "y": crop.y,
                "width": crop.width,
                "height": crop.height,
            }

        try:
            self.crop_cache_path.write_text(
                json.dumps(data, separators=(",", ":")),
                encoding="utf-8",
            )
            self._crop_cache_dirty = False
        except OSError:
            # The in-memory cache still works even if the script directory is read-only.
            pass

    def _on_close(self):
        self._save_crop_cache()
        self.destroy()

    def manage_templates(self):
        window = tk.Toplevel(self)
        window.title("Multipart Template Library")
        window.geometry("680x620")
        window.transient(self)

        ttk.Label(
            window,
            text=(
                "One template name per line.\n"
                "Use the manifest template name only "
                "(for example HairFrontLong, not Hairs/HairFrontLong)."
            ),
            padding=10,
        ).pack(anchor="w")

        notebook = ttk.Notebook(window)
        notebook.pack(
            fill="both",
            expand=True,
            padx=10,
            pady=(0, 10),
        )

        editors = {}

        for category in MULTIPART_CONFIG:
            frame = ttk.Frame(notebook, padding=8)
            notebook.add(frame, text=category)

            text = tk.Text(frame, wrap="none")
            text.pack(fill="both", expand=True)
            text.insert("1.0", "\n".join(self.template_library[category]))

            editors[category] = text

        buttons = ttk.Frame(window, padding=10)
        buttons.pack(fill="x")

        def save_and_close():
            for category, editor in editors.items():
                lines = [
                    line.strip()
                    for line in editor.get("1.0", "end").splitlines()
                    if line.strip()
                ]

                self.template_library[category] = sorted(
                    set(lines),
                    key=natural_key,
                )

            self._save_config()
            self.render_all_categories()
            window.destroy()

        ttk.Button(
            buttons,
            text="Save",
            command=save_and_close,
        ).pack(side="right")

        ttk.Button(
            buttons,
            text="Cancel",
            command=window.destroy,
        ).pack(side="right", padx=(0, 8))

    # ------------------------------------------------------------------
    # ROOT FOLDER / MANIFEST
    # ------------------------------------------------------------------

    def choose_folder(self):
        selected = filedialog.askdirectory(
            title="Choose LAW mod root folder"
        )

        if not selected:
            return

        self.folder_var.set(selected)
        self.load_folder(Path(selected))

    def load_folder(self, path: Path):
        self.root_path = path.resolve()
        self.folder_var.set(str(self.root_path))

        self.existing_manifest = {}

        manifest_path = self.root_path / "mod.json"

        if manifest_path.exists():
            try:
                self.existing_manifest = json.loads(
                    manifest_path.read_text(encoding="utf-8")
                )
            except Exception as exc:
                messagebox.showerror(
                    APP_TITLE,
                    f"Could not read mod.json:\n{exc}",
                )

        self._load_manifest_metadata()
        self.scan_folder()

    def _load_manifest_metadata(self):
        manifest = self.existing_manifest

        if manifest:
            self.id_var.set(str(manifest.get("id", "")))
            self.name_var.set(str(manifest.get("name", "")))
            self.version_var.set(str(manifest.get("version", "1.0")))
            self.min_game_version_var.set(
                str(manifest.get("minGameVersion", "0.55"))
            )
            self.author_var.set(str(manifest.get("author", "")))
            self.preview_var.set(str(manifest.get("preview", "preview.png")))

            self.description_text.delete("1.0", "end")
            self.description_text.insert(
                "1.0",
                str(manifest.get("description", "")),
            )
        else:
            if self.root_path:
                self.name_var.set(self.root_path.name)

            self.description_text.delete("1.0", "end")

            if not self.id_var.get().strip():
                self.generate_uuid()

    def generate_uuid(self):
        self.id_var.set(str(uuid.uuid4()))

    def choose_preview(self):
        if not self.root_path:
            messagebox.showinfo(
                APP_TITLE,
                "Choose the mod root folder first.",
            )
            return

        selected = filedialog.askopenfilename(
            title="Choose preview PNG",
            initialdir=str(self.root_path),
            filetypes=[("PNG files", "*.png")],
        )

        if not selected:
            return

        try:
            relative = to_posix_relative(
                Path(selected),
                self.root_path,
            )
        except ValueError:
            messagebox.showerror(
                APP_TITLE,
                "The preview must be inside the mod folder.",
            )
            return

        self.preview_var.set(relative)

    def open_mod_folder(self):
        if not self.root_path:
            return

        try:
            os.startfile(self.root_path)
        except AttributeError:
            import subprocess
            subprocess.Popen(["xdg-open", str(self.root_path)])

    # ------------------------------------------------------------------
    # SCANNING
    # ------------------------------------------------------------------

    def _detect_folder(self, aliases: List[str]) -> Optional[Path]:
        if not self.root_path:
            return None

        for name in aliases:
            candidate = self.root_path / name

            if candidate.exists() and candidate.is_dir():
                return candidate

        return None

    def _detect_multipart_folder(self, category: str) -> Optional[Path]:
        return self._detect_folder(MULTIPART_CONFIG[category]["folders"])

    def scan_folder(self):
        if not self.folder_var.get().strip():
            messagebox.showinfo(APP_TITLE, "Choose a mod folder first.")
            return

        candidate = Path(self.folder_var.get()).resolve()

        if not candidate.exists() or not candidate.is_dir():
            messagebox.showerror(APP_TITLE, "The selected mod folder does not exist.")
            return

        self.root_path = candidate
        old_assignments = self._capture_current_multipart_assignments()
        existing_assignments = self._existing_multipart_assignments()

        self.eye_data = self._scan_eyes()
        self.pubic_hair_data = self._scan_pubic_hair()

        for category in MULTIPART_CONFIG:
            self.multipart_data[category] = self._scan_multipart_category(
                category,
                old_assignments,
                existing_assignments,
            )

        self._harvest_templates_from_existing_manifest()
        self.render_all_categories()

        eye_count = len(self.eye_data)
        pubic_count = len(self.pubic_hair_data)
        multipart_count = sum(len(resources) for resources in self.multipart_data.values())

        texture_count = (
            sum(len(resource.texture_options) for resource in self.eye_data)
            + sum(
                len(pose.texture_options)
                for resource in self.pubic_hair_data
                for pose in resource.poses
            )
            + sum(
                len(pose.parts)
                for resources in self.multipart_data.values()
                for resource in resources
                for pose in resource.poses
            )
        )

        self.status_var.set(
            f"{eye_count + pubic_count + multipart_count} resources / "
            f"{texture_count} texture entries found"
        )

    # ------------------------------------------------------------------
    # EYES
    # ------------------------------------------------------------------

    def _existing_eye_map(self) -> Dict[str, Dict]:
        result = {}
        content = self.existing_manifest.get("content", {}) if self.existing_manifest else {}
        resources = content.get("eyes", [])

        if not isinstance(resources, list):
            return result

        for resource in resources:
            if not isinstance(resource, dict):
                continue

            resource_id = str(resource.get("id", "")).strip()

            if resource_id:
                result[resource_id.casefold()] = resource

        return result

    def _scan_eyes(self) -> List[EyeResourceData]:
        folder = self._detect_folder(EYES_FOLDERS)

        if folder is None:
            return []

        existing = self._existing_eye_map()
        result: List[EyeResourceData] = []

        resource_dirs = sorted(
            [path for path in folder.iterdir() if path.is_dir()],
            key=lambda path: natural_key(path.name),
        )

        for resource_dir in resource_dirs:
            pngs = sorted(
                [path for path in resource_dir.rglob("*.png") if path.is_file()],
                key=lambda path: natural_key(str(path)),
            )

            if not pngs:
                continue

            resource_id = resource_dir.name
            old = existing.get(resource_id.casefold(), {})

            options = [to_posix_relative(path, self.root_path) for path in pngs]

            left = str(old.get("left", "")).strip()
            right = str(old.get("right", "")).strip()

            if left not in options:
                left = self._suggest_eye_side(pngs, options, "left")

            if right not in options:
                right = self._suggest_eye_side(pngs, options, "right")

            result.append(
                EyeResourceData(
                    resource_id=resource_id,
                    name_var=tk.StringVar(value=str(old.get("name", resource_id))),
                    fixed_var=tk.BooleanVar(value=bool(old.get("isFixedColor", False))),
                    texture_options=options,
                    left_var=tk.StringVar(value=left),
                    right_var=tk.StringVar(value=right),
                )
            )

        direct_pngs = sorted(folder.glob("*.png"), key=lambda path: natural_key(path.name))

        for png in direct_pngs:
            resource_id = png.stem

            if any(item.resource_id.casefold() == resource_id.casefold() for item in result):
                continue

            old = existing.get(resource_id.casefold(), {})
            relative = to_posix_relative(png, self.root_path)

            result.append(
                EyeResourceData(
                    resource_id=resource_id,
                    name_var=tk.StringVar(value=str(old.get("name", resource_id))),
                    fixed_var=tk.BooleanVar(value=bool(old.get("isFixedColor", False))),
                    texture_options=[relative],
                    left_var=tk.StringVar(value=relative),
                    right_var=tk.StringVar(value=relative),
                )
            )

        return sorted(result, key=lambda item: natural_key(item.resource_id))

    def _suggest_eye_side(self, pngs: List[Path], options: List[str], side: str) -> str:
        if not options:
            return ""

        if len(options) == 1:
            return options[0]

        matcher = looks_left if side == "left" else looks_right

        for index, png in enumerate(pngs):
            if matcher(png.stem):
                return options[index]

        return options[0] if side == "left" else (options[1] if len(options) > 1 else options[0])

    # ------------------------------------------------------------------
    # PUBIC HAIR
    # ------------------------------------------------------------------

    def _existing_pubic_hair_map(self) -> Dict[str, Dict]:
        result = {}
        content = self.existing_manifest.get("content", {}) if self.existing_manifest else {}
        resources = content.get("pubicHair", [])

        if not isinstance(resources, list):
            return result

        for resource in resources:
            if not isinstance(resource, dict):
                continue

            resource_id = str(resource.get("id", "")).strip()

            if resource_id:
                result[resource_id.casefold()] = resource

        return result

    def _existing_pubic_pose_texture(self, resource: Dict, pose_id: str) -> str:
        poses = resource.get("poses", [])

        if not isinstance(poses, list):
            return ""

        for pose in poses:
            if not isinstance(pose, dict):
                continue

            if str(pose.get("poseId", "")).casefold() == pose_id.casefold():
                return str(pose.get("texture", "")).strip()

        return ""

    def _scan_pubic_hair(self) -> List[PubicHairResourceData]:
        folder = self._detect_folder(PUBIC_HAIR_FOLDERS)

        if folder is None:
            return []

        existing = self._existing_pubic_hair_map()
        result: List[PubicHairResourceData] = []

        resource_dirs = sorted(
            [path for path in folder.iterdir() if path.is_dir()],
            key=lambda path: natural_key(path.name),
        )

        for resource_dir in resource_dirs:
            resource_id = resource_dir.name
            old = existing.get(resource_id.casefold(), {})

            resource = PubicHairResourceData(
                resource_id=resource_id,
                name_var=tk.StringVar(value=str(old.get("name", resource_id))),
                fixed_var=tk.BooleanVar(value=bool(old.get("isFixedColor", False))),
            )

            direct_pngs = sorted(resource_dir.glob("*.png"), key=lambda path: natural_key(path.name))

            for png in direct_pngs:
                pose_id = png.stem
                relative = to_posix_relative(png, self.root_path)
                existing_texture = self._existing_pubic_pose_texture(old, pose_id)
                selected = existing_texture if existing_texture == relative else relative

                resource.poses.append(
                    PubicHairPoseData(
                        pose_id=pose_id,
                        texture_options=[relative],
                        texture_var=tk.StringVar(value=selected),
                    )
                )

            pose_dirs = sorted(
                [path for path in resource_dir.iterdir() if path.is_dir()],
                key=lambda path: natural_key(path.name),
            )

            for pose_dir in pose_dirs:
                pngs = sorted(
                    [path for path in pose_dir.rglob("*.png") if path.is_file()],
                    key=lambda path: natural_key(str(path)),
                )

                if not pngs:
                    continue

                pose_id = pose_dir.name

                if any(pose.pose_id.casefold() == pose_id.casefold() for pose in resource.poses):
                    continue

                options = [to_posix_relative(path, self.root_path) for path in pngs]
                existing_texture = self._existing_pubic_pose_texture(old, pose_id)
                selected = existing_texture if existing_texture in options else options[0]

                resource.poses.append(
                    PubicHairPoseData(
                        pose_id=pose_id,
                        texture_options=options,
                        texture_var=tk.StringVar(value=selected),
                    )
                )

            resource.poses.sort(key=lambda pose: natural_key(pose.pose_id))

            if resource.poses:
                result.append(resource)

        direct_root_pngs = sorted(folder.glob("*.png"), key=lambda path: natural_key(path.name))

        for png in direct_root_pngs:
            resource_id = png.stem

            if any(item.resource_id.casefold() == resource_id.casefold() for item in result):
                continue

            old = existing.get(resource_id.casefold(), {})
            relative = to_posix_relative(png, self.root_path)

            result.append(
                PubicHairResourceData(
                    resource_id=resource_id,
                    name_var=tk.StringVar(value=str(old.get("name", resource_id))),
                    fixed_var=tk.BooleanVar(value=bool(old.get("isFixedColor", False))),
                    poses=[
                        PubicHairPoseData(
                            pose_id="Default",
                            texture_options=[relative],
                            texture_var=tk.StringVar(value=relative),
                        )
                    ],
                )
            )

        return sorted(result, key=lambda item: natural_key(item.resource_id))

    # ------------------------------------------------------------------
    # MULTIPART COSMETICS
    # ------------------------------------------------------------------

    def _existing_multipart_resource_map(self, category: str) -> Dict[str, Dict]:
        result = {}
        content = self.existing_manifest.get("content", {}) if self.existing_manifest else {}
        resources = content.get(MULTIPART_CONFIG[category]["manifest_key"], [])

        if not isinstance(resources, list):
            return result

        for resource in resources:
            if not isinstance(resource, dict):
                continue

            resource_id = str(resource.get("id", "")).strip()

            if resource_id:
                result[resource_id.casefold()] = resource

        return result

    def _scan_multipart_category(
        self,
        category: str,
        old_assignments: Dict[str, str],
        existing_assignments: Dict[str, str],
    ) -> List[MultipartResourceData]:
        folder = self._detect_multipart_folder(category)

        existing_resource_map = self._existing_multipart_resource_map(category)
        resources: List[MultipartResourceData] = []

        if folder is not None:
            resource_dirs = sorted(
                [path for path in folder.iterdir() if path.is_dir()],
                key=lambda path: natural_key(path.name),
            )

            for resource_dir in resource_dirs:
                resource_id = resource_dir.name

                if not any(path.is_file() for path in resource_dir.rglob("*.png")):
                    # Still allow an empty folder if the manifest already contains
                    # only shared poses that point to other pose folders inside that resource.
                    old_full = existing_resource_map.get(resource_id.casefold())
                    if not old_full:
                        continue

                meta_source = existing_resource_map.get(resource_id.casefold(), {})

                resource = MultipartResourceData(
                    resource_id=resource_id,
                    name_var=tk.StringVar(value=str(meta_source.get("name", resource_id))),
                    fixed_var=tk.BooleanVar(value=bool(meta_source.get("isFixedColor", False))),
                    compatible_bodies_var=(
                        tk.StringVar(value=format_compatible_bodies(meta_source.get("compatibleBodies", [])))
                        if category == "Head"
                        else None
                    ),
                )

                direct_pngs = sorted(resource_dir.glob("*.png"), key=lambda path: natural_key(path.name))

                if direct_pngs:
                    resource.poses.append(
                        self._build_multipart_pose(
                            category,
                            resource_id,
                            "Default",
                            direct_pngs,
                            old_assignments,
                            existing_assignments,
                        )
                    )

                pose_dirs = sorted(
                    [path for path in resource_dir.iterdir() if path.is_dir()],
                    key=lambda path: natural_key(path.name),
                )

                for pose_dir in pose_dirs:
                    pngs = sorted(
                        pose_dir.glob("*.png"),
                        key=lambda path: natural_key(path.name),
                    )

                    if not pngs:
                        continue

                    resource.poses.append(
                        self._build_multipart_pose(
                            category,
                            resource_id,
                            pose_dir.name,
                            pngs,
                            old_assignments,
                            existing_assignments,
                        )
                    )

                self._inject_manifest_only_shared_poses(resource, category)

                resource.poses.sort(key=lambda pose: natural_key(pose.pose_id))

                if resource.poses:
                    resources.append(resource)

        # Also include manifest-only resources if no folder was found or if a resource
        # exists only in the manifest.
        existing_ids = {resource.resource_id.casefold() for resource in resources}

        for resource_id_folded, old_full in existing_resource_map.items():
            if resource_id_folded in existing_ids:
                continue

            resource_id = str(old_full.get("id", "")).strip()
            if not resource_id:
                continue

            resource = MultipartResourceData(
                resource_id=resource_id,
                name_var=tk.StringVar(value=str(old_full.get("name", resource_id))),
                fixed_var=tk.BooleanVar(value=bool(old_full.get("isFixedColor", False))),
                compatible_bodies_var=(
                    tk.StringVar(value=format_compatible_bodies(old_full.get("compatibleBodies", [])))
                    if category == "Head"
                    else None
                ),
            )

            self._inject_manifest_only_shared_poses(resource, category)

            resource.poses.sort(key=lambda pose: natural_key(pose.pose_id))

            if resource.poses:
                resources.append(resource)

        return sorted(resources, key=lambda item: natural_key(item.resource_id))

    def _inject_manifest_only_shared_poses(self, resource: MultipartResourceData, category: str):
        """
        Keep poses that exist only in mod.json, including shared poses and
        Body / ClothTop parts that use size variants.
        """
        existing_resource_map = self._existing_multipart_resource_map(category)
        old_full = existing_resource_map.get(resource.resource_id.casefold())

        if not old_full:
            return

        old_poses = old_full.get("poses", [])
        if not isinstance(old_poses, list):
            return

        existing_pose_ids = {pose.pose_id.casefold() for pose in resource.poses}

        for old_pose in old_poses:
            if not isinstance(old_pose, dict):
                continue

            pose_id = str(old_pose.get("poseId", "")).strip()

            if not pose_id or pose_id.casefold() in existing_pose_ids:
                continue

            parts = old_pose.get("parts", [])

            if not isinstance(parts, list) or not parts:
                continue

            virtual_pose = MultipartPoseData(
                pose_id=pose_id,
                source_pose_id="(shared)",
            )

            for part in parts:
                if not isinstance(part, dict):
                    continue

                texture = str(part.get("texture", "")).strip()
                template = str(part.get("template", "")).strip()

                variants: Dict[str, str] = {}
                raw_variants = part.get("variants", [])

                if isinstance(raw_variants, list):
                    for variant in raw_variants:
                        if not isinstance(variant, dict):
                            continue

                        size = str(variant.get("size", "")).strip()
                        variant_texture = str(variant.get("texture", "")).strip()

                        canonical_size = next(
                            (
                                known
                                for known in MULTIPART_SIZE_VARIANTS
                                if known.casefold() == size.casefold()
                            ),
                            None,
                        )

                        if canonical_size and variant_texture:
                            variants[canonical_size] = variant_texture

                if not texture and not variants:
                    continue

                sample_texture = texture or next(iter(variants.values()))
                sample_stem = Path(sample_texture).stem

                logical_stem, _base_part_key, parsed_part_key, _size, _variation = parse_multipart_part_stem(
                    category,
                    sample_stem,
                    resource.resource_id,
                )

                # Existing manifests already contain the final template name.
                # Prefer it as the propagation key so variation suffixes remain
                # stable for manifest-only/shared poses.
                part_key = template or parsed_part_key

                if variants:
                    available = ", ".join(
                        size for size in MULTIPART_SIZE_VARIANTS if size in variants
                    )
                    filename = f"{logical_stem} [{available}]"
                else:
                    filename = Path(texture).name

                virtual_pose.parts.append(
                    MultipartPartData(
                        texture=texture,
                        filename=filename,
                        part_key=part_key,
                        template_var=tk.StringVar(value=template),
                        variants=variants,
                    )
                )

            if virtual_pose.parts:
                resource.poses.append(virtual_pose)
                existing_pose_ids.add(pose_id.casefold())

    def _build_multipart_pose(
        self,
        category: str,
        resource_id: str,
        pose_id: str,
        pngs: List[Path],
        old_assignments: Dict[str, str],
        existing_assignments: Dict[str, str],
    ) -> MultipartPoseData:
        pose = MultipartPoseData(pose_id=pose_id)

        # Body and ClothTop support body-size variants. Body additionally
        # supports visual variations using -Variation after the optional size:
        # BodyV1_Small-Turn.png -> logical part Body-Turn, size Small.
        if category in SIZE_VARIANT_CATEGORIES:
            grouped: Dict[str, Dict] = {}

            for png in pngs:
                relative = to_posix_relative(png, self.root_path)
                logical_stem, base_part_key, part_key, size, variation = parse_multipart_part_stem(
                    category,
                    png.stem,
                    resource_id,
                )
                key = part_key.casefold()

                if key not in grouped:
                    grouped[key] = {
                        "logical_stem": logical_stem,
                        "base_part_key": base_part_key,
                        "part_key": part_key,
                        "variation": variation,
                        "texture": "",
                        "variants": {},
                        "paths": [],
                    }

                grouped[key]["paths"].append(relative)

                if size is None:
                    grouped[key]["texture"] = relative
                else:
                    grouped[key]["variants"][size] = relative

            # Resolve normal/base templates first. Variation templates can then
            # derive automatically from the matching base template.
            resolved_base_templates: Dict[str, str] = {}

            ordered_groups = sorted(
                grouped.values(),
                key=lambda item: (
                    1 if item["variation"] else 0,
                    natural_key(item["base_part_key"]),
                    natural_key(item["variation"] or ""),
                ),
            )

            for group in ordered_groups:
                logical_stem = group["logical_stem"]
                base_part_key = group["base_part_key"]
                part_key = group["part_key"]
                variation = group["variation"]
                texture = group["texture"]
                variants = {
                    size: group["variants"][size]
                    for size in MULTIPART_SIZE_VARIANTS
                    if size in group["variants"]
                }

                assignment_paths = []
                if texture:
                    assignment_paths.append(texture)

                assignment_paths.extend(
                    variants[size]
                    for size in MULTIPART_SIZE_VARIANTS
                    if size in variants
                )

                template = ""

                for path in assignment_paths:
                    template = (
                        old_assignments.get(path)
                        or existing_assignments.get(path)
                        or ""
                    )

                    if template:
                        break

                if not template:
                    if variation:
                        base_template = resolved_base_templates.get(base_part_key.casefold(), "")

                        if not base_template:
                            base_template = (
                                self._suggest_template(
                                    category,
                                    logical_stem,
                                    base_part_key,
                                )
                                or base_part_key
                            )

                        logical_variation_template = base_template + "-" + variation

                        # Prefer an exact library entry when one exists, but do
                        # NOT collapse a variation back to its base template.
                        # Unity needs the variation suffix to decide when this
                        # multipart part should be displayed. If the dedicated
                        # Spine variation skin does not exist, Unity falls back
                        # to the base skin automatically.
                        template = (
                            self._suggest_template(
                                category,
                                logical_variation_template,
                                logical_variation_template,
                            )
                            or logical_variation_template
                        )
                    else:
                        template = (
                            self._suggest_template(
                                category,
                                logical_stem,
                                base_part_key,
                            )
                            or base_part_key
                        )

                if not variation and template:
                    resolved_base_templates[base_part_key.casefold()] = template

                display_stem = logical_stem
                if variation:
                    display_stem += "-" + variation

                if variants:
                    available = ", ".join(
                        size for size in MULTIPART_SIZE_VARIANTS if size in variants
                    )

                    if texture:
                        filename = f"{display_stem} [Default + {available}]"
                    else:
                        filename = f"{display_stem} [{available}]"
                else:
                    filename = Path(texture).name if texture else display_stem

                pose.parts.append(
                    MultipartPartData(
                        texture=texture,
                        filename=filename,
                        part_key=part_key,
                        template_var=tk.StringVar(value=template),
                        variants=variants,
                    )
                )

            return pose

        # Hair and ClothBottom keep the original one-file-per-part flow.
        for png in pngs:
            relative = to_posix_relative(png, self.root_path)
            stem = png.stem
            part_key = normalize_part_stem(stem, resource_id)

            template = (
                old_assignments.get(relative)
                or existing_assignments.get(relative)
                or self._suggest_template(category, stem, part_key)
                or ""
            )

            pose.parts.append(
                MultipartPartData(
                    texture=relative,
                    filename=png.name,
                    part_key=part_key,
                    template_var=tk.StringVar(value=template),
                )
            )

        return pose

    def _suggest_template(self, category: str, stem: str, part_key: str) -> str:
        templates = self.template_library.get(category, [])

        for template in templates:
            if template.casefold() == stem.casefold():
                return template

        candidates = [
            template
            for template in templates
            if template.casefold().startswith(part_key.casefold())
        ]

        if len(candidates) == 1:
            return candidates[0]

        return ""

    def _capture_current_multipart_assignments(self) -> Dict[str, str]:
        result = {}

        for resources in self.multipart_data.values():
            for resource in resources:
                for pose in resource.poses:
                    for part in pose.parts:
                        template = part.template_var.get().strip()

                        if not template:
                            continue

                        if part.texture:
                            result[part.texture] = template

                        for variant_texture in part.variants.values():
                            if variant_texture:
                                result[variant_texture] = template

        return result

    def _existing_multipart_assignments(self) -> Dict[str, str]:
        result = {}
        content = self.existing_manifest.get("content", {}) if self.existing_manifest else {}

        for category, cfg in MULTIPART_CONFIG.items():
            resources = content.get(cfg["manifest_key"], [])

            if not isinstance(resources, list):
                continue

            for resource in resources:
                if not isinstance(resource, dict):
                    continue

                for pose in resource.get("poses", []) or []:
                    if not isinstance(pose, dict):
                        continue

                    for part in pose.get("parts", []) or []:
                        if not isinstance(part, dict):
                            continue

                        template = str(part.get("template", "")).strip()

                        if not template:
                            continue

                        texture = str(part.get("texture", "")).strip()

                        if texture:
                            result[texture] = template

                        variants = part.get("variants", [])

                        if isinstance(variants, list):
                            for variant in variants:
                                if not isinstance(variant, dict):
                                    continue

                                variant_texture = str(
                                    variant.get("texture", "")
                                ).strip()

                                if variant_texture:
                                    result[variant_texture] = template

        return result

    def _harvest_templates_from_existing_manifest(self):
        changed = False
        content = self.existing_manifest.get("content", {}) if self.existing_manifest else {}

        for category, cfg in MULTIPART_CONFIG.items():
            resources = content.get(cfg["manifest_key"], [])

            if not isinstance(resources, list):
                continue

            current = set(self.template_library[category])

            for resource in resources:
                if not isinstance(resource, dict):
                    continue

                for pose in resource.get("poses", []) or []:
                    if not isinstance(pose, dict):
                        continue

                    for part in pose.get("parts", []) or []:
                        if not isinstance(part, dict):
                            continue

                        template = str(part.get("template", "")).strip()

                        if template and template not in current:
                            current.add(template)
                            changed = True

            self.template_library[category] = sorted(current, key=natural_key)

        if changed:
            self._save_config()

    # ------------------------------------------------------------------
    # SHARED POSE UI / LOGIC
    # ------------------------------------------------------------------

    def _copy_pose_parts(self, source_pose: MultipartPoseData) -> List[MultipartPartData]:
        copied_parts: List[MultipartPartData] = []

        for part in source_pose.parts:
            copied_parts.append(
                MultipartPartData(
                    texture=part.texture,
                    filename=part.filename,
                    part_key=part.part_key,
                    template_var=tk.StringVar(
                        value=part.template_var.get().strip()
                    ),
                    variants=dict(part.variants),
                )
            )

        return copied_parts

    def _add_shared_pose_dialog(self, category: str, resource: MultipartResourceData):
        if not resource.poses:
            messagebox.showinfo(APP_TITLE, "This resource has no source pose to copy from.")
            return

        window = tk.Toplevel(self)
        window.title(f"Add shared pose - {resource.resource_id}")
        window.geometry("430x180")
        window.transient(self)
        window.grab_set()

        content = ttk.Frame(window, padding=12)
        content.pack(fill="both", expand=True)

        ttk.Label(
            content,
            text="New pose ID",
        ).grid(row=0, column=0, sticky="w", pady=4, padx=(0, 8))

        new_pose_var = tk.StringVar()
        ttk.Entry(content, textvariable=new_pose_var).grid(
            row=0,
            column=1,
            sticky="ew",
            pady=4,
        )

        ttk.Label(
            content,
            text="Reuse files from pose",
        ).grid(row=1, column=0, sticky="w", pady=4, padx=(0, 8))

        source_choices = [pose.pose_id for pose in resource.poses]
        source_pose_var = tk.StringVar(value=source_choices[0])

        ttk.Combobox(
            content,
            textvariable=source_pose_var,
            values=source_choices,
            state="readonly",
        ).grid(
            row=1,
            column=1,
            sticky="ew",
            pady=4,
        )

        ttk.Label(
            content,
            text=(
                "This creates a manifest pose that reuses the exact same textures\n"
                "and current templates as the selected source pose. No new folders\n"
                "or PNG duplication are required."
            ),
        ).grid(row=2, column=0, columnspan=2, sticky="w", pady=(10, 4))

        content.columnconfigure(1, weight=1)

        buttons = ttk.Frame(window, padding=(12, 0, 12, 12))
        buttons.pack(fill="x")

        def confirm():
            new_pose_id = new_pose_var.get().strip()
            source_pose_id = source_pose_var.get().strip()

            if not new_pose_id:
                messagebox.showerror(APP_TITLE, "Pose ID is required.", parent=window)
                return

            if len(new_pose_id) > 128:
                messagebox.showerror(APP_TITLE, "Pose ID is too long.", parent=window)
                return

            if any(pose.pose_id.casefold() == new_pose_id.casefold() for pose in resource.poses):
                messagebox.showerror(APP_TITLE, f"Pose '{new_pose_id}' already exists.", parent=window)
                return

            source_pose = next((pose for pose in resource.poses if pose.pose_id == source_pose_id), None)

            if source_pose is None:
                messagebox.showerror(APP_TITLE, "Source pose not found.", parent=window)
                return

            new_pose = MultipartPoseData(
                pose_id=new_pose_id,
                parts=self._copy_pose_parts(source_pose),
                source_pose_id=source_pose.pose_id,
            )

            resource.poses.append(new_pose)
            resource.poses.sort(key=lambda pose: natural_key(pose.pose_id))
            self.render_multipart_category(category)

            window.destroy()

        ttk.Button(buttons, text="Cancel", command=window.destroy).pack(side="right")
        ttk.Button(buttons, text="Add shared pose", command=confirm).pack(side="right", padx=(0, 8))

    def _remove_shared_pose(self, category: str, resource: MultipartResourceData, pose: MultipartPoseData):
        if not pose.source_pose_id:
            messagebox.showinfo(APP_TITLE, "Only shared poses can be removed from the helper UI.")
            return

        if not messagebox.askyesno(
            APP_TITLE,
            f"Remove shared pose '{pose.pose_id}' from resource '{resource.resource_id}'?",
            parent=self,
        ):
            return

        resource.poses = [p for p in resource.poses if p is not pose]
        self.render_multipart_category(category)

    # ------------------------------------------------------------------
    # RENDER
    # ------------------------------------------------------------------

    def render_all_categories(self):
        self.render_eyes()
        self.render_pubic_hair()

        for category in MULTIPART_CONFIG:
            self.render_multipart_category(category)

    def _clear_category_frame(self, category: str):
        parent = self.category_frames[category].inner

        for child in parent.winfo_children():
            child.destroy()

        return parent

    def render_eyes(self):
        parent = self._clear_category_frame("Eyes")
        detected = self._detect_folder(EYES_FOLDERS)

        header = ttk.Frame(parent, padding=(4, 6))
        header.pack(fill="x")

        folder_text = (
            to_posix_relative(detected, self.root_path)
            if detected is not None and self.root_path is not None
            else "(folder not found)"
        )

        ttk.Label(header, text=f"Source folder: {folder_text}", font=("", 10, "bold")).pack(side="left")
        ttk.Label(header, text=f"{len(self.eye_data)} resource(s)").pack(side="right")

        if not self.eye_data:
            ttk.Label(parent, text="No eye PNG resources found.", padding=20).pack(anchor="w")
            return

        ttk.Label(
            parent,
            text=(
                "One PNG is automatically used for both eyes. "
                "With multiple PNGs, Left/Right are guessed from filenames "
                "and can be corrected below."
            ),
            padding=(8, 4),
        ).pack(anchor="w")

        for resource in self.eye_data:
            box = ttk.LabelFrame(parent, text=resource.resource_id, padding=8)
            box.pack(fill="x", padx=4, pady=5)

            props = ttk.Frame(box)
            props.pack(fill="x", pady=(0, 8))

            ttk.Label(props, text="Display name").pack(side="left")
            ttk.Entry(props, textvariable=resource.name_var, width=32).pack(side="left", padx=(6, 18))
            ttk.Checkbutton(props, text="Fixed color", variable=resource.fixed_var).pack(side="left")

            rows = ttk.Frame(box)
            rows.pack(fill="x")

            ttk.Label(rows, text="Left texture", width=16).grid(row=0, column=0, sticky="w", pady=2)
            ttk.Combobox(rows, textvariable=resource.left_var, values=resource.texture_options, state="readonly").grid(
                row=0, column=1, sticky="ew", pady=2
            )

            ttk.Label(rows, text="Right texture", width=16).grid(row=1, column=0, sticky="w", pady=2)
            ttk.Combobox(rows, textvariable=resource.right_var, values=resource.texture_options, state="readonly").grid(
                row=1, column=1, sticky="ew", pady=2
            )

            rows.columnconfigure(1, weight=1)

    def render_pubic_hair(self):
        parent = self._clear_category_frame("PubicHair")
        detected = self._detect_folder(PUBIC_HAIR_FOLDERS)

        header = ttk.Frame(parent, padding=(4, 6))
        header.pack(fill="x")

        folder_text = (
            to_posix_relative(detected, self.root_path)
            if detected is not None and self.root_path is not None
            else "(folder not found)"
        )

        ttk.Label(header, text=f"Source folder: {folder_text}", font=("", 10, "bold")).pack(side="left")
        ttk.Label(header, text=f"{len(self.pubic_hair_data)} resource(s)").pack(side="right")

        if not self.pubic_hair_data:
            ttk.Label(parent, text="No pubic hair PNG resources found.", padding=20).pack(anchor="w")
            return

        for resource in self.pubic_hair_data:
            box = ttk.LabelFrame(parent, text=resource.resource_id, padding=8)
            box.pack(fill="x", padx=4, pady=5)

            props = ttk.Frame(box)
            props.pack(fill="x", pady=(0, 6))

            ttk.Label(props, text="Display name").pack(side="left")
            ttk.Entry(props, textvariable=resource.name_var, width=32).pack(side="left", padx=(6, 18))
            ttk.Checkbutton(props, text="Fixed color", variable=resource.fixed_var).pack(side="left")

            rows = ttk.Frame(box)
            rows.pack(fill="x")

            for row_index, pose in enumerate(resource.poses):
                ttk.Label(rows, text=pose.pose_id, width=20, font=("", 9, "bold")).grid(
                    row=row_index, column=0, sticky="w", pady=2
                )

                if len(pose.texture_options) == 1:
                    ttk.Label(rows, text=pose.texture_options[0]).grid(
                        row=row_index, column=1, sticky="w", pady=2
                    )
                else:
                    ttk.Combobox(rows, textvariable=pose.texture_var, values=pose.texture_options, state="readonly").grid(
                        row=row_index, column=1, sticky="ew", pady=2
                    )

            rows.columnconfigure(1, weight=1)

    def render_multipart_category(self, category: str):
        parent = self._clear_category_frame(category)
        resources = self.multipart_data[category]
        detected = self._detect_multipart_folder(category)

        header = ttk.Frame(parent, padding=(4, 6))
        header.pack(fill="x")

        folder_text = (
            to_posix_relative(detected, self.root_path)
            if detected is not None and self.root_path is not None
            else "(folder not found)"
        )

        ttk.Label(header, text=f"Source folder: {folder_text}", font=("", 10, "bold")).pack(side="left")
        ttk.Label(header, text=f"{len(resources)} resource(s)").pack(side="right")

        if not resources:
            ttk.Label(parent, text="No PNG resources found in this category.", padding=20).pack(anchor="w")
            return

        ttk.Label(
            parent,
            text="You can add shared poses that reuse the textures of another pose without duplicating PNG files.",
            padding=(8, 2),
        ).pack(anchor="w")

        ttk.Label(
            parent,
            text=(
                f"Optimization: author multipart PNGs on {MULTIPART_CANVAS_WIDTH}x{MULTIPART_CANVAS_HEIGHT}. "
                f"Build ZIP crops visible pixels with {MULTIPART_CROP_PADDING}px transparent padding; source PNGs are never modified."
            ),
            padding=(8, 2),
        ).pack(anchor="w")

        if category == "Head":
            ttk.Label(
                parent,
                text=(
                    "Head compatibility: use official body keys such as V1/V2, a body resource ID "
                    "for a body in the same mod (for example PuppetBody), "
                    "OtherModId:BodyId for another mod, or * for every body."
                ),
                padding=(8, 2),
            ).pack(anchor="w")

        if category in SIZE_VARIANT_CATEGORIES:
            ttk.Label(
                parent,
                text=(
                    f"{category}: files ending in _Small, _Medium and _Big are "
                    "automatically grouped into one logical part. For Body this works on any part name "
                    "(Body, BoobRight, BoobLeft, etc.)."
                ),
                padding=(8, 2),
            ).pack(anchor="w")

        if category == "Body":
            ttk.Label(
                parent,
                text=(
                    "Body variations: append -Variation after the optional size, for example "
                    "BodyV1_Small-Turn.png. The generated logical template is Body-Turn. "
                    "Keep that variation suffix even when the variation reuses the base Spine mesh; "
                    "Unity will try Body_Small-Turn first and automatically fall back to Body_Small/Body."
                ),
                padding=(8, 2),
            ).pack(anchor="w")

        for resource in resources:
            box = ttk.LabelFrame(parent, text=resource.resource_id, padding=8)
            box.pack(fill="x", padx=4, pady=5)

            props = ttk.Frame(box)
            props.pack(fill="x", pady=(0, 6))

            ttk.Label(props, text="Display name").pack(side="left")
            ttk.Entry(props, textvariable=resource.name_var, width=28).pack(side="left", padx=(6, 14))
            ttk.Checkbutton(props, text="Fixed color", variable=resource.fixed_var).pack(side="left")

            if category == "Head" and resource.compatible_bodies_var is not None:
                compatibility = ttk.Frame(box)
                compatibility.pack(fill="x", pady=(0, 6))

                ttk.Label(compatibility, text="Compatible bodies").pack(side="left")
                ttk.Entry(
                    compatibility,
                    textvariable=resource.compatible_bodies_var,
                ).pack(side="left", fill="x", expand=True, padx=(6, 8))
                ttk.Label(
                    compatibility,
                    text="V1, V2, PuppetBody, OtherMod:BodyId, or *",
                ).pack(side="left")

            ttk.Button(
                props,
                text="Add shared pose",
                command=lambda c=category, r=resource: self._add_shared_pose_dialog(c, r),
            ).pack(side="right")

            for pose in resource.poses:
                pose_box = ttk.Frame(box)
                pose_box.pack(fill="x", pady=(5, 0))

                label_text = pose.pose_id
                if pose.source_pose_id:
                    if pose.source_pose_id == "(shared)":
                        label_text += "  [shared pose]"
                    else:
                        label_text += f"  [shared from {pose.source_pose_id}]"

                ttk.Label(
                    pose_box,
                    text=label_text,
                    width=28,
                    font=("", 9, "bold"),
                ).grid(row=0, column=0, sticky="nw", padx=(0, 8))

                rows = ttk.Frame(pose_box)
                rows.grid(row=0, column=1, sticky="ew")
                pose_box.columnconfigure(1, weight=1)

                if pose.source_pose_id:
                    ttk.Button(
                        pose_box,
                        text="Remove",
                        command=lambda c=category, r=resource, p=pose: self._remove_shared_pose(c, r, p),
                    ).grid(row=0, column=2, sticky="ne", padx=(8, 0))

                for row_index, part in enumerate(pose.parts):
                    ttk.Label(rows, text=part.filename, width=42).grid(
                        row=row_index, column=0, sticky="w", pady=2
                    )

                    ttk.Label(rows, text="Template").grid(
                        row=row_index, column=1, sticky="e", padx=(8, 5)
                    )

                    combo = ttk.Combobox(
                        rows,
                        textvariable=part.template_var,
                        values=self.template_library.get(category, []),
                        width=32,
                        state="normal",
                    )
                    combo.grid(row=row_index, column=2, sticky="ew", pady=2)
                    rows.columnconfigure(2, weight=1)

                    combo.bind(
                        "<<ComboboxSelected>>",
                        lambda _event, c=category, r=resource, p=part: self._template_changed(c, r, p),
                    )

                    combo.bind(
                        "<FocusOut>",
                        lambda _event, c=category, r=resource, p=part: self._template_changed(c, r, p),
                    )

    def _template_changed(self, category: str, resource: MultipartResourceData, changed_part: MultipartPartData):
        template = changed_part.template_var.get().strip()

        if not template:
            return

        if template not in self.template_library[category]:
            self.template_library[category].append(template)
            self.template_library[category] = sorted(
                set(self.template_library[category]),
                key=natural_key,
            )
            self._save_config()

        if not self.propagate_var.get():
            return

        for pose in resource.poses:
            for part in pose.parts:
                if part is changed_part:
                    continue

                if part.part_key.casefold() == changed_part.part_key.casefold():
                    part.template_var.set(template)

    def _get_crop_info(self, texture: str) -> CropInfo:
        if not self.root_path:
            raise PngCropError("No mod folder selected.")

        path = (self.root_path / Path(texture)).resolve()
        stat = path.stat()
        key = str(path)
        cached = self._crop_cache.get(key)

        if cached and cached[0] == stat.st_mtime_ns and cached[1] == stat.st_size:
            return cached[2]

        crop = analyze_png_crop(path, MULTIPART_CROP_PADDING)
        self._crop_cache[key] = (stat.st_mtime_ns, stat.st_size, crop)
        self._crop_cache_dirty = True
        return crop


    def _is_crop_info_cached(self, texture: str) -> bool:
        if not self.root_path or not texture:
            return False

        try:
            path = (self.root_path / Path(texture)).resolve()
            stat = path.stat()
        except OSError:
            return False

        cached = self._crop_cache.get(str(path))

        return bool(
            cached and
            cached[0] == stat.st_mtime_ns and
            cached[1] == stat.st_size
        )

    def _collect_multipart_texture_paths(self) -> List[str]:
        result = []
        seen = set()

        for resources in self.multipart_data.values():
            for resource in resources:
                for pose in resource.poses:
                    for part in pose.parts:
                        candidates = []

                        if part.texture:
                            candidates.append(part.texture)

                        candidates.extend(part.variants.values())

                        for texture in candidates:
                            if not texture:
                                continue

                            key = texture.casefold()

                            if key in seen:
                                continue

                            seen.add(key)
                            result.append(texture)

        return sorted(result, key=natural_key)

    def _warm_crop_cache_with_progress(self, title: str):
        textures = self._collect_multipart_texture_paths()

        pending = [
            texture
            for texture in textures
            if not self._is_crop_info_cached(texture)
        ]

        if not pending:
            return

        dialog = OperationProgressDialog(self, title, len(pending))

        try:
            engine = "Pillow fast PNG engine" if PILImage is not None else "built-in PNG engine"

            for index, texture in enumerate(pending):
                dialog.update(
                    index,
                    f"{title} — {engine}",
                    Path(texture).name,
                )

                try:
                    self._get_crop_info(texture)
                except (OSError, PngCropError):
                    # Validation will report the exact error afterwards.
                    pass

                dialog.update(
                    index + 1,
                    f"{title} — {engine}",
                    Path(texture).name,
                )
        finally:
            dialog.close()
            self._save_crop_cache()


    def _try_get_crop_info(self, texture: str) -> Optional[CropInfo]:
        try:
            return self._get_crop_info(texture)
        except (OSError, PngCropError):
            return None

    @staticmethod
    def _apply_crop_fields(target: Dict, crop: Optional[CropInfo]):
        if crop is None:
            return

        target["canvasWidth"] = crop.canvas_width
        target["canvasHeight"] = crop.canvas_height
        target["cropX"] = crop.x
        target["cropY"] = crop.y
        target["cropWidth"] = crop.width
        target["cropHeight"] = crop.height

    def _collect_multipart_crop_infos(self) -> Dict[str, CropInfo]:
        result: Dict[str, CropInfo] = {}

        for resources in self.multipart_data.values():
            for resource in resources:
                for pose in resource.poses:
                    for part in pose.parts:
                        paths = []
                        if part.texture:
                            paths.append(part.texture)
                        paths.extend(part.variants.values())

                        for texture in paths:
                            if texture and texture not in result:
                                result[texture] = self._get_crop_info(texture)

        return result

    @staticmethod
    def _format_mib(value: int) -> str:
        return f"{value / (1024 * 1024):.1f} MiB"

    def _optimization_summary(self, crop_infos: Dict[str, CropInfo]) -> str:
        if not crop_infos:
            return ""

        before = sum(info.canvas_width * info.canvas_height * 4 for info in crop_infos.values())
        after = sum(info.runtime_bytes_rgba32 for info in crop_infos.values())
        saved = before - after
        percent = (saved / before * 100.0) if before else 0.0

        return (
            f"Multipart runtime texture estimate: {self._format_mib(before)} -> "
            f"{self._format_mib(after)} ({percent:.1f}% smaller)"
        )

    # ------------------------------------------------------------------
    # MANIFEST BUILD
    # ------------------------------------------------------------------

    def build_manifest(self) -> Dict:
        manifest = dict(self.existing_manifest) if isinstance(self.existing_manifest, dict) else {}
        old_content = manifest.get("content", {})
        content = dict(old_content) if isinstance(old_content, dict) else {}

        manifest["formatVersion"] = FORMAT_VERSION
        manifest["id"] = self.id_var.get().strip()
        manifest["name"] = self.name_var.get().strip()
        manifest["version"] = self.version_var.get().strip()
        manifest["minGameVersion"] = self.min_game_version_var.get().strip()
        manifest["author"] = self.author_var.get().strip()
        manifest["description"] = self.description_text.get("1.0", "end").strip()
        manifest["preview"] = self.preview_var.get().strip()

        eyes_json = []

        for resource in self.eye_data:
            eyes_json.append(
                {
                    "id": resource.resource_id,
                    "name": resource.name_var.get().strip() or resource.resource_id,
                    "isFixedColor": bool(resource.fixed_var.get()),
                    "left": resource.left_var.get().strip(),
                    "right": resource.right_var.get().strip(),
                }
            )

        content["eyes"] = eyes_json

        pubic_json = []

        for resource in self.pubic_hair_data:
            poses_json = []

            for pose in resource.poses:
                poses_json.append(
                    {
                        "poseId": pose.pose_id,
                        "texture": pose.texture_var.get().strip(),
                    }
                )

            pubic_json.append(
                {
                    "id": resource.resource_id,
                    "name": resource.name_var.get().strip() or resource.resource_id,
                    "isFixedColor": bool(resource.fixed_var.get()),
                    "poses": poses_json,
                }
            )

        content["pubicHair"] = pubic_json

        for category, cfg in MULTIPART_CONFIG.items():
            resources_json = []

            for resource in self.multipart_data[category]:
                poses_json = []

                for pose in resource.poses:
                    parts_json = []

                    for part in pose.parts:
                        part_json = {
                            "template": part.template_var.get().strip(),
                        }

                        if part.texture:
                            part_json["texture"] = part.texture
                            self._apply_crop_fields(
                                part_json,
                                self._try_get_crop_info(part.texture),
                            )

                        if part.variants:
                            variants_json = []

                            for size in MULTIPART_SIZE_VARIANTS:
                                if size not in part.variants:
                                    continue

                                variant_json = {
                                    "size": size,
                                    "texture": part.variants[size],
                                }

                                self._apply_crop_fields(
                                    variant_json,
                                    self._try_get_crop_info(part.variants[size]),
                                )

                                variants_json.append(variant_json)

                            part_json["variants"] = variants_json

                        parts_json.append(part_json)

                    poses_json.append(
                        {
                            "poseId": pose.pose_id,
                            "parts": parts_json,
                        }
                    )

                resource_json = {
                    "id": resource.resource_id,
                    "name": resource.name_var.get().strip() or resource.resource_id,
                    "isFixedColor": bool(resource.fixed_var.get()),
                    "poses": poses_json,
                }

                if category == "Head":
                    compatible_text = (
                        resource.compatible_bodies_var.get()
                        if resource.compatible_bodies_var is not None
                        else ""
                    )
                    resource_json["compatibleBodies"] = parse_compatible_bodies_text(compatible_text)

                resources_json.append(resource_json)

            content[cfg["manifest_key"]] = resources_json

        manifest["content"] = content
        return manifest

    # ------------------------------------------------------------------
    # VALIDATION
    # ------------------------------------------------------------------

    def validate_manifest(self) -> Tuple[bool, List[str], List[str]]:
        errors: List[str] = []
        warnings: List[str] = []

        if not self.root_path:
            return False, ["No mod folder selected."], warnings

        manifest = self.build_manifest()
        mod_id = manifest.get("id", "")

        if not valid_id(mod_id):
            errors.append(
                "Manifest ID must be 1-64 ASCII letters/numbers/._- and may not start with '.'."
            )

        if not manifest.get("name"):
            errors.append("Name is required.")

        if not manifest.get("author"):
            errors.append("Author is required.")

        if not VERSION_RE.fullmatch(manifest.get("version", "")):
            errors.append("Version must look like 1.0, 1.0.0, etc.")

        if not VERSION_RE.fullmatch(manifest.get("minGameVersion", "")):
            errors.append("Minimum game version must look like 0.55, 1.0, etc.")

        preview = manifest.get("preview", "")

        if not preview:
            errors.append("Preview path is required.")
        else:
            preview_path = self.root_path / Path(preview)

            if not preview_path.exists():
                errors.append(f"Preview file does not exist: {preview}")
            elif preview_path.suffix.casefold() != ".png":
                errors.append("Preview must be a PNG.")

        total_resources = 0

        # Eyes
        seen_eye_ids = set()

        for resource in self.eye_data:
            total_resources += 1
            self._validate_resource_id("Eyes", resource.resource_id, seen_eye_ids, errors)

            left = resource.left_var.get().strip()
            right = resource.right_var.get().strip()

            if not left:
                errors.append(f"Eyes/{resource.resource_id}: left texture is missing.")
            else:
                self._validate_texture_path(left, errors)

            if not right:
                errors.append(f"Eyes/{resource.resource_id}: right texture is missing.")
            else:
                self._validate_texture_path(right, errors)

        # Pubic hair
        seen_pubic_ids = set()

        for resource in self.pubic_hair_data:
            total_resources += 1
            self._validate_resource_id("PubicHair", resource.resource_id, seen_pubic_ids, errors)

            if not resource.poses:
                errors.append(f"PubicHair/{resource.resource_id}: no poses found.")

            seen_poses = set()

            for pose in resource.poses:
                pose_key = pose.pose_id.casefold()

                if not pose.pose_id.strip() or len(pose.pose_id) > 128:
                    errors.append(f"PubicHair/{resource.resource_id}: invalid pose '{pose.pose_id}'.")

                if pose_key in seen_poses:
                    errors.append(f"PubicHair/{resource.resource_id}: duplicate pose '{pose.pose_id}'.")

                seen_poses.add(pose_key)

                texture = pose.texture_var.get().strip()

                if not texture:
                    errors.append(f"PubicHair/{resource.resource_id}/{pose.pose_id}: texture is missing.")
                else:
                    self._validate_texture_path(texture, errors)

        # Multipart
        for category, resources in self.multipart_data.items():
            seen_ids = set()

            for resource in resources:
                total_resources += 1
                self._validate_resource_id(category, resource.resource_id, seen_ids, errors)

                if category == "Head":
                    compatible_text = (
                        resource.compatible_bodies_var.get()
                        if resource.compatible_bodies_var is not None
                        else ""
                    )
                    compatible_bodies = parse_compatible_bodies_text(compatible_text)

                    if not compatible_bodies:
                        errors.append(
                            f"Head/{resource.resource_id}: compatibleBodies must contain at least one body or '*'."
                        )
                    else:
                        for body_ref in compatible_bodies:
                            if not valid_compatible_body(body_ref):
                                errors.append(
                                    f"Head/{resource.resource_id}: invalid compatible body '{body_ref}'. "
                                    "Use V1/V2, SameModBodyId, OtherModId:BodyId, or *."
                                )

                        if "*" in compatible_bodies and len(compatible_bodies) > 1:
                            warnings.append(
                                f"Head/{resource.resource_id}: '*' already matches every body; other compatibleBodies entries are redundant."
                            )

                seen_poses = set()

                for pose in resource.poses:
                    pose_key = pose.pose_id.casefold()

                    if not pose.pose_id.strip() or len(pose.pose_id) > 128:
                        errors.append(f"{category}/{resource.resource_id}: invalid pose '{pose.pose_id}'.")

                    if pose_key in seen_poses:
                        errors.append(f"{category}/{resource.resource_id}: duplicate pose '{pose.pose_id}'.")

                    seen_poses.add(pose_key)

                    seen_templates = set()

                    for part in pose.parts:
                        template = part.template_var.get().strip()

                        if not template:
                            errors.append(
                                f"{category}/{resource.resource_id}/{pose.pose_id}/{part.filename}: template is not selected."
                            )
                            continue

                        if not valid_id(template):
                            errors.append(
                                f"{category}/{resource.resource_id}/{pose.pose_id}/{part.filename}: invalid template '{template}'."
                            )

                        template_key = template.casefold()

                        if template_key in seen_templates:
                            errors.append(
                                f"{category}/{resource.resource_id}/{pose.pose_id}: template '{template}' is used more than once."
                            )

                        seen_templates.add(template_key)

                        if part.texture:
                            self._validate_texture_path(part.texture, errors)
                            self._validate_multipart_crop(part.texture, errors)

                        if part.variants:
                            for size in MULTIPART_SIZE_VARIANTS:
                                variant_texture = part.variants.get(size)

                                if variant_texture:
                                    self._validate_texture_path(
                                        variant_texture,
                                        errors,
                                    )
                                    self._validate_multipart_crop(variant_texture, errors)

                        if not part.texture and not part.variants:
                            errors.append(
                                f"{category}/{resource.resource_id}/"
                                f"{pose.pose_id}/{part.filename}: "
                                "part has no texture or size variants."
                            )

        if total_resources == 0:
            errors.append("No supported cosmetic resources were found.")

        return not errors, errors, warnings

    def _validate_resource_id(self, category: str, resource_id: str, seen_ids: set, errors: List[str]):
        if not valid_id(resource_id):
            errors.append(f"{category}: invalid resource ID '{resource_id}'. Rename the resource folder.")

        folded = resource_id.casefold()

        if folded in seen_ids:
            errors.append(f"{category}: duplicate resource ID '{resource_id}'.")

        seen_ids.add(folded)

    def _validate_multipart_crop(self, texture: str, errors: List[str]):
        if not texture or not self.root_path:
            return

        texture_path = self.root_path / Path(texture)
        if not texture_path.exists():
            return

        try:
            self._get_crop_info(texture)
        except (OSError, PngCropError) as exc:
            errors.append(f"Cannot auto-crop multipart texture {texture}: {exc}")

    def _validate_texture_path(self, texture: str, errors: List[str]):
        if not texture:
            errors.append("Empty texture path.")
            return

        texture_path = self.root_path / Path(texture)

        try:
            texture_path.resolve().relative_to(self.root_path.resolve())
        except ValueError:
            errors.append(f"Texture is outside the mod folder: {texture}")
            return

        if not texture_path.exists():
            errors.append(f"Missing texture: {texture}")
        elif texture_path.suffix.casefold() != ".png":
            errors.append(f"Texture is not PNG: {texture}")

    def validate_with_popup(self):
        self._warm_crop_cache_with_progress("Validating multipart textures")
        ok, errors, warnings = self.validate_manifest()

        if ok:
            text = "Manifest is valid."

            if warnings:
                text += "\n\nWarnings:\n- " + "\n- ".join(warnings)

            messagebox.showinfo(APP_TITLE, text)
        else:
            text = "Fix these errors:\n\n- " + "\n- ".join(errors)

            if warnings:
                text += "\n\nWarnings:\n- " + "\n- ".join(warnings)

            messagebox.showerror(APP_TITLE, text)

    # ------------------------------------------------------------------
    # SAVE / ZIP
    # ------------------------------------------------------------------

    def save_manifest(self):
        if not self.root_path:
            messagebox.showinfo(APP_TITLE, "Choose a mod folder first.")
            return

        self._warm_crop_cache_with_progress("Preparing multipart textures")
        ok, errors, warnings = self.validate_manifest()

        if not ok:
            messagebox.showerror(APP_TITLE, "mod.json was not saved.\n\n- " + "\n- ".join(errors))
            return

        manifest = self.build_manifest()
        path = self.root_path / "mod.json"

        if path.exists():
            shutil.copy2(path, self.root_path / "mod.json.bak")

        path.write_text(
            json.dumps(manifest, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )

        self.existing_manifest = manifest
        self._remember_used_templates()
        self._save_config()

        text = f"Saved:\n{path}"

        if warnings:
            text += "\n\nWarnings:\n- " + "\n- ".join(warnings)

        messagebox.showinfo(APP_TITLE, text)

    def _remember_used_templates(self):
        for category, resources in self.multipart_data.items():
            current = set(self.template_library[category])

            for resource in resources:
                for pose in resource.poses:
                    for part in pose.parts:
                        template = part.template_var.get().strip()

                        if template:
                            current.add(template)

            self.template_library[category] = sorted(current, key=natural_key)

    def build_zip(self):
        if not self.root_path:
            messagebox.showinfo(APP_TITLE, "Choose a mod folder first.")
            return

        self._warm_crop_cache_with_progress("Preparing multipart textures")
        ok, errors, warnings = self.validate_manifest()

        if not ok:
            messagebox.showerror(APP_TITLE, "ZIP was not created.\n\n- " + "\n- ".join(errors))
            return

        manifest = self.build_manifest()
        manifest_path = self.root_path / "mod.json"

        if manifest_path.exists():
            shutil.copy2(manifest_path, self.root_path / "mod.json.bak")

        manifest_path.write_text(
            json.dumps(manifest, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )

        self.existing_manifest = manifest

        safe_name = (
            manifest["name"]
            .replace("/", "_")
            .replace("\\", "_")
            .replace(" ", "_")
        )

        default_name = f"{safe_name}_{manifest['version']}.zip"

        output = filedialog.asksaveasfilename(
            title="Build LAW Mod ZIP",
            defaultextension=".zip",
            initialfile=default_name,
            filetypes=[("ZIP files", "*.zip")],
        )

        if not output:
            return

        output_path = Path(output).resolve()

        try:
            crop_infos = self._collect_multipart_crop_infos()

            files_to_pack = []

            for file_path in sorted(
                self.root_path.rglob("*"),
                key=lambda path: natural_key(str(path)),
            ):
                if not file_path.is_file():
                    continue

                if file_path.name in {"mod.json.bak", CONFIG_FILE_NAME, CROP_CACHE_FILE_NAME}:
                    continue

                if file_path.resolve() == output_path:
                    continue

                if file_path.suffix.casefold() not in {".png", ".json", ".txt"}:
                    continue

                files_to_pack.append(file_path)

            dialog = OperationProgressDialog(
                self,
                "Building ZIP",
                len(files_to_pack),
            )

            try:
                with zipfile.ZipFile(
                    output_path,
                    "w",
                    compression=zipfile.ZIP_DEFLATED,
                    compresslevel=6,
                ) as archive:
                    for index, file_path in enumerate(files_to_pack):
                        relative = to_posix_relative(file_path, self.root_path)

                        if relative in crop_infos:
                            phase = "Cropping + packing multipart PNGs"
                        else:
                            phase = "Packing mod files"

                        dialog.update(index, phase, relative)

                        if relative in crop_infos:
                            optimized_png = build_cropped_png(
                                file_path,
                                crop_infos[relative],
                            )

                            # PNG already contains its own DEFLATE stream. Storing it
                            # avoids wasting time compressing compressed data again.
                            archive.writestr(
                                relative,
                                optimized_png,
                                compress_type=zipfile.ZIP_STORED,
                            )
                        elif file_path.suffix.casefold() == ".png":
                            archive.write(
                                file_path,
                                relative,
                                compress_type=zipfile.ZIP_STORED,
                            )
                        else:
                            archive.write(
                                file_path,
                                relative,
                                compress_type=zipfile.ZIP_DEFLATED,
                            )

                        dialog.update(index + 1, phase, relative)
            finally:
                dialog.close()

            self._save_crop_cache()

            text = f"ZIP created:\n{output_path}"
            summary = self._optimization_summary(crop_infos)

            if summary:
                text += "\n\n" + summary

            if warnings:
                text += "\n\nWarnings:\n- " + "\n- ".join(warnings)

            messagebox.showinfo(APP_TITLE, text)
        except Exception as exc:
            messagebox.showerror(APP_TITLE, f"Could not create ZIP:\n{exc}")


def main():
    app = ManifestHelperApp()
    app.mainloop()


if __name__ == "__main__":
    main()
