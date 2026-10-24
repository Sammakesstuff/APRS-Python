

import json
import math
import os
import queue
import threading
import time
import tkinter as tk
import urllib.error
import urllib.parse
import urllib.request
from io import BytesIO
from tkinter import messagebox, ttk

try:
    from PIL import Image, ImageTk
    PIL_AVAILABLE = True
except ImportError:
    PIL_AVAILABLE = False

CONFIG_PATH = os.path.join(os.path.expanduser("~"), ".aprs_tracker_config.json")
TILE_CACHE_DIR = os.path.join(os.path.expanduser("~"), ".aprs_tracker_tiles")
API_URL = "https://api.aprs.fi/api/get"
USER_AGENT = "aprs-tracker-tk/1.1"
TILE_SIZE = 256

TILE_SOURCES = {
    "Street (OpenStreetMap)": (
        "https://tile.openstreetmap.org/{z}/{x}/{y}.png",
        "png", False, 19, "(c) OpenStreetMap contributors",
    ),
    "Satellite (Esri World Imagery)": (
        "https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}",
        "jpg", True, 19, "Esri, Maxar, Earthstar Geographics",
    ),
    "Topographic (OpenTopoMap)": (
        "https://tile.opentopomap.org/{z}/{x}/{y}.png",
        "png", False, 17, "(c) OpenTopoMap (CC-BY-SA), SRTM",
    ),
}


SYMBOL_CELL = 24
SYMBOL_GRID_COLS = 16
SYMBOL_SHEET_URLS = {
    "/": "https://raw.githubusercontent.com/hessu/aprs-symbols/master/png/aprs-symbols-24-0.png",
    "\\": "https://raw.githubusercontent.com/hessu/aprs-symbols/master/png/aprs-symbols-24-1.png",
}


# -----------------------
def load_config():
    if os.path.exists(CONFIG_PATH):
        try:
            with open(CONFIG_PATH, "r") as f:
                return json.load(f)
        except (json.JSONDecodeError, OSError):
            pass
    return {}


def save_config(data):
    try:
        with open(CONFIG_PATH, "w") as f:
            json.dump(data, f, indent=2)
    except OSError:
        pass


# --------------------------------------------------------------------------
# --------------------------------------------------------------------------
def fetch_positions(api_key, callsigns):
    names = ",".join(c.strip() for c in callsigns if c.strip())
    if not names:
        return []

    params = {"name": names, "what": "loc", "apikey": api_key, "format": "json"}
    url = API_URL + "?" + urllib.parse.urlencode(params)
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})

    try:
        with urllib.request.urlopen(req, timeout=15) as resp:
            raw = resp.read().decode("utf-8")
    except urllib.error.HTTPError as e:
        raise RuntimeError(f"HTTP error {e.code} from aprs.fi")
    except urllib.error.URLError as e:
        raise RuntimeError(f"Network error: {e.reason}")

    try:
        data = json.loads(raw)
    except json.JSONDecodeError:
        raise RuntimeError("aprs.fi returned invalid JSON")

    if data.get("result") != "ok":
        raise RuntimeError(data.get("description", "aprs.fi API returned an error"))

    return data.get("entries", [])


# --------------------------------------------------------------------------
# --------------------------------------------------------------------------
def lonlat_to_world_px(lon, lat, zoom):
    n = 2 ** zoom
    x = (lon + 180.0) / 360.0 * n * TILE_SIZE
    lat_rad = math.radians(max(min(lat, 85.05112878), -85.05112878))
    y = (1.0 - math.asinh(math.tan(lat_rad)) / math.pi) / 2.0 * n * TILE_SIZE
    return x, y


def world_px_to_lonlat(x, y, zoom):
    n = 2 ** zoom
    lon = x / (n * TILE_SIZE) * 360.0 - 180.0
    y_frac = y / (n * TILE_SIZE)
    lat_rad = math.atan(math.sinh(math.pi * (1 - 2 * y_frac)))
    lat = math.degrees(lat_rad)
    return lon, lat


# --------------------------------------------------------------------------

class TileMapWidget(tk.Frame):
    def __init__(self, master, on_marker_click=None, **kwargs):
        super().__init__(master, **kwargs)
        self.canvas = tk.Canvas(self, background="#1a1a1a", highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True)

        self.source_name = "Street (OpenStreetMap)"
        self.zoom = 6
        self.center_lon, self.center_lat = 153.0, -27.0  # roughly Queensland
        self.markers = {}  # name -> (lat, lon, symbol_str_or_None)
        self.selected_name = None
        self.on_marker_click = on_marker_click

        self._image_cache = {}          # (source, z, x, y) -> PhotoImage (kept alive)
        self._pending = set()           # tiles currently downloading
        self._tile_queue = queue.Queue()
        self._marker_hitboxes = []      # (x0,y0,x1,y1,name) for click detection

        self._symbol_sheets = {}        # table_char -> full PhotoImage sprite sheet
        self._symbol_sheets_pending = set()
        self._symbol_icon_cache = {}    # (table_char, code_char) -> cropped PhotoImage
        self._symbol_queue = queue.Queue()
        self._symbol_sheet_last_error = None
        self._symbol_sheet_retry_count = 0

        self._drag_start = None
        self._drag_origin_center_px = None

        os.makedirs(TILE_CACHE_DIR, exist_ok=True)

        self.canvas.bind("<Configure>", lambda e: self._redraw())
        self.canvas.bind("<ButtonPress-1>", self._on_press)
        self.canvas.bind("<B1-Motion>", self._on_drag)
        self.canvas.bind("<ButtonRelease-1>", self._on_release)
        self.canvas.bind("<MouseWheel>", self._on_wheel)      # Windows / macOS
        self.canvas.bind("<Button-4>", lambda e: self._zoom_step(1, e))   # Linux scroll up
        self.canvas.bind("<Button-5>", lambda e: self._zoom_step(-1, e))  # Linux scroll down

        self.after(80, self._poll_tile_queue)
        self.after(80, self._poll_symbol_queue)
        self._request_symbol_sheets()

    # ------------------------------------------------------------ public API
    def set_source(self, name):
        if name in TILE_SOURCES and name != self.source_name:
            self.source_name = name
            self._redraw()

    def set_markers(self, markers, selected_name=None):
        """markers: dict name -> (lat, lon) or (lat, lon, symbol_str)"""
        normalized = {}
        for name, val in markers.items():
            if len(val) == 2:
                normalized[name] = (val[0], val[1], None)
            else:
                normalized[name] = (val[0], val[1], val[2])
        self.markers = normalized
        self.selected_name = selected_name
        self._redraw()

    def select_marker(self, name):
        self.selected_name = name
        self._redraw()

    def fit_to_markers(self, padding_frac=0.18):
        pts = [v for v in self.markers.values() if v[0] is not None and v[1] is not None]
        if not pts:
            return
        lats = [p[0] for p in pts]
        lons = [p[1] for p in pts]
        if len(pts) == 1:
            self.center_lat, self.center_lon = lats[0], lons[0]
            self.zoom = 12
            self._redraw()
            return

        lat_min, lat_max = min(lats), max(lats)
        lon_min, lon_max = min(lons), max(lons)
        self.center_lat = (lat_min + lat_max) / 2
        self.center_lon = (lon_min + lon_max) / 2

        w = max(self.canvas.winfo_width(), 200)
        h = max(self.canvas.winfo_height(), 200)

        best_zoom = 2
        for z in range(19, 0, -1):
            x0, y0 = lonlat_to_world_px(lon_min, lat_max, z)
            x1, y1 = lonlat_to_world_px(lon_max, lat_min, z)
            span_x = abs(x1 - x0)
            span_y = abs(y1 - y0)
            if span_x <= w * (1 - padding_frac) and span_y <= h * (1 - padding_frac):
                best_zoom = z
                break
        self.zoom = best_zoom
        self._redraw()

    def zoom_in(self):
        self._zoom_step(1)

    def zoom_out(self):
        self._zoom_step(-1)

    # ------------------------------------------------------------ interaction
    def _on_press(self, event):
        self._drag_start = (event.x, event.y)
        self._drag_origin_center_px = lonlat_to_world_px(self.center_lon, self.center_lat, self.zoom)

    def _on_drag(self, event):
        if self._drag_start is None:
            return
        dx = event.x - self._drag_start[0]
        dy = event.y - self._drag_start[1]
        cx, cy = self._drag_origin_center_px
        new_center_px = (cx - dx, cy - dy)
        self.center_lon, self.center_lat = world_px_to_lonlat(*new_center_px, self.zoom)
        self._redraw()

    def _on_release(self, event):
        # Treat a near-zero-movement click as a marker click
        if self._drag_start and abs(event.x - self._drag_start[0]) < 4 and abs(event.y - self._drag_start[1]) < 4:
            for (x0, y0, x1, y1, name) in self._marker_hitboxes:
                if x0 <= event.x <= x1 and y0 <= event.y <= y1:
                    self.selected_name = name
                    self._redraw()
                    if self.on_marker_click:
                        self.on_marker_click(name)
                    break
        self._drag_start = None
        self._drag_origin_center_px = None

    def _on_wheel(self, event):
        direction = 1 if event.delta > 0 else -1
        self._zoom_step(direction, event)

    def _zoom_step(self, direction, event=None):
        _, _, _, max_zoom, _ = TILE_SOURCES[self.source_name]
        new_zoom = max(2, min(max_zoom, self.zoom + direction))
        if new_zoom == self.zoom:
            return
        self.zoom = new_zoom
        self._redraw()

    # ------------------------------------------------------------ tile loading
    def _cache_path(self, source, z, x, y, ext):
        safe_source = source.split(" ")[0].lower()
        return os.path.join(TILE_CACHE_DIR, safe_source, str(z), str(x), f"{y}.{ext}")

    def _request_tile(self, source, z, x, y):
        key = (source, z, x, y)
        if key in self._image_cache or key in self._pending:
            return
        n = 2 ** z
        if x < 0 or x >= n or y < 0 or y >= n:
            return
        self._pending.add(key)
        threading.Thread(target=self._download_tile, args=(source, z, x, y), daemon=True).start()

    def _download_tile(self, source, z, x, y):
        url_tmpl, ext, needs_pillow, _, _ = TILE_SOURCES[source]
        key = (source, z, x, y)
        if needs_pillow and not PIL_AVAILABLE:
            self._pending.discard(key)
            return

        cache_path = self._cache_path(source, z, x, y, ext)
        data = None
        if os.path.exists(cache_path):
            try:
                with open(cache_path, "rb") as f:
                    data = f.read()
            except OSError:
                data = None

        if data is None:
            url = url_tmpl.format(z=z, x=x, y=y)
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            try:
                with urllib.request.urlopen(req, timeout=10) as resp:
                    data = resp.read()
                os.makedirs(os.path.dirname(cache_path), exist_ok=True)
                try:
                    with open(cache_path, "wb") as f:
                        f.write(data)
                except OSError:
                    pass
            except (urllib.error.HTTPError, urllib.error.URLError):
                self._pending.discard(key)
                return

        self._tile_queue.put((key, data, ext, needs_pillow))

    def _poll_tile_queue(self):
        updated = False
        try:
            while True:
                key, data, ext, needs_pillow = self._tile_queue.get_nowait()
                self._pending.discard(key)
                try:
                    if needs_pillow:
                        img = Image.open(BytesIO(data))
                        photo = ImageTk.PhotoImage(img)
                    else:
                        photo = tk.PhotoImage(data=data)
                except Exception:
                    photo = None
                if photo is not None:
                    self._image_cache[key] = photo
                    updated = True
        except queue.Empty:
            pass
        if updated:
            self._redraw()
        self.after(80, self._poll_tile_queue)

    # ------------------------------------------------------------ APRS symbol icons
    def _request_symbol_sheets(self):
        for table_char in SYMBOL_SHEET_URLS:
            self._request_symbol_sheet_one(table_char)

    def _request_symbol_sheet_one(self, table_char):
        if table_char in self._symbol_sheets or table_char in self._symbol_sheets_pending:
            return
        self._symbol_sheets_pending.add(table_char)
        threading.Thread(target=self._download_symbol_sheet, args=(table_char,), daemon=True).start()

    def _download_symbol_sheet(self, table_char):
        url = SYMBOL_SHEET_URLS[table_char]
        safe_name = "primary" if table_char == "/" else "alternate"
        cache_path = os.path.join(TILE_CACHE_DIR, "symbols", f"{safe_name}.png")

        data = None
        try:
            if os.path.exists(cache_path):
                try:
                    with open(cache_path, "rb") as f:
                        data = f.read()
                except OSError:
                    data = None

            if data is None:
                req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
                with urllib.request.urlopen(req, timeout=15) as resp:
                    data = resp.read()
                try:
                    os.makedirs(os.path.dirname(cache_path), exist_ok=True)
                    with open(cache_path, "wb") as f:
                        f.write(data)
                except OSError:
                    pass  # cache write failing is not fatal, we still have the data

            self._symbol_queue.put((table_char, data, None))
        except Exception as e:  # noqa: BLE001 - any failure must reach the UI thread, not vanish
            self._symbol_queue.put((table_char, None, f"{type(e).__name__}: {e}"))

    def _poll_symbol_queue(self):
        updated = False
        try:
            while True:
                table_char, data, error = self._symbol_queue.get_nowait()
                self._symbol_sheets_pending.discard(table_char)

                if error is not None:
                    self._symbol_sheet_last_error = error
                    self._symbol_sheet_retry_count = self._symbol_sheet_retry_count + 1
                    delay_ms = min(60000, 5000 * self._symbol_sheet_retry_count)
                    self.after(delay_ms, lambda tc=table_char: self._request_symbol_sheet_one(tc))
                    continue

                try:
                    sheet = tk.PhotoImage(data=data)
                except Exception as e:
                    self._symbol_sheet_last_error = f"decode failed: {e}"
                    self.after(5000, lambda tc=table_char: self._request_symbol_sheet_one(tc))
                    continue

                self._symbol_sheets[table_char] = sheet
                self._symbol_sheet_last_error = None
                updated = True
        except queue.Empty:
            pass
        if updated:
            self._redraw()
        self.after(80, self._poll_symbol_queue)

    def _get_symbol_icon(self, symbol):
        """symbol: two-char APRS symbol string, e.g. '/>' or '\\_'. Returns a
        24x24 PhotoImage for the icon, or None if not yet available/invalid."""
        if not symbol or len(symbol) < 2:
            return None
        table_char, code_char = symbol[0], symbol[1]
        if table_char not in SYMBOL_SHEET_URLS:
            return None

        key = (table_char, code_char)
        cached = self._symbol_icon_cache.get(key)
        if cached is not None:
            return cached

        sheet = self._symbol_sheets.get(table_char)
        if sheet is None:
            return None  # still downloading; caller falls back to a dot

        code_point = ord(code_char)
        if code_point < 33 or code_point > 126:
            return None
        idx = code_point - 33
        row, col = divmod(idx, SYMBOL_GRID_COLS)
        x0, y0 = col * SYMBOL_CELL, row * SYMBOL_CELL
        x1, y1 = x0 + SYMBOL_CELL, y0 + SYMBOL_CELL

        try:
            icon = tk.PhotoImage(width=SYMBOL_CELL, height=SYMBOL_CELL)
            icon.tk.call(icon, "copy", sheet, "-from", x0, y0, x1, y1, "-to", 0, 0)
        except Exception:
            return None

        self._symbol_icon_cache[key] = icon
        return icon

    # ------------------------------------------------------------ drawing
    def _redraw(self):
        self.canvas.delete("all")
        self._marker_hitboxes = []

        w = self.canvas.winfo_width()
        h = self.canvas.winfo_height()
        if w < 10 or h < 10:
            return

        source = self.source_name
        _, ext, needs_pillow, max_zoom, attribution = TILE_SOURCES[source]
        if needs_pillow and not PIL_AVAILABLE:
            self.canvas.create_text(
                w / 2, h / 2,
                text="Satellite view needs Pillow.\nRun: pip install pillow --break-system-packages",
                fill="#e8f5e9", justify="center", font=("TkDefaultFont", 11),
            )
            return

        zoom = min(self.zoom, max_zoom)
        center_px_x, center_px_y = lonlat_to_world_px(self.center_lon, self.center_lat, zoom)

        top_left_x = center_px_x - w / 2
        top_left_y = center_px_y - h / 2

        first_tile_x = int(top_left_x // TILE_SIZE)
        first_tile_y = int(top_left_y // TILE_SIZE)
        last_tile_x = int((top_left_x + w) // TILE_SIZE) + 1
        last_tile_y = int((top_left_y + h) // TILE_SIZE) + 1

        for tx in range(first_tile_x, last_tile_x + 1):
            for ty in range(first_tile_y, last_tile_y + 1):
                screen_x = tx * TILE_SIZE - top_left_x
                screen_y = ty * TILE_SIZE - top_left_y
                key = (source, zoom, tx, ty)
                photo = self._image_cache.get(key)
                if photo is not None:
                    self.canvas.create_image(screen_x, screen_y, image=photo, anchor="nw")
                else:
                    self.canvas.create_rectangle(
                        screen_x, screen_y, screen_x + TILE_SIZE, screen_y + TILE_SIZE,
                        fill="#20262b", outline="#2a3238",
                    )
                    self._request_tile(source, zoom, tx, ty)

        # markers
        for name, (lat, lon, symbol) in self.markers.items():
            if lat is None or lon is None:
                continue
            px, py = lonlat_to_world_px(lon, lat, zoom)
            sx = px - top_left_x
            sy = py - top_left_y
            if -24 <= sx <= w + 24 and -24 <= sy <= h + 24:
                is_sel = name == self.selected_name
                icon = self._get_symbol_icon(symbol) if symbol else None

                if is_sel:
                    r_halo = (SYMBOL_CELL // 2) + 5 if icon is not None else 10
                    self.canvas.create_oval(
                        sx - r_halo, sy - r_halo, sx + r_halo, sy + r_halo,
                        fill="#ffb703", outline="#111111",
                    )

                if icon is not None:
                    self.canvas.create_image(sx, sy, image=icon, anchor="center")
                    half = SYMBOL_CELL // 2
                    hit = (sx - half, sy - half, sx + half, sy + half)
                else:
                    r = 8 if is_sel else 6
                    color = "#ffb703" if is_sel else "#ff3b30"
                    self.canvas.create_oval(
                        sx - r, sy - r, sx + r, sy + r,
                        fill=color, outline="#111111", width=1.5,
                    )
                    hit = (sx - r, sy - r, sx + r, sy + r)

                label_y = hit[1] - 9
                self.canvas.create_text(
                    sx, label_y, text=name, fill="#ffffff",
                    font=("TkDefaultFont", 9, "bold"),
                )
                self._marker_hitboxes.append((hit[0] - 4, hit[1] - 4, hit[2] + 4, hit[3] + 4, name))

        self.canvas.create_text(
            6, h - 6, anchor="sw", fill="#cccccc", font=("TkDefaultFont", 7),
            text=f"{attribution}   |   zoom {zoom}",
        )

        if self._symbol_sheet_last_error and not self._symbol_sheets:
            self.canvas.create_text(
                w - 6, h - 6, anchor="se", fill="#ff9d5c", font=("TkDefaultFont", 7),
                text=f"symbol icons unavailable ({self._symbol_sheet_last_error}) - retrying, showing dots meanwhile",
            )



# --------------------------------------------------------------------------
# Main application
# --------------------------------------------------------------------------
class AprsTrackerApp(tk.Tk):
    COLUMNS = ("callsign", "time", "lat", "lng", "alt", "speed", "course", "comment")
    HEADINGS = {
        "callsign": "Callsign", "time": "Last heard", "lat": "Latitude", "lng": "Longitude",
        "alt": "Alt (m)", "speed": "Speed (km/h)", "course": "Course", "comment": "Comment",
    }

    def __init__(self):
        super().__init__()
        self.title("APRS.fi Station Tracker")
        self.geometry("1080x700")
        self.minsize(820, 540)

        self.cfg = load_config()
        self.result_queue = queue.Queue()
        self.polling = False
        self.poll_thread = None
        self.stop_event = threading.Event()
        self.last_entries = []
        self.auto_fit = tk.BooleanVar(value=True)

        self._build_ui()
        self._restore_config()
        self.after(150, self._process_queue)
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    # ---------------------------------------------------------- UI layout
    def _build_ui(self):
        top = ttk.Frame(self, padding=8)
        top.pack(side=tk.TOP, fill=tk.X)

        ttk.Label(top, text="API key:").grid(row=0, column=0, sticky="w")
        self.api_key_var = tk.StringVar()
        self.api_key_entry = ttk.Entry(top, textvariable=self.api_key_var, width=24, show="*")
        self.api_key_entry.grid(row=0, column=1, sticky="we", padx=(4, 10))

        self.show_key_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(top, text="show", variable=self.show_key_var, command=self._toggle_key_visibility).grid(
            row=0, column=2, sticky="w"
        )

        ttk.Label(top, text="Callsigns:").grid(row=0, column=3, sticky="w", padx=(10, 0))
        self.callsigns_var = tk.StringVar()
        ttk.Entry(top, textvariable=self.callsigns_var, width=26).grid(row=0, column=4, sticky="we", padx=(4, 10))

        ttk.Label(top, text="Interval (s):").grid(row=0, column=5, sticky="w")
        self.interval_var = tk.IntVar(value=60)
        ttk.Spinbox(top, from_=15, to=3600, textvariable=self.interval_var, width=6).grid(
            row=0, column=6, sticky="w", padx=(4, 10)
        )

        self.start_btn = ttk.Button(top, text="Start tracking", command=self.start_tracking)
        self.start_btn.grid(row=0, column=7, padx=(0, 4))
        self.stop_btn = ttk.Button(top, text="Stop", command=self.stop_tracking, state=tk.DISABLED)
        self.stop_btn.grid(row=0, column=8, padx=(0, 4))
        self.refresh_btn = ttk.Button(top, text="Refresh now", command=self.poll_once_async)
        self.refresh_btn.grid(row=0, column=9)

        top.columnconfigure(1, weight=1)
        top.columnconfigure(4, weight=1)

        # second row: map controls
        map_ctrl = ttk.Frame(self, padding=(8, 0, 8, 6))
        map_ctrl.pack(side=tk.TOP, fill=tk.X)
        ttk.Label(map_ctrl, text="Map:").pack(side=tk.LEFT)
        self.map_source_var = tk.StringVar(value="Street (OpenStreetMap)")
        map_combo = ttk.Combobox(
            map_ctrl, textvariable=self.map_source_var, state="readonly",
            values=list(TILE_SOURCES.keys()), width=28,
        )
        map_combo.pack(side=tk.LEFT, padx=(4, 12))
        map_combo.bind("<<ComboboxSelected>>", lambda e: self.map_widget.set_source(self.map_source_var.get()))

        ttk.Button(map_ctrl, text="\u2212", width=3, command=lambda: self.map_widget.zoom_out()).pack(side=tk.LEFT)
        ttk.Button(map_ctrl, text="+", width=3, command=lambda: self.map_widget.zoom_in()).pack(side=tk.LEFT, padx=(2, 12))
        ttk.Button(map_ctrl, text="Fit to stations", command=lambda: self.map_widget.fit_to_markers()).pack(side=tk.LEFT)
        ttk.Checkbutton(map_ctrl, text="Auto-fit on update", variable=self.auto_fit).pack(side=tk.LEFT, padx=(12, 0))

        if not PIL_AVAILABLE:
            ttk.Label(
                map_ctrl, text="(Pillow not installed - satellite view unavailable)",
                foreground="#a05a2c",
            ).pack(side=tk.RIGHT)

        # Body: table left, map right
        body = ttk.PanedWindow(self, orient=tk.HORIZONTAL)
        body.pack(fill=tk.BOTH, expand=True, padx=8, pady=(0, 8))

        table_frame = ttk.Frame(body)
        self.tree = ttk.Treeview(table_frame, columns=self.COLUMNS, show="headings", height=10)
        for col in self.COLUMNS:
            self.tree.heading(col, text=self.HEADINGS[col])
            width = 150 if col == "comment" else 100
            self.tree.column(col, width=width, anchor="w")
        vsb = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)
        self.tree.bind("<<TreeviewSelect>>", self._on_tree_select)
        body.add(table_frame, weight=1)

        map_frame = ttk.Frame(body)
        self.map_widget = TileMapWidget(map_frame, on_marker_click=self._on_map_marker_click)
        self.map_widget.pack(fill=tk.BOTH, expand=True)
        body.add(map_frame, weight=2)

        status = ttk.Frame(self, padding=(8, 2))
        status.pack(side=tk.BOTTOM, fill=tk.X)
        self.status_var = tk.StringVar(value="Idle. Enter your aprs.fi API key and callsign(s), then Start tracking.")
        ttk.Label(status, textvariable=self.status_var).pack(side=tk.LEFT)

    def _toggle_key_visibility(self):
        self.api_key_entry.configure(show="" if self.show_key_var.get() else "*")

    def _restore_config(self):
        self.api_key_var.set(self.cfg.get("api_key", ""))
        self.callsigns_var.set(self.cfg.get("callsigns", ""))
        self.interval_var.set(self.cfg.get("interval", 60))
        saved_source = self.cfg.get("map_source")
        if saved_source in TILE_SOURCES:
            self.map_source_var.set(saved_source)
            self.map_widget.set_source(saved_source)

    # ---------------------------------------------------------- selection sync
    def _on_tree_select(self, event):
        sel = self.tree.selection()
        if sel:
            self.map_widget.select_marker(sel[0])

    def _on_map_marker_click(self, name):
        if self.tree.exists(name):
            self.tree.selection_set(name)
            self.tree.see(name)

    # ---------------------------------------------------------- tracking control
    def start_tracking(self):
        api_key = self.api_key_var.get().strip()
        callsigns = [c for c in self.callsigns_var.get().split(",") if c.strip()]
        if not api_key:
            messagebox.showwarning("Missing API key", "Enter your aprs.fi API key first.")
            return
        if not callsigns:
            messagebox.showwarning("Missing callsigns", "Enter at least one callsign or object name.")
            return

        self._save_current_config()

        self.polling = True
        self.stop_event.clear()
        self.start_btn.configure(state=tk.DISABLED)
        self.stop_btn.configure(state=tk.NORMAL)
        self.status_var.set("Tracking started.")

        self.poll_thread = threading.Thread(target=self._poll_loop, daemon=True)
        self.poll_thread.start()

    def stop_tracking(self):
        self.polling = False
        self.stop_event.set()
        self.start_btn.configure(state=tk.NORMAL)
        self.stop_btn.configure(state=tk.DISABLED)
        self.status_var.set("Tracking stopped.")

    def poll_once_async(self):
        api_key = self.api_key_var.get().strip()
        callsigns = [c for c in self.callsigns_var.get().split(",") if c.strip()]
        if not api_key or not callsigns:
            messagebox.showwarning("Missing info", "Enter an API key and at least one callsign.")
            return
        threading.Thread(target=self._poll_once, args=(api_key, callsigns), daemon=True).start()

    def _poll_loop(self):
        while not self.stop_event.is_set():
            api_key = self.api_key_var.get().strip()
            callsigns = [c for c in self.callsigns_var.get().split(",") if c.strip()]
            self._poll_once(api_key, callsigns)
            interval = max(15, int(self.interval_var.get() or 60))
            self.stop_event.wait(interval)

    def _poll_once(self, api_key, callsigns):
        try:
            entries = fetch_positions(api_key, callsigns)
            self.result_queue.put(("ok", entries))
        except RuntimeError as e:
            self.result_queue.put(("error", str(e)))

    # ---------------------------------------------------------- queue -> UI thread
    def _process_queue(self):
        try:
            while True:
                kind, payload = self.result_queue.get_nowait()
                if kind == "ok":
                    self._update_table(payload)
                    stamp = time.strftime("%H:%M:%S")
                    self.status_var.set(f"Last updated {stamp} - {len(payload)} station(s) found.")
                else:
                    self.status_var.set(f"Error: {payload}")
        except queue.Empty:
            pass
        self.after(150, self._process_queue)

    def _update_table(self, entries):
        self.last_entries = entries
        had_rows_before = len(self.tree.get_children()) > 0
        self.tree.delete(*self.tree.get_children())
        markers = {}
        for e in entries:
            t = e.get("lasttime") or e.get("time")
            try:
                t_str = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(int(t)))
            except (TypeError, ValueError):
                t_str = str(t or "")
            name = e.get("name", "")
            values = (
                name, t_str, e.get("lat", ""), e.get("lng", ""),
                e.get("altitude", e.get("alt", "")), e.get("speed", ""),
                e.get("course", ""), e.get("comment", ""),
            )
            self.tree.insert("", tk.END, iid=name, values=values)
            try:
                markers[name] = (float(e.get("lat")), float(e.get("lng")), e.get("symbol"))
            except (TypeError, ValueError):
                pass

        self.map_widget.set_markers(markers, selected_name=self.map_widget.selected_name)
        if markers and (self.auto_fit.get() or not had_rows_before):
            self.map_widget.fit_to_markers()

    def _save_current_config(self):
        save_config({
            "api_key": self.api_key_var.get().strip(),
            "callsigns": self.callsigns_var.get(),
            "interval": self.interval_var.get(),
            "map_source": self.map_source_var.get(),
        })

    # ---------------------------------------------------------- shutdown
    def _on_close(self):
        self.stop_event.set()
        self.polling = False
        self._save_current_config()
        self.destroy()


if __name__ == "__main__":
    app = AprsTrackerApp()
    app.mainloop()
