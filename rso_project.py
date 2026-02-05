#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
RSO Accessibility Project (Russia): Recyclemap harvesting + accessibility index + white spots + recommendations + map + mini-service helpers.

Key features:
- Fast Recyclemap scan with concurrency + global rate limit + resume via state file.
- Cache reuse across runs; backward-compatible with older cache file names.
- Excludes non-residential areas (water / forests / parks / large industrial zones) using OSM (optional).
- Accessibility metrics overall + per waste type (finite-only aggregation; no infinities in report).
- Auto-recommendations "where to open new points" for selected waste types.
- Folium map with layers + HTML patch for older/strict JS engines (removes object spread "...{ }" and fixes octal escapes "\2").
- Nearest-points helper + geocoding for mini-service.

Usage (examples):
  python rso_project.py pipeline --bbox 37.20 55.50 37.95 55.97 --end-id 50000 --data-dir data --out-dir run
  python rso_project.py nearest --points run/points_filtered.csv --address "Москва, Тверская 7" --waste-type Пластик

Notes:
- Recyclemap public API endpoint is used as-is.
- Respect external services' rate limits (Recyclemap, Nominatim).
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import math
import os
import random
import re
import shutil
import sys
import threading
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

# Optional deps (import lazily where possible)
try:
    import requests  # type: ignore
except Exception as _e:  # pragma: no cover
    requests = None  # type: ignore

try:
    import pandas as pd  # type: ignore
except Exception:  # pragma: no cover
    pd = None  # type: ignore

try:
    import numpy as np  # type: ignore
except Exception:  # pragma: no cover
    np = None  # type: ignore

try:
    from pyproj import CRS, Transformer  # type: ignore
except Exception:  # pragma: no cover
    CRS = None  # type: ignore
    Transformer = None  # type: ignore

try:
    import folium  # type: ignore
    from folium.plugins import MarkerCluster  # type: ignore
except Exception:  # pragma: no cover
    folium = None  # type: ignore
    MarkerCluster = None  # type: ignore

# For faster nearest-neighbor distances
try:
    from scipy.spatial import cKDTree  # type: ignore
except Exception:  # pragma: no cover
    cKDTree = None  # type: ignore

# OSM exclusions (optional)
try:
    import osmnx as ox  # type: ignore
except Exception:  # pragma: no cover
    ox = None  # type: ignore

try:
    from shapely.geometry import Point as ShpPoint  # type: ignore
    from shapely.geometry import shape as ShpShape  # type: ignore
    from shapely.geometry.base import BaseGeometry  # type: ignore
    from shapely.prepared import prep as ShpPrep  # type: ignore
    from shapely.strtree import STRtree  # type: ignore
    from shapely.ops import transform as ShpTransform  # type: ignore
    from shapely import wkt as _shp_wkt  # type: ignore
except Exception:  # pragma: no cover
    ShpPoint = None  # type: ignore
    ShpShape = None  # type: ignore
    BaseGeometry = object  # type: ignore
    ShpPrep = None  # type: ignore
    STRtree = None  # type: ignore
    ShpTransform = None  # type: ignore
    _shp_wkt = None  # type: ignore

# -----------------------------
# Constants & dictionaries
# -----------------------------

RECYCLEMAP_POINT_URL = "https://recyclemap.ru/api/public/points/{point_id}"

# Optional: population dataset for Moscow districts (used for per-capita indices)
MOSCOW_POPULATION_2018_CSV_URL = "https://storage.yandexcloud.net/doc-files/Moscow%20Population%202018.csv"

# Mapping of Recyclemap fraction codes -> human-readable labels (for nicer outputs)
FRACTION_CODE_TO_NAME: Dict[str, str] = {
    "BUMAGA": "Бумага",
    "PLASTIK": "Пластик",
    "STEKLO": "Стекло",
    "METALL": "Металл",
    "TETRA_PAK": "ТетраПак",
    "KRYSHECHKI": "Крышечки",
    "BATAREJKI": "Батарейки",
    "LAMPOCHKI": "Лампочки",
    "BYTOVAJA_TEHNIKA": "Электроника/техника",
    "OPASNYE_OTHODY": "Опасные отходы",
    "ODEZHDA": "Одежда",
    "SHINY": "Шины",
    "INOE": "Другое",
}

# Waste categories for scheme="categories":
# key = display name (used in layers/metrics)
# values = substrings to match (case-insensitive) in fractions text.
# IMPORTANT: includes both Russian keywords and Recyclemap translit codes (bumaga, plastik, batarejki, ...)
WASTE_CATEGORIES: Dict[str, List[str]] = {
    "Бумага": ["бумаг", "макулат", "картон", "bumaga"],
    "Пластик": ["пласт", "пэт", "pet", "полиэт", "polyeth", "пвх", "pvc", "plastik", "kryshechki", "крышеч"],
    "Стекло": ["стекл", "steklo"],
    "Металл": ["металл", "алюмин", "жест", "бан", "metall"],
    "ТетраПак": ["тетра", "tetra", "tetra_pak", "tetrapak"],
    "Батарейки": ["батар", "аккум", "аккумулят", "batarejki", "battery"],
    "Лампочки": ["ламп", "ртут", "lampochki", "lamp"],
    "Электроника": ["электрон", "техник", "e-waste", "ewaste", "bytovaja_tehnika", "электроприб", "прибора"],
    "Одежда": ["одежд", "текстил", "odezhda", "textil"],
    "Шины": ["шин", "покрыш", "tire", "tyre", "shiny"],
    "Опасные отходы": ["опасн", "hazard", "opasnye_othody"],
    "Крышечки": ["крышеч", "kryshechki"],
}

# OSM tags to exclude from "residential-accessible" analysis area (water/forests/parks/large industrial zones)
OSM_EXCLUDE_TAGS: Dict[str, object] = {
    # Water & forests
    "natural": ["water", "wood"],
    "waterway": ["riverbank"],
    "landuse": ["reservoir", "forest", "industrial", "railway", "construction", "military"],
    # Parks / protected areas
    "leisure": ["park", "nature_reserve", "garden"],
    "boundary": ["protected_area"],
}


# -----------------------------
# Data structures
# -----------------------------

@dataclasses.dataclass(frozen=True)
class BBox:
    lon_min: float
    lat_min: float
    lon_max: float
    lat_max: float

    def contains(self, lon: float, lat: float) -> bool:
        return (self.lon_min <= lon <= self.lon_max) and (self.lat_min <= lat <= self.lat_max)

    def as_tuple_lrbt(self, ndigits: int = 6) -> Tuple[float, float, float, float]:
        # (left, bottom, right, top)
        return (
            round(float(self.lon_min), ndigits),
            round(float(self.lat_min), ndigits),
            round(float(self.lon_max), ndigits),
            round(float(self.lat_max), ndigits),
        )

    def center(self) -> Tuple[float, float]:
        return ((self.lon_min + self.lon_max) / 2.0, (self.lat_min + self.lat_max) / 2.0)


# -----------------------------
# Helpers (text, paths, hashing)
# -----------------------------

def safe_mkdir(p: Path) -> None:
    p.mkdir(parents=True, exist_ok=True)


def utc_now_iso() -> str:
    # timezone-aware UTC (no deprecated utcnow)
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _stable_hash(obj: object, n: int = 12) -> str:
    s = json.dumps(obj, ensure_ascii=False, sort_keys=True)
    return hashlib.sha1(s.encode("utf-8")).hexdigest()[:n]


def normalize_text(s: str) -> str:
    """Lowercase + normalize separators for robust substring matching."""
    if s is None:
        return ""
    t = str(s).lower().replace("ё", "е")
    # unify separators
    t = t.replace("_", " ")
    t = re.sub(r"[;|/]+", ",", t)
    t = re.sub(r"\s+", " ", t).strip()
    return t


def sanitize_text(s: object) -> str:
    """Basic HTML-escaping for Folium popups (avoid breaking HTML/JS)."""
    if s is None:
        return ""
    t = str(s)
    t = t.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    t = t.replace('"', "&quot;").replace("'", "&#x27;")
    return t


def _fmt_dist_m(val: object) -> str:
    """Safe formatting of distance (meters) for UI."""
    try:
        v = float(val)
    except Exception:
        return "NA"
    if not math.isfinite(v):
        return "∞"
    return str(int(round(v)))


def _fmt_float(val: object, nd: int = 2) -> str:
    try:
        v = float(val)
    except Exception:
        return "NA"
    if not math.isfinite(v):
        return "∞"
    return f"{v:.{nd}f}"

# -----------------------------
# Moscow districts (optional): boundaries + per-district metrics
# -----------------------------

@dataclasses.dataclass
class District:
    """Single district/raion polygon (old boundaries)."""
    name: str
    ao: str = ""
    abbrev_ao: str = ""
    okato: str = ""
    oktmo: str = ""
    geom: "BaseGeometry" = None  # type: ignore


@dataclasses.dataclass
class DistrictIndex:
    """Spatial index for fast point-in-polygon assignment."""
    districts: List[District]
    tree: object
    geom_id_to_idx: Dict[int, int]
    prepared: List[object]


def load_districts_geojson(path: Path) -> DistrictIndex:
    """
    Load districts from a GeoJSON file (WGS84 lon/lat).
    Expected properties keys (best-effort):
      - NAME, NAME_AO, ABBREV_AO, OKATO, OKTMO
    """
    if ShpShape is None or STRtree is None or ShpPrep is None:
        raise RuntimeError("shapely is required for district boundaries. Install: pip install shapely")

    obj = json.loads(path.read_text(encoding="utf-8"))
    feats = obj.get("features", [])
    districts: List[District] = []
    geoms: List[BaseGeometry] = []

    for f in feats:
        props = f.get("properties", {}) or {}
        name = str(props.get("NAME") or props.get("name") or "").strip()
        ao = str(props.get("NAME_AO") or props.get("AO") or "").strip()
        abbr = str(props.get("ABBREV_AO") or props.get("ABBREV") or "").strip()
        okato = str(props.get("OKATO") or "").strip()
        oktmo = str(props.get("OKTMO") or "").strip()

        geom = ShpShape(f.get("geometry"))
        if geom is None:
            continue
        districts.append(District(name=name, ao=ao, abbrev_ao=abbr, okato=okato, oktmo=oktmo, geom=geom))
        geoms.append(geom)

    tree = STRtree(geoms)
    geom_id_to_idx = {id(g): i for i, g in enumerate(geoms)}
    prepared = [ShpPrep(g) for g in geoms]

    return DistrictIndex(districts=districts, tree=tree, geom_id_to_idx=geom_id_to_idx, prepared=prepared)


def assign_district_indices(lons: Sequence[float], lats: Sequence[float], dindex: DistrictIndex) -> "np.ndarray":
    """
    Assign each lon/lat to a district index (0..N-1), or -1 if outside.

    IMPORTANT: compatible with both Shapely 1.x and Shapely 2.x:
      - Shapely 1.x: STRtree.query(point) -> list[geometry]
      - Shapely 2.x: STRtree.query(point) -> numpy array of integer indices

    Uses STRtree + prepared geometries.
    """
    if np is None:
        raise RuntimeError("numpy is required. Install: pip install numpy")
    if ShpPoint is None:
        raise RuntimeError("shapely is required. Install: pip install shapely")

    out = np.full(len(lons), -1, dtype=int)
    tree = dindex.tree
    id2i = dindex.geom_id_to_idx
    preps = dindex.prepared

    for i, (lon, lat) in enumerate(zip(lons, lats)):
        try:
            pt = ShpPoint(float(lon), float(lat))
        except Exception:
            continue

        try:
            cands = tree.query(pt)
        except Exception:
            cands = []

        if cands is None:
            continue

        # Shapely 2.x: cands is array of integer indices
        cand_indices: List[int] = []
        try:
            if hasattr(cands, "__len__") and len(cands) > 0 and isinstance(cands[0], (int, np.integer)):
                cand_indices = [int(j) for j in cands]
            else:
                # Shapely 1.x: cands is list of geometries
                for g in cands:
                    idx = id2i.get(id(g))
                    if idx is not None:
                        cand_indices.append(int(idx))
        except Exception:
            # Last resort: assume it's geometries
            try:
                for g in cands:
                    idx = id2i.get(id(g))
                    if idx is not None:
                        cand_indices.append(int(idx))
            except Exception:
                cand_indices = []

        for idx in cand_indices:
            if idx < 0 or idx >= len(preps):
                continue
            try:
                # covers() is more tolerant than contains() (includes boundary points)
                if preps[idx].covers(pt):
                    out[i] = int(idx)
                    break
            except Exception:
                continue

    return out


def _parse_int_any(x: object) -> Optional[int]:
    if x is None:
        return None
    s = str(x).strip()
    s = re.sub(r"[^0-9]", "", s)
    if not s:
        return None
    try:
        return int(s)
    except Exception:
        return None


def _parse_float_ru(x: object) -> Optional[float]:
    if x is None:
        return None
    s = str(x).strip().replace(",", ".")
    s = re.sub(r"[^0-9.\\-]", "", s)
    if not s:
        return None
    try:
        return float(s)
    except Exception:
        return None


def ensure_moscow_population_csv(data_dir: Path, refresh: bool = False) -> Optional[Path]:
    """
    Ensure Moscow district population CSV exists locally.

    Uses Yandex Cloud tutorial dataset 'Moscow Population 2018.csv' (source: Wikipedia list of districts).
    URL: MOSCOW_POPULATION_2018_CSV_URL
    """
    dst = data_dir / "Moscow_Population_2018.csv"
    if dst.exists() and not refresh:
        return dst
    if requests is None:
        return dst if dst.exists() else None
    try:
        r = requests.get(MOSCOW_POPULATION_2018_CSV_URL, timeout=60)
        r.raise_for_status()
        dst.write_bytes(r.content)
        return dst
    except Exception as e:
        print(f"[WARN] Failed to download Moscow population CSV: {e}")
        return dst if dst.exists() else None


def load_moscow_population_by_district(csv_path: Path) -> Dict[str, Dict[str, object]]:
    """
    Load district population (+ optional area) from the Moscow population CSV.

    Returns mapping:
      norm_district_name -> {"district": <orig>, "population": int, "area_km2": float, "ao": str}
    """
    if pd is None:
        raise RuntimeError("pandas is required. Install: pip install pandas")

    dfp = pd.read_csv(csv_path)
    # Best-effort column mapping (dataset is in Russian)
    col_name = None
    for c in ["Район", "район", "District", "NAME"]:
        if c in dfp.columns:
            col_name = c
            break
    if col_name is None:
        raise RuntimeError(f"Population CSV has no district-name column. Columns: {list(dfp.columns)}")

    col_pop = None
    for c in ["Население", "население", "Population"]:
        if c in dfp.columns:
            col_pop = c
            break
    if col_pop is None:
        raise RuntimeError(f"Population CSV has no population column. Columns: {list(dfp.columns)}")

    col_area = None
    for c in ["Площадь", "площадь", "Area"]:
        if c in dfp.columns:
            col_area = c
            break

    col_ao = None
    for c in ["АО", "ao", "AO"]:
        if c in dfp.columns:
            col_ao = c
            break

    out: Dict[str, Dict[str, object]] = {}
    for _, r in dfp.iterrows():
        name_raw = str(r.get(col_name, "")).strip()
        if not name_raw:
            continue
        key = normalize_text(name_raw)
        pop = _parse_int_any(r.get(col_pop))
        if pop is None:
            continue
        area_km2 = _parse_float_ru(r.get(col_area)) if col_area else None
        ao = str(r.get(col_ao, "")).strip() if col_ao else ""
        out[key] = {"district": name_raw, "population": int(pop), "area_km2": area_km2, "ao": ao}
    return out


# -----------------------------
# Recyclemap parsing & matching
# -----------------------------

def parse_wkt_point(wkt_str: str) -> Optional[Tuple[float, float]]:
    """Parse 'POINT(lon lat)' and return (lon, lat)."""
    if not wkt_str:
        return None
    m = re.search(r"POINT\s*\(\s*([0-9\.\-]+)\s+([0-9\.\-]+)\s*\)", str(wkt_str))
    if not m:
        return None
    return float(m.group(1)), float(m.group(2))


def _fractions_to_text_and_raw(fractions_obj: object) -> Tuple[str, str]:
    """
    Convert Recyclemap 'fractions' field into:
    - fractions_raw: codes or raw strings (comma-separated)
    - fractions_text: human-readable (comma-separated, Russian where possible)
    Supports:
      - str
      - list[str]
      - list[dict] with keys like 'title'/'name'/'code'
    """
    if fractions_obj is None:
        return "", ""

    # If already a string like "BUMAGA,PLASTIK"
    if isinstance(fractions_obj, str):
        raw = fractions_obj
    elif isinstance(fractions_obj, list):
        parts: List[str] = []
        for it in fractions_obj:
            if it is None:
                continue
            if isinstance(it, str):
                parts.append(it)
            elif isinstance(it, dict):
                # try common fields
                for k in ("code", "title", "name", "value"):
                    if k in it and it[k]:
                        parts.append(str(it[k]))
                        break
                else:
                    parts.append(str(it))
            else:
                parts.append(str(it))
        raw = ",".join(parts)
    else:
        raw = str(fractions_obj)

    raw = raw.strip()
    # Build readable: map codes -> names, keep unknown as-is
    tokens = [t.strip() for t in re.split(r"[,;]+", raw) if t.strip()]
    readable_parts: List[str] = []
    for tok in tokens:
        up = tok.strip().upper()
        readable_parts.append(FRACTION_CODE_TO_NAME.get(up, tok))
    readable = ", ".join(dict.fromkeys(readable_parts))  # preserve order, unique
    raw_norm = ",".join(dict.fromkeys([t.strip().upper() for t in tokens]))
    return readable, raw_norm


def point_accepts_type(fractions_text: str, waste_type: str, scheme: str = "categories") -> bool:
    """
    Determine if a point accepts a given waste type.
    - scheme='categories': uses keyword lists in WASTE_CATEGORIES (includes Recyclemap translit codes)
    - scheme='raw': substring match of waste_type in fractions_text
    """
    if not fractions_text:
        return False
    ft = normalize_text(fractions_text)
    if scheme == "raw":
        return normalize_text(waste_type) in ft

    keywords = WASTE_CATEGORIES.get(waste_type)
    if not keywords:
        # fallback: substring match
        return normalize_text(waste_type) in ft

    return any(normalize_text(k) in ft for k in keywords)


def recyclemap_get_point(point_id: int, session: "requests.Session", timeout: int = 20) -> Tuple[bool, Optional[dict]]:
    """
    Fetch a single point card from Recyclemap public API.
    Returns: (exists, data_dict_or_none)
      exists=False means card does not exist / cannot be parsed / non-200 / isSuccess==False.
      exists=True means API returned a valid 'data' object (even if later filtered out of bbox).
    """
    if requests is None:
        raise RuntimeError("requests is required. Install: pip install requests")
    url = RECYCLEMAP_POINT_URL.format(point_id=point_id)
    try:
        r = session.get(url, timeout=timeout)
    except Exception:
        return False, None
    if r.status_code != 200:
        return False, None
    try:
        payload = r.json()
    except Exception:
        return False, None
    if not payload or not payload.get("isSuccess"):
        return False, None
    return True, payload.get("data")


def parse_recyclemap_row(data: dict) -> Optional[Dict[str, object]]:
    """Extract a flat row from Recyclemap data card."""
    if not data:
        return None

    point_id = data.get("id") or data.get("pointId") or data.get("point_id")
    try:
        point_id_i = int(point_id)
    except Exception:
        return None

    # geometry / lonlat
    lonlat = None
    for gk in ("geometry", "geom", "wkt"):
        if gk in data and data[gk]:
            lonlat = parse_wkt_point(str(data[gk]))
            if lonlat:
                break
    if lonlat is None:
        # Sometimes coordinates might be direct
        if "lon" in data and "lat" in data and data["lon"] and data["lat"]:
            try:
                lonlat = (float(data["lon"]), float(data["lat"]))
            except Exception:
                lonlat = None
    if lonlat is None:
        return None
    lon, lat = lonlat

    # type (optional)
    ptype = str(data.get("pointType") or data.get("type") or data.get("point_type") or "").strip()

    title = data.get("title") or data.get("name") or ""
    address = data.get("address") or data.get("fullAddress") or data.get("addr") or ""

    fractions_text, fractions_raw = _fractions_to_text_and_raw(data.get("fractions"))
    # Some cards might have fractions in another field
    if not fractions_text and data.get("fractionsText"):
        fractions_text = str(data.get("fractionsText"))
    if not fractions_raw and fractions_text:
        fractions_raw = ",".join([t.strip().upper() for t in re.split(r"[,;]+", fractions_text) if t.strip()])

    return {
        "id": point_id_i,
        "lon": float(lon),
        "lat": float(lat),
        "title": str(title),
        "address": str(address),
        "point_type": ptype,
        "fractions_raw": str(fractions_raw),
        "fractions": str(fractions_text),
    }


# -----------------------------
# Cache selection (backward compatibility)
# -----------------------------

def _points_signature_v2(bbox: BBox, point_type: str, start_id: int) -> Dict[str, object]:
    return {
        "version": 2,
        "bbox": bbox.as_tuple_lrbt(),
        "point_type": str(point_type or ""),
        "start_id": int(start_id),
        "source": "recyclemap_public_api",
    }


def _state_progress(state: dict, default: int) -> int:
    """Return progress id from state, compatible with older field names."""
    for k in ("max_scanned_id", "last_scanned_id", "last_id", "scanned_to", "end_id_scanned"):
        if k in state and state[k] is not None:
            try:
                return int(state[k])
            except Exception:
                pass
    return int(default)


def _read_json(path: Path) -> Optional[dict]:
    try:
        return json.loads(path.read_text(encoding="utf-8", errors="ignore"))
    except Exception:
        return None


def _bbox_like_equal(a: Sequence[float], b: Sequence[float], tol: float = 1e-5) -> bool:
    if len(a) != 4 or len(b) != 4:
        return False
    return all(abs(float(x) - float(y)) <= tol for x, y in zip(a, b))


def _state_matches(bbox: BBox, point_type: str, start_id: int, state: dict) -> bool:
    """Best-effort match of an old state file to current run params."""
    if not isinstance(state, dict):
        return False

    # Signature field (newer)
    sig = state.get("signature")
    if isinstance(sig, dict):
        try:
            bbox_sig = sig.get("bbox")
            if isinstance(bbox_sig, (list, tuple)) and _bbox_like_equal(bbox_sig, bbox.as_tuple_lrbt()):
                if str(sig.get("point_type", "")) == str(point_type or "") and int(sig.get("start_id", start_id)) == int(start_id):
                    return True
        except Exception:
            pass

    # Direct fields (older)
    bbox_state = state.get("bbox")
    if isinstance(bbox_state, dict):
        try:
            bbox2 = (bbox_state.get("lon_min"), bbox_state.get("lat_min"), bbox_state.get("lon_max"), bbox_state.get("lat_max"))
            if all(x is not None for x in bbox2) and _bbox_like_equal(bbox2, bbox.as_tuple_lrbt()):
                return True
        except Exception:
            pass
    if isinstance(bbox_state, (list, tuple)) and _bbox_like_equal(bbox_state, bbox.as_tuple_lrbt()):
        return True

    # If no bbox info, cannot prove match
    return False


def select_cache_files(
    data_dir: Path,
    bbox: BBox,
    point_type: str,
    start_id: int,
) -> Tuple[Path, Path, Path, str]:
    """
    Choose cache file paths, with backward compatibility.
    Returns: (points_csv, cache_jsonl, state_json, chosen_key_label)
    """
    safe_mkdir(data_dir)

    # New v2 signature paths
    sig2 = _points_signature_v2(bbox=bbox, point_type=point_type, start_id=start_id)
    key2 = _stable_hash(sig2)
    p2 = data_dir / f"points_filtered__{key2}.csv"
    c2 = data_dir / f"cache_points__{key2}.jsonl"
    s2 = data_dir / f"harvest_state__{key2}.json"
    if s2.exists() or p2.exists() or c2.exists():
        return p2, c2, s2, f"v2:{key2}"

    # Candidate legacy keyed states: harvest_state__*.json
    candidates = sorted(data_dir.glob("harvest_state__*.json"))
    matches: List[Tuple[float, Path, dict]] = []
    for st_path in candidates:
        st = _read_json(st_path)
        if st is None:
            continue
        if _state_matches(bbox=bbox, point_type=point_type, start_id=start_id, state=st):
            matches.append((st_path.stat().st_mtime, st_path, st))

    if matches:
        # choose most recent match
        matches.sort(key=lambda x: x[0], reverse=True)
        st_path = matches[0][1]
        m = re.match(r"harvest_state__(.+)\.json$", st_path.name)
        if m:
            key = m.group(1)
            return (
                data_dir / f"points_filtered__{key}.csv",
                data_dir / f"cache_points__{key}.jsonl",
                st_path,
                f"legacy:{key}",
            )

    # If no exact match, but legacy keyed state files exist, pick the most recent one (best-effort)
    # This helps reuse old caches produced by earlier script versions without rescanning 10+ hours.
    if (not matches) and candidates:
        st_path = max(candidates, key=lambda p: p.stat().st_mtime)
        m = re.match(r"harvest_state__(.+)\.json$", st_path.name)
        if m:
            key = m.group(1)
            return (
                data_dir / f"points_filtered__{key}.csv",
                data_dir / f"cache_points__{key}.jsonl",
                st_path,
                f"legacy:most_recent:{key}",
            )

    # Unkeyed legacy
    p0 = data_dir / "points_filtered.csv"
    c0 = data_dir / "cache_points.jsonl"
    s0 = data_dir / "harvest_state.json"
    if s0.exists() or p0.exists() or c0.exists():
        return p0, c0, s0, "legacy:unkeyed"

    # Default v2 paths (even if don't exist yet)
    return p2, c2, s2, f"v2:{key2}"


# -----------------------------
# Fast scan with concurrency + resume
# -----------------------------

class GlobalRateLimiter:
    """Simple global rate limiter for threads: ensures <= rps calls per second overall."""
    def __init__(self, rps: float):
        self.rps = max(float(rps), 0.0)
        self._lock = threading.Lock()
        self._next_allowed = time.monotonic()

    def wait(self) -> None:
        if self.rps <= 0:
            return
        with self._lock:
            now = time.monotonic()
            min_interval = 1.0 / self.rps
            if now < self._next_allowed:
                sleep_s = self._next_allowed - now
                self._next_allowed += min_interval
            else:
                sleep_s = 0.0
                self._next_allowed = now + min_interval
        if sleep_s > 0:
            time.sleep(sleep_s)


_thread_local = threading.local()


def _get_session() -> "requests.Session":
    if requests is None:
        raise RuntimeError("requests is required. Install: pip install requests")
    sess = getattr(_thread_local, "session", None)
    if sess is None:
        sess = requests.Session()
        # Basic UA - helps some endpoints
        sess.headers.update({"User-Agent": "rso-school-project/1.0"})
        _thread_local.session = sess
    return sess


def import_cache_jsonl_to_points_csv(
    cache_jsonl: Path,
    points_csv: Path,
    bbox: BBox,
    point_type: str,
    type_scheme: str = "categories",
) -> Tuple[int, int]:
    """
    Build (or rebuild) points CSV from an existing JSONL cache.
    Returns (n_rows_written, max_point_id_seen).

    The JSONL can contain:
      - raw Recyclemap 'data' dicts
      - flattened row dicts produced by this script
      - wrapper dicts with key 'data'
    """
    if pd is None:
        raise RuntimeError("pandas is required. Install: pip install pandas")
    if not cache_jsonl.exists():
        return 0, 0

    rows: List[Dict[str, object]] = []
    max_seen = 0

    def _accept_row(row: Dict[str, object]) -> bool:
        # Filter by bbox and point_type if present
        try:
            lon = float(row.get("lon"))
            lat = float(row.get("lat"))
        except Exception:
            return False
        if not bbox.contains(lon, lat):
            return False
        pt = str(row.get("point_type") or "")
        if point_type and pt and pt != point_type:
            # If point_type missing in cache, we won't filter it out.
            return False
        return True

    with cache_jsonl.open("r", encoding="utf-8", errors="ignore") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                obj = json.loads(line)
            except Exception:
                continue

            data_obj = None
            if isinstance(obj, dict) and "data" in obj and isinstance(obj["data"], dict):
                data_obj = obj["data"]
            elif isinstance(obj, dict) and ("lon" in obj and "lat" in obj and "id" in obj):
                # row-like already
                row = obj
            elif isinstance(obj, dict):
                data_obj = obj
            else:
                continue

            if data_obj is not None:
                row = parse_recyclemap_row(data_obj) or {}
            if not row:
                continue

            try:
                pid = int(row.get("id"))
                max_seen = max(max_seen, pid)
            except Exception:
                pass

            if _accept_row(row):
                # Ensure fractions columns exist
                if "fractions_raw" not in row:
                    row["fractions_raw"] = str(row.get("fractions", ""))
                if "fractions" not in row:
                    row["fractions"] = str(row.get("fractions_raw", ""))
                rows.append(row)

    if not rows:
        return 0, max_seen

    df = pd.DataFrame(rows)
    # Deduplicate by id
    if "id" in df.columns:
        df = df.drop_duplicates(subset=["id"])
    safe_mkdir(points_csv.parent)
    df.to_csv(points_csv, index=False, encoding="utf-8")
    return int(len(df)), int(max_seen)


def harvest_recyclemap_points_cached(
    data_dir: Path,
    bbox: BBox,
    point_type: str = "RC",
    start_id: int = 1,
    end_id: int = 50000,
    *,
    reuse_cache: bool = True,
    refresh: bool = False,
    # speed
    scan_workers: int = 12,
    rate_limit_rps: float = 4.0,
    timeout_s: int = 20,
    retries: int = 2,
    scan_chunk: int = 400,
    stop_after_misses: int = 0,
    # cache format
    write_raw_cache: bool = True,
) -> Path:
    """
    Scan Recyclemap IDs and save filtered points within bbox into a CSV.
    Supports resume via state file and reusing previous cache (including older versions).

    - If already scanned to end_id, it will reuse points CSV without rescanning.
    - If end_id increased, it continues from last scanned id + 1.
    """
    if pd is None:
        raise RuntimeError("pandas is required. Install: pip install pandas")
    if requests is None:
        raise RuntimeError("requests is required. Install: pip install requests")

    safe_mkdir(data_dir)

    points_csv, cache_jsonl, state_json, key_label = select_cache_files(
        data_dir=data_dir, bbox=bbox, point_type=point_type, start_id=start_id
    )

    if refresh:
        for p in (points_csv, cache_jsonl, state_json):
            try:
                if p.exists():
                    p.unlink()
            except Exception:
                pass

    # Load state if exists
    state = _read_json(state_json) if state_json.exists() else None
    if state is None:
        state = {
            "created_at": utc_now_iso(),
            "updated_at": utc_now_iso(),
            "signature": _points_signature_v2(bbox=bbox, point_type=point_type, start_id=start_id),
            "max_scanned_id": start_id - 1,
            "key_label": key_label,
        }

    # Backward-compat: migrate progress field
    max_scanned = _state_progress(state, default=start_id - 1)
    state["max_scanned_id"] = int(max_scanned)

    # If points CSV is missing but JSONL cache exists, rebuild points CSV from cache (fast local)
    if reuse_cache and (not points_csv.exists()) and cache_jsonl.exists():
        n_rows, max_seen = import_cache_jsonl_to_points_csv(
            cache_jsonl=cache_jsonl, points_csv=points_csv, bbox=bbox, point_type=point_type
        )
        if n_rows > 0:
            print(f"[CACHE] rebuilt points CSV from JSONL: {points_csv} (rows={n_rows})")
        if max_seen > state.get("max_scanned_id", start_id - 1):
            # best-effort: if cache contains ids higher than state, update state
            state["max_scanned_id"] = int(max(state["max_scanned_id"], max_seen))
            max_scanned = int(state["max_scanned_id"])

    # If already scanned enough and CSV exists -> reuse
    if reuse_cache and points_csv.exists() and int(max_scanned) >= int(end_id):
        print(f"[CACHE] reuse points (already scanned to {max_scanned} >= {end_id}) | {points_csv.name}")
        return points_csv

    # Load existing ids to avoid duplicates on append
    existing_ids: set = set()
    if points_csv.exists():
        try:
            df_existing = pd.read_csv(points_csv, usecols=["id"])
            existing_ids = set(int(x) for x in df_existing["id"].dropna().astype(int).tolist())
        except Exception:
            existing_ids = set()

    # Ensure files exist with header if we append
    if not points_csv.exists():
        pd.DataFrame(columns=["id", "lon", "lat", "title", "address", "point_type", "fractions_raw", "fractions"]).to_csv(
            points_csv, index=False, encoding="utf-8"
        )

    if write_raw_cache and (not cache_jsonl.exists()):
        # start a new JSONL (even if we write only filtered rows)
        cache_jsonl.write_text("", encoding="utf-8")

    limiter = GlobalRateLimiter(rate_limit_rps)

    # Worker: fetch, parse; return (pid, exists, row_filtered_or_none, raw_obj_or_none)
    def _fetch_one(pid: int) -> Tuple[int, bool, Optional[Dict[str, object]], Optional[dict]]:
        sess = _get_session()
        for attempt in range(int(retries) + 1):
            limiter.wait()
            exists, data = recyclemap_get_point(pid, sess, timeout=timeout_s)
            if exists:
                row = parse_recyclemap_row(data) if data else None
                if row is None:
                    return pid, True, None, data
                # Filter by bbox
                try:
                    lon = float(row["lon"])
                    lat = float(row["lat"])
                except Exception:
                    return pid, True, None, data

                if not bbox.contains(lon, lat):
                    return pid, True, None, data

                # Filter by point_type if available
                if point_type:
                    pt = str(row.get("point_type") or "").strip()
                    if pt and pt != point_type:
                        return pid, True, None, data

                return pid, True, row, data
            # not exists: retry with backoff
            if attempt < int(retries):
                time.sleep(min(2.0 ** attempt + random.random() * 0.2, 5.0))
                continue
            return pid, False, None, None

    # Scan loop in chunks (sequential chunks; concurrent inside)
    scan_start = max(int(max_scanned) + 1, int(start_id))
    if scan_start > end_id:
        # nothing to do (maybe CSV missing but should have been handled above)
        print(f"[SCAN] nothing to scan (scan_start={scan_start} > end_id={end_id})")
        return points_csv

    print(f"[SCAN] key={key_label} | range={scan_start}..{end_id} | workers={scan_workers} | rps={rate_limit_rps}")

    from concurrent.futures import ThreadPoolExecutor, as_completed

    consecutive_nonexist = 0
    max_scanned_local = int(max_scanned)

    # Open output streams once for speed
    csv_buffer_rows: List[Dict[str, object]] = []
    jsonl_buffer_lines: List[str] = []

    def _flush_buffers() -> None:
        nonlocal csv_buffer_rows, jsonl_buffer_lines, existing_ids
        if csv_buffer_rows:
            df_new = pd.DataFrame(csv_buffer_rows)
            # drop duplicates against existing ids
            if "id" in df_new.columns:
                df_new = df_new[~df_new["id"].astype(int).isin(existing_ids)]
            if len(df_new) > 0:
                # append (no header)
                df_new.to_csv(points_csv, mode="a", header=False, index=False, encoding="utf-8")
                existing_ids.update(int(x) for x in df_new["id"].astype(int).tolist())
            csv_buffer_rows = []

        if write_raw_cache and jsonl_buffer_lines:
            with cache_jsonl.open("a", encoding="utf-8") as jf:
                jf.write("\n".join(jsonl_buffer_lines) + "\n")
            jsonl_buffer_lines = []

    for chunk_lo in range(scan_start, end_id + 1, int(scan_chunk)):
        chunk_hi = min(end_id, chunk_lo + int(scan_chunk) - 1)
        ids = list(range(chunk_lo, chunk_hi + 1))

        results: Dict[int, Tuple[bool, Optional[Dict[str, object]], Optional[dict]]] = {}

        with ThreadPoolExecutor(max_workers=int(scan_workers)) as ex:
            futs = {ex.submit(_fetch_one, pid): pid for pid in ids}
            for fut in as_completed(futs):
                pid = futs[fut]
                try:
                    pid2, exists, row, raw = fut.result()
                except Exception:
                    pid2, exists, row, raw = pid, False, None, None
                results[pid2] = (exists, row, raw)

        # Process in order to compute consecutive misses by id sequence
        for pid in ids:
            exists, row, raw = results.get(pid, (False, None, None))

            if exists:
                consecutive_nonexist = 0
            else:
                consecutive_nonexist += 1

            # record filtered row
            if row is not None:
                csv_buffer_rows.append(row)
                if write_raw_cache:
                    # store a compact row (not the whole raw payload) -> smaller & faster
                    jsonl_buffer_lines.append(json.dumps({"id": row["id"], "lon": row["lon"], "lat": row["lat"], "point_type": row.get("point_type",""), "fractions_raw": row.get("fractions_raw",""), "fractions": row.get("fractions",""), "title": row.get("title",""), "address": row.get("address","")}, ensure_ascii=False))

            max_scanned_local = max(max_scanned_local, pid)

        # Update state after each chunk
        state["updated_at"] = utc_now_iso()
        state["max_scanned_id"] = int(max_scanned_local)
        state["key_label"] = key_label
        state_json.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")

        # Flush buffers periodically
        _flush_buffers()

        print(f"[SCAN] scanned {chunk_lo}-{chunk_hi} | max_scanned={max_scanned_local} | new_rows_total={len(existing_ids)} | nonexist_streak={consecutive_nonexist}")

        # Early stop only if we have a long streak of truly non-existent IDs (NOT out-of-bbox)
        if int(stop_after_misses) > 0 and consecutive_nonexist >= int(stop_after_misses):
            print(f"[SCAN] early stop: non-existent streak reached {consecutive_nonexist} (>= {stop_after_misses}) at id={chunk_hi}")
            break

    # Final dedupe (safety)
    try:
        df_final = pd.read_csv(points_csv)
        if "id" in df_final.columns:
            df_final = df_final.drop_duplicates(subset=["id"])
        df_final.to_csv(points_csv, index=False, encoding="utf-8")
    except Exception:
        pass

    return points_csv


# -----------------------------
# Projection & grid
# -----------------------------

def make_transformers(center_lon: float, center_lat: float) -> Tuple["Transformer", "Transformer"]:
    """
    Metric transformer (WGS84 -> local AEQD meters) and inverse.
    AEQD reduces distortion on city scale.
    """
    if CRS is None or Transformer is None:
        raise RuntimeError("pyproj is required. Install: pip install pyproj")
    crs_wgs = CRS.from_epsg(4326)
    crs_aeqd = CRS.from_proj4(f"+proj=aeqd +lat_0={center_lat} +lon_0={center_lon} +datum=WGS84 +units=m +no_defs")
    fwd = Transformer.from_crs(crs_wgs, crs_aeqd, always_xy=True)
    inv = Transformer.from_crs(crs_aeqd, crs_wgs, always_xy=True)
    return fwd, inv


def build_grid(bbox: BBox, step_m: float, fwd: "Transformer", inv: "Transformer") -> Tuple["np.ndarray", "np.ndarray"]:
    """
    Regular grid within bbox:
      - returns grid_xy in meters (N x 2)
      - returns grid_ll as lon/lat (N x 2)
    """
    if np is None:
        raise RuntimeError("numpy is required. Install: pip install numpy")
    # Project bbox corners to meters
    x0, y0 = fwd.transform(bbox.lon_min, bbox.lat_min)
    x1, y1 = fwd.transform(bbox.lon_max, bbox.lat_max)
    xmin, xmax = (min(x0, x1), max(x0, x1))
    ymin, ymax = (min(y0, y1), max(y0, y1))

    xs = np.arange(xmin, xmax + float(step_m), float(step_m))
    ys = np.arange(ymin, ymax + float(step_m), float(step_m))
    # Mesh
    xx, yy = np.meshgrid(xs, ys)
    grid_xy = np.c_[xx.ravel(), yy.ravel()]

    # Back to lon/lat
    lons, lats = inv.transform(grid_xy[:, 0], grid_xy[:, 1])
    grid_ll = np.c_[lons, lats]
    return grid_xy, grid_ll


def nearest_distances_m(grid_xy: "np.ndarray", pts_xy: "np.ndarray") -> "np.ndarray":
    """Distance (meters) from each grid point to nearest point. Returns inf if pts empty."""
    if np is None:
        raise RuntimeError("numpy is required. Install: pip install numpy")
    if pts_xy is None or len(pts_xy) == 0:
        return np.full(len(grid_xy), np.inf, dtype=float)
    if cKDTree is not None:
        tree = cKDTree(pts_xy)
        d, _ = tree.query(grid_xy, k=1)
        return d.astype(float)
    # Fallback: chunked brute force (slower)
    out = np.empty(len(grid_xy), dtype=float)
    chunk = 2000
    for i in range(0, len(grid_xy), chunk):
        g = grid_xy[i:i+chunk]
        # squared distances: (g[:,None,:]-pts[None,:,:])^2
        dd = ((g[:, None, :] - pts_xy[None, :, :]) ** 2).sum(axis=2)
        out[i:i+chunk] = np.sqrt(dd.min(axis=1))
    return out


# -----------------------------
# OSM exclusions (optional)
# -----------------------------

def load_osm_exclusions(
    bbox: BBox,
    data_dir: Path,
    *,
    reuse_cache: bool = True,
    refresh: bool = False,
) -> List["BaseGeometry"]:
    """
    Download or load cached OSM polygons to exclude from analysis area.
    Cache is stored as JSON with list of WKT geometries.
    """
    if ox is None or ShpPoint is None or _shp_wkt is None:
        print("[WARN] OSM exclusions requested but osmnx/shapely not available. Skipping exclusions.")
        return []

    safe_mkdir(data_dir)
    cache_key = _stable_hash({"bbox": bbox.as_tuple_lrbt(), "tags": OSM_EXCLUDE_TAGS}, n=10)
    cache_file = data_dir / f"osm_exclusions__{cache_key}.json"

    if reuse_cache and cache_file.exists() and not refresh:
        try:
            obj = json.loads(cache_file.read_text(encoding="utf-8"))
            wkts = obj.get("wkt", [])
            polys = []
            for w in wkts:
                try:
                    g = _shp_wkt.loads(w)
                    polys.append(g)
                except Exception:
                    continue
            print(f"[OSM] loaded exclusions from cache: {cache_file.name} (polys={len(polys)})")
            return polys
        except Exception:
            pass

    # Fetch from OSM (osmnx API differs between 1.x and 2.x)
    bbox_lrbt = bbox.as_tuple_lrbt()  # (left, bottom, right, top) = (west, south, east, north)
    try:
        if hasattr(ox, "features_from_bbox"):
            # osmnx 2.x: features_from_bbox(bbox, tags)
            try:
                gdf = ox.features_from_bbox(bbox_lrbt, tags=OSM_EXCLUDE_TAGS)  # type: ignore
            except TypeError:
                try:
                    gdf = ox.features_from_bbox(bbox=bbox_lrbt, tags=OSM_EXCLUDE_TAGS)  # type: ignore
                except TypeError:
                    # osmnx 1.x legacy signature
                    north, south, east, west = bbox.lat_max, bbox.lat_min, bbox.lon_max, bbox.lon_min
                    gdf = ox.features_from_bbox(north=north, south=south, east=east, west=west, tags=OSM_EXCLUDE_TAGS)  # type: ignore
        else:
            # older osmnx: geometries_from_bbox
            north, south, east, west = bbox.lat_max, bbox.lat_min, bbox.lon_max, bbox.lon_min
            try:
                gdf = ox.geometries_from_bbox(north=north, south=south, east=east, west=west, tags=OSM_EXCLUDE_TAGS)  # type: ignore
            except TypeError:
                gdf = ox.geometries_from_bbox(north, south, east, west, tags=OSM_EXCLUDE_TAGS)  # type: ignore
    except Exception as e:
        print(f"[WARN] OSM fetch failed: {e}")
        return []

    polys: List[BaseGeometry] = []
    try:
        geoms = list(gdf.geometry)
    except Exception:
        geoms = []

    for g in geoms:
        if g is None:
            continue
        # keep polygons and multipolygons; points/lines are ignored
        gt = getattr(g, "geom_type", "")
        if gt in ("Polygon", "MultiPolygon"):
            polys.append(g)

    # Cache
    try:
        cache_file.write_text(json.dumps({"created_at": utc_now_iso(), "wkt": [p.wkt for p in polys]}, ensure_ascii=False), encoding="utf-8")
        print(f"[OSM] saved exclusions cache: {cache_file.name} (polys={len(polys)})")
    except Exception:
        pass

    return polys


def filter_grid_excluding_polygons(grid_ll: "np.ndarray", exclusion_polys: List["BaseGeometry"]) -> "np.ndarray":
    """
    Return boolean mask for grid points to keep (True=keep).

    IMPORTANT: compatible with both Shapely 1.x and Shapely 2.x STRtree behavior:
      - Shapely 1.x: STRtree.query(point) -> list[geometry]
      - Shapely 2.x: STRtree.query(point) -> numpy array of integer indices

    """
    if np is None:
        raise RuntimeError("numpy is required. Install: pip install numpy")
    if not exclusion_polys:
        return np.ones(len(grid_ll), dtype=bool)

    if ShpPoint is None or STRtree is None:
        # Fallback: very slow O(n*m)
        keep = np.ones(len(grid_ll), dtype=bool)
        for i, (lon, lat) in enumerate(grid_ll):
            try:
                p = ShpPoint(float(lon), float(lat))  # type: ignore
            except Exception:
                continue
            for poly in exclusion_polys:
                try:
                    # covers() includes boundary; good for exclusion masks
                    if poly.covers(p):
                        keep[i] = False
                        break
                except Exception:
                    continue
        return keep

    tree = STRtree(exclusion_polys)
    keep = np.ones(len(grid_ll), dtype=bool)

    for i, (lon, lat) in enumerate(grid_ll):
        try:
            p = ShpPoint(float(lon), float(lat))
        except Exception:
            continue

        try:
            candidates = tree.query(p)
        except Exception:
            candidates = exclusion_polys

        # Shapely 2.x: indices
        try:
            if hasattr(candidates, "__len__") and len(candidates) > 0 and isinstance(candidates[0], (int, np.integer)):
                cand_geoms = (exclusion_polys[int(j)] for j in candidates)
            else:
                cand_geoms = candidates
        except Exception:
            cand_geoms = candidates

        for poly in cand_geoms:
            try:
                if poly.covers(p):
                    keep[i] = False
                    break
            except Exception:
                continue

    return keep

    tree = STRtree(exclusion_polys)
    keep = np.ones(len(grid_ll), dtype=bool)
    for i, (lon, lat) in enumerate(grid_ll):
        p = ShpPoint(float(lon), float(lat))
        # query candidates by bbox
        try:
            candidates = tree.query(p)
        except Exception:
            candidates = exclusion_polys
        for poly in candidates:
            try:
                if poly.contains(p):
                    keep[i] = False
                    break
            except Exception:
                continue
    return keep


# -----------------------------
# Metrics helpers (finite-only aggregation)
# -----------------------------

def summarize_distances(dist_m: "np.ndarray", radius_m: float) -> Dict[str, object]:
    """
    Compute robust distance stats:
    - coverage_share / white_spot_share computed on all cells (inf counts as not covered)
    - mean/median/p95/max computed ONLY on finite distances
    - also reports share_no_points (inf distances)
    """
    if np is None:
        raise RuntimeError("numpy is required. Install: pip install numpy")
    dist_arr = np.asarray(dist_m, dtype=float)
    finite_mask = np.isfinite(dist_arr)
    dist_fin = dist_arr[finite_mask]

    out: Dict[str, object] = {
        "cells_total": int(len(dist_arr)),
        "cells_no_points": int((~finite_mask).sum()),
        "share_no_points": float((~finite_mask).mean()) if len(dist_arr) else 0.0,
        "coverage_share": float((dist_arr <= float(radius_m)).mean()) if len(dist_arr) else 0.0,
        "white_spot_share": float((dist_arr > float(radius_m)).mean()) if len(dist_arr) else 0.0,
    }

    if dist_fin.size > 0:
        out.update(
            {
                "mean_dist_m": float(dist_fin.mean()),
                "median_dist_m": float(np.median(dist_fin)),
                "p95_dist_m": float(np.percentile(dist_fin, 95)),
                "max_dist_m": float(dist_fin.max()),
            }
        )
    else:
        out.update({"mean_dist_m": None, "median_dist_m": None, "p95_dist_m": None, "max_dist_m": None})
    return out


# -----------------------------
# White-spot clustering + recommendations
# -----------------------------

def cluster_white_spots(
    grid_xy: "np.ndarray",
    grid_ll: "np.ndarray",
    distances_m: "np.ndarray",
    step_m: float,
    radius_m: float,
    inv: "Transformer",
    min_cluster_cells: int = 4,
    connectivity: int = 8,
) -> List[Dict[str, object]]:
    """
    Cluster white-spot cells (dist > radius_m) on regular grid using BFS.
    Returns list of clusters sorted by score desc.
    """
    if np is None:
        raise RuntimeError("numpy is required. Install: pip install numpy")
    assert connectivity in (4, 8)

    ws_mask = np.asarray(distances_m, dtype=float) > float(radius_m)
    if not ws_mask.any():
        return []

    # Map each grid cell to integer indices on regular grid:
    xs = grid_xy[:, 0]
    ys = grid_xy[:, 1]
    xmin = xs.min()
    ymin = ys.min()
    ix = np.round((xs - xmin) / float(step_m)).astype(int)
    iy = np.round((ys - ymin) / float(step_m)).astype(int)

    # dictionary from (ix,iy)->index
    idx_map: Dict[Tuple[int, int], int] = {}
    for i in range(len(grid_xy)):
        if ws_mask[i]:
            idx_map[(int(ix[i]), int(iy[i]))] = i

    visited = set()
    clusters: List[Dict[str, object]] = []

    # neighbor offsets
    neigh = [(-1, 0), (1, 0), (0, -1), (0, 1)]
    if connectivity == 8:
        neigh += [(-1, -1), (-1, 1), (1, -1), (1, 1)]

    for key, start_idx in list(idx_map.items()):
        if key in visited:
            continue
        # BFS
        q = [key]
        visited.add(key)
        members: List[int] = []
        while q:
            cx, cy = q.pop()
            mi = idx_map.get((cx, cy))
            if mi is not None:
                members.append(mi)
            for dx, dy in neigh:
                nk = (cx + dx, cy + dy)
                if nk in idx_map and nk not in visited:
                    visited.add(nk)
                    q.append(nk)

        if len(members) < int(min_cluster_cells):
            continue

        dvals = np.asarray(distances_m)[members]
        mean_d = float(np.mean(dvals[np.isfinite(dvals)])) if np.isfinite(dvals).any() else None
        max_d = float(np.max(dvals[np.isfinite(dvals)])) if np.isfinite(dvals).any() else None
        n_cells = int(len(members))
        area_m2 = n_cells * (float(step_m) ** 2)
        area_km2 = float(area_m2 / 1e6)

        # recommended point: deepest cell (max distance); if distances finite
        if max_d is not None:
            deepest_local = members[int(np.argmax(dvals))]
            rx, ry = float(grid_xy[deepest_local, 0]), float(grid_xy[deepest_local, 1])
        else:
            # fallback to centroid of members
            rx = float(np.mean(grid_xy[members, 0]))
            ry = float(np.mean(grid_xy[members, 1]))

        lon_r, lat_r = inv.transform(rx, ry)

        # score: emphasize area + depth
        depth_factor = 1.0
        if mean_d is not None and radius_m > 0:
            depth_factor = float(mean_d) / float(radius_m)
        score = float(area_km2 * depth_factor)

        clusters.append(
            {
                "n_cells": n_cells,
                "area_km2": area_km2,
                "mean_distance_m": mean_d,
                "max_distance_m": max_d,
                "score": score,
                "recommended_lon": float(lon_r),
                "recommended_lat": float(lat_r),
            }
        )

    clusters.sort(key=lambda x: float(x.get("score") or 0.0), reverse=True)
    return clusters


def reverse_geocode(lat: float, lon: float, *, language: str = "ru", min_delay_s: float = 1.0) -> Optional[str]:
    """Reverse geocode via Nominatim. Use carefully (rate-limited)."""
    if requests is None:
        return None
    time.sleep(max(float(min_delay_s), 0.0))
    url = "https://nominatim.openstreetmap.org/reverse"
    params = {"format": "jsonv2", "lat": str(lat), "lon": str(lon), "zoom": "18", "addressdetails": "0", "accept-language": language}
    headers = {"User-Agent": "rso-school-project/1.0"}
    try:
        r = requests.get(url, params=params, headers=headers, timeout=30)
        if r.status_code != 200:
            return None
        js = r.json()
        return js.get("display_name")
    except Exception:
        return None


def write_recommendations_outputs(out_dir: Path, metrics: dict, recs_by_type: Dict[str, List[Dict[str, object]]]) -> None:
    if pd is None:
        raise RuntimeError("pandas required. Install: pip install pandas")
    safe_mkdir(out_dir)

    # flat table
    rows: List[Dict[str, object]] = []
    for wt, recs in recs_by_type.items():
        for i, r in enumerate(recs, start=1):
            rows.append(
                {
                    "waste_type": wt,
                    "rank": i,
                    "recommended_lat": r.get("recommended_lat"),
                    "recommended_lon": r.get("recommended_lon"),
                    "area_km2": r.get("area_km2"),
                    "mean_distance_m": r.get("mean_distance_m"),
                    "max_distance_m": r.get("max_distance_m"),
                    "score": r.get("score"),
                    "note": r.get("note", ""),
                    "approx_address": r.get("approx_address", ""),
                }
            )
    df = pd.DataFrame(rows)
    df.to_csv(out_dir / "recommendations.csv", index=False, encoding="utf-8")

    for wt in recs_by_type:
        df_t = df[df["waste_type"] == wt]
        key = re.sub(r"[^0-9A-Za-zА-Яа-я]+", "_", wt).strip("_")
        df_t.to_csv(out_dir / f"recommendations__{key}.csv", index=False, encoding="utf-8")

    (out_dir / "recommendations.json").write_text(json.dumps(metrics.get("recommendations", {}), ensure_ascii=False, indent=2), encoding="utf-8")

    # Text report
    lines: List[str] = []
    lines.append("# Авто‑отчёт: рекомендации по размещению новых пунктов РСО\n")
    lines.append(f"Дата: {utc_now_iso()}\n")
    lines.append(f"Радиус доступности: {metrics.get('radius_m')} м\n")
    lines.append(f"Шаг сетки: {metrics.get('grid_step_m')} м\n")
    lines.append(f"Площадь анализируемой (доступной) территории: {metrics.get('area_km2_eligible'):.2f} км²\n\n")

    for wt, recs in recs_by_type.items():
        lines.append(f"## {wt}\n")
        if not recs:
            lines.append("- Рекомендаций нет (возможно, покрытие хорошее или данных недостаточно).\n\n")
            continue
        for i, r in enumerate(recs, start=1):
            lat = r.get("recommended_lat")
            lon = r.get("recommended_lon")
            area = r.get("area_km2")
            mean_d = r.get("mean_distance_m")
            max_d = r.get("max_distance_m")
            note = r.get("note", "")
            addr = r.get("approx_address", "")
            lines.append(f"{i}. Точка: {lat:.6f}, {lon:.6f}\n")
            lines.append(f"   - Площадь белого пятна: {_fmt_float(area, 3)} км²\n")
            lines.append(f"   - Средняя дистанция: {_fmt_dist_m(mean_d)} м\n")
            lines.append(f"   - Максимальная дистанция: {_fmt_dist_m(max_d)} м\n")
            if addr:
                lines.append(f"   - Адрес (примерно): {addr}\n")
            if note:
                lines.append(f"   - Примечание: {note}\n")
        lines.append("\n")

    (out_dir / "recommendations_report.md").write_text("".join(lines), encoding="utf-8")
    # plaintext too
    (out_dir / "recommendations_report.txt").write_text("".join(lines).replace("# ", "").replace("## ", ""), encoding="utf-8")
    # minimal HTML
    html = "<html><head><meta charset='utf-8'><title>Recommendations</title></head><body><pre>" + sanitize_text("".join(lines)) + "</pre></body></html>"
    (out_dir / "recommendations_report.html").write_text(html, encoding="utf-8")


# -----------------------------
# Folium HTML patcher (fix object spread + octal escapes)
# -----------------------------


def patch_folium_html_for_compat(
    html_path: Path,
    prefer_unpkg_leaflet: bool = True,
    remove_leaflet_prefix: bool = True,
) -> None:
    """
    Make Folium HTML compatible with stricter/older JS engines and some school/corporate environments:

      1) Removes object spread usage "...{ ... }" inside map options (can break older JS parsers)
      2) Fixes illegal octal escapes in template strings: "\\2" -> "/2" (addresses like "32\\2")
      3) Optionally swaps Leaflet CDN from jsDelivr to unpkg (sometimes works better with tracking protection)
      4) Optionally removes Leaflet attribution prefix/link (keeps OSM attribution!)

    Notes:
      - Removing Leaflet prefix is done via JS: map.attributionControl.setPrefix('')
      - We DO NOT remove OpenStreetMap attribution (it should stay).
    """
    try:
        lines = html_path.read_text(encoding="utf-8", errors="ignore").splitlines()
    except Exception:
        return

    out_lines: List[str] = []
    spread_open = 0

    # 1) remove "...{"
    for line in lines:
        if "...{" in line:
            # remove token, but keep the rest
            new_line = line.replace("...{", "")
            if new_line.strip():
                out_lines.append(new_line)
            spread_open += 1
            continue

        # remove one matching closing brace for each "...{"
        if spread_open > 0 and re.match(r"^\s*\}\s*,?\s*$", line):
            spread_open -= 1
            continue

        out_lines.append(line)

    txt = "\n".join(out_lines)

    # 2) Fix octal escapes like "\2" (commonly appears in addresses like "32\2")
    txt = re.sub(r"\\([0-9])", r"/\1", txt)

    # 3) Swap Leaflet CDN if requested
    if prefer_unpkg_leaflet:
        txt = txt.replace(
            "https://cdn.jsdelivr.net/npm/leaflet@1.9.3/dist/leaflet.js",
            "https://unpkg.com/leaflet@1.9.3/dist/leaflet.js",
        ).replace(
            "https://cdn.jsdelivr.net/npm/leaflet@1.9.3/dist/leaflet.css",
            "https://unpkg.com/leaflet@1.9.3/dist/leaflet.css",
        )

    # 4) Remove Leaflet prefix/link in attribution (keep OSM attribution)
    if remove_leaflet_prefix:
        m = re.search(r"var\s+(map_[A-Za-z0-9_]+)\s*=\s*L\.map\(", txt)
        if m:
            map_var = m.group(1)
            if "attributionControl.setPrefix" not in txt:
                inject = (
                    "\n<script>\n"
                    f"try {{ {map_var}.attributionControl.setPrefix(''); }} catch(e) {{}}\n"
                    "</script>\n"
                )
                # insert before </body> if possible
                if "</body>" in txt:
                    txt = txt.replace("</body>", inject + "</body>")
                else:
                    txt = txt + inject

    try:
        html_path.write_text(txt, encoding="utf-8")
    except Exception:
        pass


def _safe_slug(s: str) -> str:
    """Safe slug for filenames (keeps Cyrillic, replaces other chars)."""
    s = str(s or "").strip()
    s = re.sub(r"[^\wА-Яа-я0-9]+", "_", s, flags=re.UNICODE).strip("_")
    return s or "x"


def _build_geojson_with_properties(
    districts_geojson: dict,
    props_by_normname: Dict[str, Dict[str, object]],
) -> dict:
    """
    Returns a *new* GeoJSON object where each feature gets extra properties from props_by_normname
    based on normalized district name (feature.properties.NAME).
    """
    gj = json.loads(json.dumps(districts_geojson, ensure_ascii=False))
    feats = gj.get("features", [])
    for f in feats:
        p = f.get("properties", {}) or {}
        name = p.get("NAME", "") or ""
        key = normalize_text(str(name))
        extra = props_by_normname.get(key)
        if extra:
            for k, v in extra.items():
                p[k] = v
        f["properties"] = p
    return gj


def _color_for_value(val: Optional[float], vmin: float, vmax: float, cmap_name: str = "YlOrRd") -> str:
    """
    Map a numeric value to a color (hex) using a branca colormap if available.
    """
    if val is None or (isinstance(val, float) and (not math.isfinite(val))):
        return "#cccccc"
    v = float(val)
    if vmax <= vmin:
        vmax = vmin + 1.0

    try:
        from branca.colormap import linear  # type: ignore
        cmap = getattr(linear, cmap_name, linear.YlOrRd_09)
        # branca colormap objects are callables that return hex
        cm = cmap.scale(vmin, vmax)
        return cm(v)
    except Exception:
        # fallback: simple grayscale
        t = (v - vmin) / (vmax - vmin)
        t = max(0.0, min(1.0, t))
        g = int(255 * (1.0 - t))
        return f"#{g:02x}{g:02x}{g:02x}"


def add_district_choropleths_to_map(
    m: "folium.Map",
    districts_geojson_path: Path,
    out_dir: Path,
    waste_types: List[str],
    radius_m: float,
    save_images: bool = True,
) -> None:
    """
    Adds per-district choropleth layers to an existing Folium map.

    Layers added (for each waste type):
      - "Хороплет (покрытие): <тип>"     colored by coverage_share (% of district area within radius_m)
      - "Хороплет (точек на 10 тыс.): <тип>" colored by points_per_10k

    Also saves static PNG images for each choropleth (optional) to:
      out_dir / "choropleth_images" / *.png
    """
    if folium is None or pd is None:
        return

    # Need district per-type metrics
    df_t_path = out_dir / "district_accessibility__per_type.csv"
    df_all_path = out_dir / "district_accessibility__all.csv"
    if not df_t_path.exists() or not df_all_path.exists():
        return

    try:
        districts_geojson = json.loads(districts_geojson_path.read_text(encoding="utf-8"))
    except Exception:
        return

    df_t = pd.read_csv(df_t_path)
    df_all = pd.read_csv(df_all_path)

    if df_t.empty or df_all.empty:
        return

    # population map (same for all types)
    pop_by = {normalize_text(r["district"]): int(r["population"]) if not pd.isna(r.get("population")) else None for _, r in df_all.iterrows()}

    # Prepare static image output folder
    img_dir = out_dir / "choropleth_images"
    if save_images:
        safe_mkdir(img_dir)

    # Helper: build one layer (style + tooltip)
    def _add_layer(
        gj_props: dict,
        layer_name: str,
        metric_field: str,
        cmap_name: str,
        vmin: float,
        vmax: float,
        tooltip_aliases: List[str],
        tooltip_fields: List[str],
    ) -> None:
        fg = folium.FeatureGroup(name=layer_name, show=False)

        def style_func(feature):
            p = feature.get("properties", {}) or {}
            val = p.get(metric_field)
            return {
                "fillColor": _color_for_value(val, vmin=vmin, vmax=vmax, cmap_name=cmap_name),
                "color": "#444444",
                "weight": 1,
                "fillOpacity": 0.70,
            }

        try:
            tooltip = folium.GeoJsonTooltip(fields=tooltip_fields, aliases=tooltip_aliases, localize=True, sticky=False)
        except Exception:
            tooltip = None

        folium.GeoJson(
            data=gj_props,
            name=layer_name,
            style_function=style_func,
            tooltip=tooltip,
        ).add_to(fg)

        fg.add_to(m)

    # Create layers per type
    for wt in waste_types:
        df_w = df_t[df_t["waste_type"] == wt].copy()
        if df_w.empty:
            continue

        # Map props by district
        props_map: Dict[str, Dict[str, object]] = {}
        vals_cov: List[float] = []
        vals_pp: List[float] = []
        for _, r in df_w.iterrows():
            dname = str(r.get("district", ""))
            key = normalize_text(dname)
            cov = r.get("coverage_share")
            cov_pct = float(cov) * 100.0 if cov is not None and not pd.isna(cov) else None
            pp10k = r.get("points_per_10k")
            pp10k = float(pp10k) if pp10k is not None and not pd.isna(pp10k) else None
            npt = r.get("n_points_type_in_district")
            try:
                npt = int(npt) if npt is not None and not pd.isna(npt) else 0
            except Exception:
                npt = 0
            pop = pop_by.get(key)

            if cov_pct is not None and math.isfinite(float(cov_pct)):
                vals_cov.append(float(cov_pct))
            if pp10k is not None and math.isfinite(float(pp10k)):
                vals_pp.append(float(pp10k))

            type_key = _safe_slug(wt).lower()
            props_map[key] = {
                "population": pop,
                f"{type_key}_n": npt,
                f"{type_key}_pp10k": (round(pp10k, 3) if isinstance(pp10k, float) else None),
                f"{type_key}_covpct": (round(cov_pct, 1) if isinstance(cov_pct, float) else None),
            }

        # Build geojson with those properties
        gj_w = _build_geojson_with_properties(districts_geojson, props_map)

        # Ranges
        cov_vmin, cov_vmax = 0.0, 100.0
        pp_vmin = 0.0
        if vals_pp:
            try:
                import numpy as _np  # type: ignore
                pp_vmax = float(_np.percentile(_np.asarray(vals_pp, dtype=float), 95))
            except Exception:
                pp_vmax = float(max(vals_pp))
            pp_vmax = max(pp_vmax, 0.1)
        else:
            pp_vmax = 1.0

        type_key = _safe_slug(wt).lower()
        # Coverage layer
        _add_layer(
            gj_props=gj_w,
            layer_name=f"Хороплет (покрытие): {wt} (R={int(radius_m)}м)",
            metric_field=f"{type_key}_covpct",
            cmap_name="YlGn_09",
            vmin=cov_vmin,
            vmax=cov_vmax,
            tooltip_aliases=["Район", "АО", "Население", "Пунктов", "Пунктов на 10 тыс.", f"Покрытие R={int(radius_m)}м, %"],
            tooltip_fields=["NAME", "ABBREV_AO", "population", f"{type_key}_n", f"{type_key}_pp10k", f"{type_key}_covpct"],
        )

        # Points-per-10k layer
        _add_layer(
            gj_props=gj_w,
            layer_name=f"Хороплет (точек на 10 тыс.): {wt}",
            metric_field=f"{type_key}_pp10k",
            cmap_name="YlOrRd_09",
            vmin=pp_vmin,
            vmax=pp_vmax,
            tooltip_aliases=["Район", "АО", "Население", "Пунктов", "Пунктов на 10 тыс.", f"Покрытие R={int(radius_m)}м, %"],
            tooltip_fields=["NAME", "ABBREV_AO", "population", f"{type_key}_n", f"{type_key}_pp10k", f"{type_key}_covpct"],
        )

        # Save static PNGs
        if save_images:
            try:
                save_district_choropleth_images(
                    districts_geojson=districts_geojson,
                    props_by_normname=props_map,
                    metric_field=f"{type_key}_covpct",
                    title=f"{wt}: покрытие в радиусе {int(radius_m)} м, %",
                    out_png=img_dir / f"choropleth_coverage_share_{type_key}.png",
                    vmin=cov_vmin,
                    vmax=cov_vmax,
                    cmap_name="YlGn",
                )
                save_district_choropleth_images(
                    districts_geojson=districts_geojson,
                    props_by_normname=props_map,
                    metric_field=f"{type_key}_pp10k",
                    title=f"{wt}: пунктов на 10 тыс. жителей",
                    out_png=img_dir / f"choropleth_points_per_10k_{type_key}.png",
                    vmin=pp_vmin,
                    vmax=pp_vmax,
                    cmap_name="YlOrRd",
                )
            except Exception as e:
                print(f"[WARN] Failed to save choropleth images for {wt}: {e}")


def save_district_choropleth_images(
    districts_geojson: dict,
    props_by_normname: Dict[str, Dict[str, object]],
    metric_field: str,
    title: str,
    out_png: Path,
    vmin: float,
    vmax: float,
    cmap_name: str = "YlOrRd",
) -> None:
    """
    Save a simple static choropleth PNG using matplotlib (no basemap).
    Works without geopandas; uses shapely shapes.

    If matplotlib is not installed, silently does nothing.
    """
    try:
        import matplotlib.pyplot as plt  # type: ignore
        from matplotlib.collections import PatchCollection  # type: ignore
        from matplotlib.patches import Polygon as MplPolygon  # type: ignore
        import numpy as _np  # type: ignore
    except Exception:
        return

    if ShpShape is None:
        return

    patches = []
    values = []

    for feat in districts_geojson.get("features", []):
        props = feat.get("properties", {}) or {}
        name = props.get("NAME", "") or ""
        key = normalize_text(str(name))
        extra = props_by_normname.get(key, {})
        val = extra.get(metric_field)
        if val is None or (isinstance(val, float) and (not math.isfinite(val))):
            v = _np.nan
        else:
            v = float(val)

        geom = feat.get("geometry")
        if not geom:
            continue
        try:
            g = ShpShape(geom)  # type: ignore
        except Exception:
            continue

        def _add_poly(poly):
            try:
                x, y = poly.exterior.coords.xy
                coords = list(zip(x, y))
                patches.append(MplPolygon(coords, closed=True))
                values.append(v)
            except Exception:
                pass

        if getattr(g, "geom_type", "") == "Polygon":
            _add_poly(g)
        elif getattr(g, "geom_type", "") == "MultiPolygon":
            for poly in g.geoms:
                _add_poly(poly)

    if not patches:
        return

    fig, ax = plt.subplots(figsize=(7.5, 7.5))
    pc = PatchCollection(patches, cmap=getattr(plt.cm, cmap_name, plt.cm.YlOrRd), edgecolor="black", linewidths=0.15)
    arr = _np.asarray(values, dtype=float)
    pc.set_array(arr)
    pc.set_clim(vmin, vmax)
    ax.add_collection(pc)
    ax.autoscale_view()
    ax.set_aspect("equal", adjustable="box")
    ax.axis("off")
    cbar = fig.colorbar(pc, ax=ax, fraction=0.03, pad=0.01)
    cbar.ax.tick_params(labelsize=8)
    ax.set_title(title, fontsize=10)
    fig.savefig(str(out_png), dpi=220, bbox_inches="tight")
    plt.close(fig)


# -----------------------------
# Accessibility analysis (UPDATED)
# -----------------------------


# -----------------------------
# District-level accessibility (optional)
# -----------------------------

def _md_table(df: "pd.DataFrame", cols: List[str], n: int = 20) -> str:
    """Render a small DataFrame as a markdown table (no external deps)."""
    if df is None or df.empty:
        return "_нет данных_"
    cols2 = [c for c in cols if c in df.columns]
    df2 = df[cols2].head(int(n)).copy()
    lines = []
    lines.append("| " + " | ".join(cols2) + " |")
    lines.append("| " + " | ".join(["---"] * len(cols2)) + " |")
    for _, r in df2.iterrows():
        lines.append("| " + " | ".join(str(r[c]) for c in cols2) + " |")
    return "\n".join(lines)


def compute_district_accessibility(
    out_dir: Path,
    district_index: DistrictIndex,
    grid_district_idx: "np.ndarray",
    points_df: "pd.DataFrame",
    distances_all: "np.ndarray",
    dist_by_type: Dict[str, "np.ndarray"],
    waste_types: List[str],
    radius_m: float,
    grid_step_m: float,
    type_scheme: str,
    pop_by_district: Optional[Dict[str, Dict[str, object]]] = None,
    top_n: int = 5,
) -> Dict[str, object]:
    """
    Compute accessibility metrics per district (overall + per waste type).

    Writes:
      - district_accessibility__all.csv
      - district_accessibility__per_type.csv
      - district_rankings.md
    """
    if pd is None or np is None:
        raise RuntimeError("pandas and numpy are required. Install: pip install pandas numpy")

    n_d = len(district_index.districts)
    if n_d == 0:
        return {"enabled": False, "reason": "No districts loaded"}

    # grid -> district
    grid_didx = np.asarray(grid_district_idx, dtype=int)
    grid_counts = np.bincount(grid_didx, minlength=n_d) if grid_didx.size else np.zeros(n_d, dtype=int)
    eligible_area_km2 = (grid_counts.astype(float) * (float(grid_step_m) ** 2)) / 1e6

    # points -> district
    if "district_idx" not in points_df.columns:
        raise RuntimeError("points_df must contain 'district_idx' column")
    p_didx = points_df["district_idx"].to_numpy(dtype=int, copy=False)
    points_counts_all = np.bincount(p_didx, minlength=n_d) if p_didx.size else np.zeros(n_d, dtype=int)

    # population map (normalized district -> population)
    pop_map = pop_by_district or {}

    # supply counts by type (points located in district)
    frac_series = points_df.get("fractions_search", points_df.get("fractions", "")).fillna("").astype(str)
    counts_by_type: Dict[str, "np.ndarray"] = {}
    for wt in waste_types:
        mask = frac_series.apply(lambda s: point_accepts_type(str(s), wt, scheme=type_scheme)).to_numpy(dtype=bool)
        didx_sel = p_didx[mask]
        counts_by_type[wt] = np.bincount(didx_sel, minlength=n_d) if didx_sel.size else np.zeros(n_d, dtype=int)

    rows_all: List[Dict[str, object]] = []
    rows_t: List[Dict[str, object]] = []

    # precompute indices for each district (grid masks)
    # (Store as list of numpy arrays of indices - cheap for 125 districts)
    idx_by_d: List["np.ndarray"] = [np.where(grid_didx == i)[0] for i in range(n_d)]

    for i, d in enumerate(district_index.districts):
        name = d.name
        key = normalize_text(name)
        ao = d.abbrev_ao or d.ao
        pop = pop_map.get(key, {}).get("population") if pop_map else None
        pop = int(pop) if pop is not None else None

        idxs = idx_by_d[i]
        cells = int(idxs.size)
        area_km2 = float(eligible_area_km2[i])

        # Overall accessibility for residents of this district (nearest point can be anywhere in city)
        if cells > 0:
            stats = summarize_distances(distances_all[idxs], radius_m=radius_m)
        else:
            stats = {"cells_total": 0, "cells_no_points": 0, "share_no_points": 0.0, "coverage_share": 0.0, "white_spot_share": 0.0,
                     "mean_dist_m": None, "median_dist_m": None, "p95_dist_m": None, "max_dist_m": None}

        n_points = int(points_counts_all[i])
        pts_per_km2 = float(n_points / max(area_km2, 1e-9)) if area_km2 > 0 else None
        pts_per_10k = float(n_points * 10000.0 / pop) if pop and pop > 0 else None

        row = {
            "district": name,
            "ao": ao,
            "population": pop,
            "eligible_area_km2": round(area_km2, 4),
            "grid_cells": cells,
            "n_points_all_in_district": n_points,
            "points_per_km2_eligible": (round(pts_per_km2, 4) if isinstance(pts_per_km2, float) else None),
            "points_per_10k": (round(pts_per_10k, 4) if isinstance(pts_per_10k, float) else None),
            **stats,
        }
        rows_all.append(row)

        # Per-type rows
        for wt in waste_types:
            d_arr = dist_by_type.get(wt)
            if d_arr is None:
                continue
            if cells > 0:
                st = summarize_distances(np.asarray(d_arr, dtype=float)[idxs], radius_m=radius_m)
            else:
                st = {"cells_total": 0, "cells_no_points": 0, "share_no_points": 0.0, "coverage_share": 0.0, "white_spot_share": 0.0,
                      "mean_dist_m": None, "median_dist_m": None, "p95_dist_m": None, "max_dist_m": None}
            n_pt = int(counts_by_type.get(wt, np.zeros(n_d, dtype=int))[i])
            pts_km2 = float(n_pt / max(area_km2, 1e-9)) if area_km2 > 0 else None
            pts_10k = float(n_pt * 10000.0 / pop) if pop and pop > 0 else None
            rows_t.append(
                {
                    "waste_type": wt,
                    "district": name,
                    "ao": ao,
                    "population": pop,
                    "eligible_area_km2": round(area_km2, 4),
                    "grid_cells": cells,
                    "n_points_type_in_district": n_pt,
                    "points_per_km2_eligible": (round(pts_km2, 4) if isinstance(pts_km2, float) else None),
                    "points_per_10k": (round(pts_10k, 4) if isinstance(pts_10k, float) else None),
                    **st,
                }
            )

    df_all = pd.DataFrame(rows_all)
    df_t = pd.DataFrame(rows_t)

    # Save
    out_all_csv = out_dir / "district_accessibility__all.csv"
    out_t_csv = out_dir / "district_accessibility__per_type.csv"
    df_all.to_csv(out_all_csv, index=False, encoding="utf-8")
    df_t.to_csv(out_t_csv, index=False, encoding="utf-8")

    # Rankings (top/bottom by points_per_10k and coverage_share)
    def _top_bottom(df: "pd.DataFrame", metric: str, n: int) -> Tuple["pd.DataFrame", "pd.DataFrame"]:
        if metric not in df.columns:
            return df.head(0), df.head(0)
        dfx = df.dropna(subset=[metric]).copy()
        if dfx.empty:
            return dfx, dfx
        top = dfx.sort_values(metric, ascending=False).head(n)
        bottom = dfx.sort_values(metric, ascending=True).head(n)
        return top, bottom

    md_lines: List[str] = []
    md_lines.append("# Районный анализ доступности РСО")
    md_lines.append("")
    md_lines.append(f"- Радиус доступности: **{int(radius_m)} м**")
    md_lines.append(f"- Шаг сетки: **{int(grid_step_m)} м**")
    md_lines.append(f"- Число районов: **{n_d}**")
    if pop_map:
        md_lines.append("- Индексы на население: **точки на 10 тыс. жителей** (по данным CSV населения районов).")
    else:
        md_lines.append("- Индексы на население: **нет данных** (population CSV не найден).")
    md_lines.append("")

    # Overall rankings
    md_lines.append("## Все фракции вместе")
    top, bot = _top_bottom(df_all, "points_per_10k", int(top_n))
    md_lines.append("### TOP по точкам на 10 тыс. жителей")
    md_lines.append(_md_table(top, ["district", "ao", "n_points_all_in_district", "population", "points_per_10k", "coverage_share", "share_no_points"], n=top_n))
    md_lines.append("")
    md_lines.append("### BOTTOM по точкам на 10 тыс. жителей")
    md_lines.append(_md_table(bot, ["district", "ao", "n_points_all_in_district", "population", "points_per_10k", "coverage_share", "share_no_points"], n=top_n))
    md_lines.append("")
    top2, bot2 = _top_bottom(df_all, "coverage_share", int(top_n))
    md_lines.append("### TOP по доле покрытия (coverage_share)")
    md_lines.append(_md_table(top2, ["district", "ao", "coverage_share", "median_dist_m", "p95_dist_m", "share_no_points"], n=top_n))
    md_lines.append("")
    md_lines.append("### BOTTOM по доле покрытия (coverage_share)")
    md_lines.append(_md_table(bot2, ["district", "ao", "coverage_share", "median_dist_m", "p95_dist_m", "share_no_points"], n=top_n))
    md_lines.append("")

    # Per-type rankings
    for wt in waste_types:
        dfw = df_t[df_t["waste_type"] == wt].copy()
        md_lines.append(f"## Фракция: {wt}")
        top, bot = _top_bottom(dfw, "points_per_10k", int(top_n))
        md_lines.append("### TOP по точкам на 10 тыс. жителей")
        md_lines.append(_md_table(top, ["district", "ao", "n_points_type_in_district", "population", "points_per_10k", "coverage_share", "share_no_points"], n=top_n))
        md_lines.append("")
        md_lines.append("### BOTTOM по точкам на 10 тыс. жителей")
        md_lines.append(_md_table(bot, ["district", "ao", "n_points_type_in_district", "population", "points_per_10k", "coverage_share", "share_no_points"], n=top_n))
        md_lines.append("")
        top2, bot2 = _top_bottom(dfw, "coverage_share", int(top_n))
        md_lines.append("### TOP по доле покрытия (coverage_share)")
        md_lines.append(_md_table(top2, ["district", "ao", "coverage_share", "median_dist_m", "p95_dist_m", "share_no_points"], n=top_n))
        md_lines.append("")
        md_lines.append("### BOTTOM по доле покрытия (coverage_share)")
        md_lines.append(_md_table(bot2, ["district", "ao", "coverage_share", "median_dist_m", "p95_dist_m", "share_no_points"], n=top_n))
        md_lines.append("")

    out_md = out_dir / "district_rankings.md"
    out_md.write_text("\n".join(md_lines), encoding="utf-8")

    # Return compact summary for metrics.json
    summary: Dict[str, object] = {
        "enabled": True,
        "districts_count": int(n_d),
        "files": {
            "district_accessibility_all_csv": str(out_all_csv.name),
            "district_accessibility_per_type_csv": str(out_t_csv.name),
            "district_rankings_md": str(out_md.name),
        },
    }
    return summary
def analyze_accessibility(
    points_csv: Path,
    out_dir: Path,
    bbox: BBox,
    radius_m: float = 800.0,
    grid_step_m: float = 500.0,
    data_dir: Optional[Path] = None,
    exclude_osm: bool = True,
    waste_types: Optional[List[str]] = None,
    type_scheme: str = "categories",
    max_white_markers: int = 1500,
    show_excluded_layer: bool = False,
    # districts (optional)
    districts_geojson: Optional[Path] = None,
    district_population_csv: Optional[Path] = None,
    district_top_n: int = 5,
    # recommendations
    recommend_for: Optional[List[str]] = None,
    recommend_top: int = 8,
    min_cluster_cells: int = 4,
    reverse_geocode_recs: bool = False,
    reverse_geocode_limit: int = 0,
) -> Dict[str, object]:
    """
    Compute accessibility metrics (overall + per waste type) and export:
    - grid CSVs
    - metrics.json
    - recommendations outputs
    - interactive map.html
    """
    if pd is None or np is None:
        raise RuntimeError("pandas and numpy are required. Install: pip install pandas numpy")

    safe_mkdir(out_dir)
    df = pd.read_csv(points_csv)

    if df.empty:
        raise RuntimeError("No points found. Check bbox/end_id or points file.")

    # Normalize fractions fields (support both new and old CSV formats)
    if "fractions_raw" not in df.columns:
        df["fractions_raw"] = df.get("fractions", "")
    df["fractions_raw"] = df["fractions_raw"].fillna("").astype(str)
    df["fractions"] = df.get("fractions", "").fillna("").astype(str)

    # Combined field for robust matching (works for both code-only and human-readable)
    df["fractions_search"] = (df["fractions_raw"].astype(str) + " " + df["fractions"].astype(str)).fillna("").astype(str)

    # Optional: clip analysis to district polygons (defines the city boundary) + enable per-district metrics
    district_index: Optional[DistrictIndex] = None
    grid_district_idx: Optional["np.ndarray"] = None
    pop_by_district: Optional[Dict[str, Dict[str, object]]] = None
    districts_geojson_path: Optional[Path] = None

    if districts_geojson is not None:
        districts_geojson_path = Path(districts_geojson)
        if not districts_geojson_path.exists():
            raise RuntimeError(f"Districts GeoJSON not found: {districts_geojson_path}")
        district_index = load_districts_geojson(districts_geojson_path)

        # Assign district for each point and DROP points outside provided districts (old Moscow boundary)
        df_before = df.copy()
        p_idx = assign_district_indices(df_before["lon"].values, df_before["lat"].values, district_index)
        df_before["district_idx"] = p_idx
        df = df_before[df_before["district_idx"] >= 0].copy()

        if df.empty:
            # Heuristic auto-fix: maybe lon/lat are swapped in the points CSV
            p_idx_swapped = assign_district_indices(df_before["lat"].values, df_before["lon"].values, district_index)
            if (p_idx_swapped >= 0).any():
                print("[WARN] Detected swapped lon/lat columns in points CSV. Auto-fixing (swap lon<->lat).")
                df_before2 = df_before.copy()
                df_before2["lon"], df_before2["lat"] = df_before2["lat"], df_before2["lon"]
                df_before2["district_idx"] = p_idx_swapped
                df = df_before2[df_before2["district_idx"] >= 0].copy()

        if df.empty:
            # Diagnostics for user
            try:
                lon_min0 = float(pd.to_numeric(df_before["lon"], errors="coerce").min())
                lon_max0 = float(pd.to_numeric(df_before["lon"], errors="coerce").max())
                lat_min0 = float(pd.to_numeric(df_before["lat"], errors="coerce").min())
                lat_max0 = float(pd.to_numeric(df_before["lat"], errors="coerce").max())
                coord_hint = f"Диапазон точек: lon=[{lon_min0:.4f};{lon_max0:.4f}], lat=[{lat_min0:.4f};{lat_max0:.4f}]."
            except Exception:
                coord_hint = "Не удалось вычислить диапазон координат точек."
            try:
                import shapely as _shp  # type: ignore
                shp_ver = getattr(_shp, "__version__", "unknown")
            except Exception:
                shp_ver = "unknown"
            raise RuntimeError(
                "После фильтрации по границам (районы) не осталось ни одной точки.\n"
                "Проверьте, что points CSV действительно относится к Москве (и bbox задан как lon_min lat_min lon_max lat_max).\n"
                f"Версия shapely: {shp_ver}. {coord_hint}"
            )

        # Add readable columns (handy for exports / debugging)
        df["district"] = df["district_idx"].apply(lambda i: district_index.districts[int(i)].name if int(i) >= 0 else "")
        df["ao"] = df["district_idx"].apply(lambda i: (district_index.districts[int(i)].abbrev_ao or district_index.districts[int(i)].ao) if int(i) >= 0 else "")

        # Population dataset (optional): auto-download Moscow Population 2018 CSV if not provided
        pop_path: Optional[Path] = None
        if district_population_csv is not None:
            pop_path = Path(district_population_csv)
            if not pop_path.exists():
                print(f"[WARN] district_population_csv not found: {pop_path}")
                pop_path = None

        if pop_path is None:
            if data_dir is None:
                data_dir = out_dir / "data"
            safe_mkdir(data_dir)

            # Prefer a local (more recent) population table if present
            cand1 = data_dir / "moscow_population_2024_125districts.csv"
            cand2 = Path("moscow_population_2024_125districts.csv")
            if cand1.exists():
                pop_path = cand1
            elif cand2.exists():
                pop_path = cand2
            else:
                pop_path = ensure_moscow_population_csv(data_dir=data_dir, refresh=False)

        if pop_path is not None and pop_path.exists():
            try:
                pop_by_district = load_moscow_population_by_district(pop_path)
            except Exception as e:
                print(f"[WARN] Failed to load population CSV: {e}")
                pop_by_district = None

    # Determine analysis waste types
    if waste_types is None:
        waste_types = ["Бумага", "Пластик", "Стекло", "Металл", "ТетраПак", "Батарейки"]

    # Projection
    lon_c, lat_c = bbox.center()
    fwd, inv = make_transformers(center_lon=lon_c, center_lat=lat_c)

    # Points in meters (overall)
    px, py = fwd.transform(df["lon"].values, df["lat"].values)
    pts_xy_all = np.c_[px, py]

    # Grid
    grid_xy, grid_ll = build_grid(bbox, grid_step_m, fwd, inv)

    # Apply exclusion mask
    exclusion_polys: List[BaseGeometry] = []
    if exclude_osm:
        if data_dir is None:
            data_dir = out_dir / "data"
        safe_mkdir(data_dir)
        exclusion_polys = load_osm_exclusions(bbox=bbox, data_dir=data_dir, reuse_cache=True, refresh=False)
        if exclusion_polys:
            keep_mask = filter_grid_excluding_polygons(grid_ll, exclusion_polys)
            grid_xy = grid_xy[keep_mask]
            grid_ll = grid_ll[keep_mask]

    # Clip grid to district polygons (city boundary), if provided
    if district_index is not None:
        g_idx = assign_district_indices(grid_ll[:, 0], grid_ll[:, 1], district_index)
        keep = g_idx >= 0
        grid_xy = grid_xy[keep]
        grid_ll = grid_ll[keep]
        grid_district_idx = g_idx[keep]



    if len(grid_xy) < 10:
        raise RuntimeError(
            "После исключения территорий осталось слишком мало точек сетки. "
            "Уменьшите исключения (--no-exclude-osm) или увеличьте bbox."
        )

    # Compute bbox area and eligible area (approx by grid cells)
    x0, y0 = fwd.transform(bbox.lon_min, bbox.lat_min)
    x1, y1 = fwd.transform(bbox.lon_max, bbox.lat_max)
    bbox_area_km2 = (abs(x1 - x0) * abs(y1 - y0)) / 1e6
    eligible_area_km2 = (len(grid_xy) * (float(grid_step_m) ** 2)) / 1e6

    # Overall distances
    d_all = nearest_distances_m(grid_xy, pts_xy_all)

    # Save base grid CSV
    grid_base = pd.DataFrame(
        {
            "lon": grid_ll[:, 0],
            "lat": grid_ll[:, 1],
            "dist_m_all": d_all,
            "white_spot_all": (d_all > float(radius_m)).astype(int),
        }
    )
    grid_base.to_csv(out_dir / "grid_distances__all.csv", index=False, encoding="utf-8")

    # Metrics overall (finite-safe)
    overall_stats = summarize_distances(d_all, radius_m=radius_m)

    metrics: Dict[str, object] = {
        "generated_at": utc_now_iso(),
        "bbox": {"lon_min": bbox.lon_min, "lat_min": bbox.lat_min, "lon_max": bbox.lon_max, "lat_max": bbox.lat_max},
        "radius_m": float(radius_m),
        "grid_step_m": float(grid_step_m),
        "area_km2_bbox": float(bbox_area_km2),
        "area_km2_eligible": float(eligible_area_km2),
        "n_points_all": int(len(df)),
        "density_points_per_km2_eligible": float(len(df) / max(eligible_area_km2, 1e-9)),
        "exclude_osm": bool(exclude_osm),
        "waste_type_scheme": str(type_scheme),
        "waste_types": waste_types,
        "overall": overall_stats,
        # legacy-friendly shortcuts (finite-safe)
        "coverage_share_all": overall_stats.get("coverage_share"),
        "white_spot_share_all": overall_stats.get("white_spot_share"),
        "mean_distance_m_all": overall_stats.get("mean_dist_m"),
        "median_distance_m_all": overall_stats.get("median_dist_m"),
        "p95_distance_m_all": overall_stats.get("p95_dist_m"),
        "max_distance_m_all": overall_stats.get("max_dist_m"),
        "cells_no_points_all": overall_stats.get("cells_no_points"),
        "share_no_points_all": overall_stats.get("share_no_points"),
        "per_type": {},
    }

    # Per-type computations
    per_type: Dict[str, dict] = {}
    dist_by_type: Dict[str, np.ndarray] = {}

    for wt in waste_types:
        accept_mask = df["fractions_search"].apply(lambda s: point_accepts_type(str(s), wt, scheme=type_scheme))
        df_t = df[accept_mask].copy()

        if df_t.empty:
            d_t = np.full(len(grid_xy), np.inf, dtype=float)
            dist_by_type[wt] = d_t
            stats_t = summarize_distances(d_t, radius_m=radius_m)
            per_type[wt] = {
                "n_points": 0,
                "density_points_per_km2_eligible": 0.0,
                **stats_t,
            }
            # Save grid distances for this type (still useful to show white spot layer)
            type_key = re.sub(r"[^0-9A-Za-zА-Яа-я]+", "_", wt).strip("_")
            grid_t = pd.DataFrame(
                {"lon": grid_ll[:, 0], "lat": grid_ll[:, 1], f"dist_m_{type_key}": d_t, f"white_spot_{type_key}": (d_t > float(radius_m)).astype(int)}
            )
            grid_t.to_csv(out_dir / f"grid_distances__{type_key}.csv", index=False, encoding="utf-8")
            continue

        px_t, py_t = fwd.transform(df_t["lon"].values, df_t["lat"].values)
        pts_xy_t = np.c_[px_t, py_t]
        d_t = nearest_distances_m(grid_xy, pts_xy_t)
        dist_by_type[wt] = d_t

        # Save grid distances for this type
        type_key = re.sub(r"[^0-9A-Za-zА-Яа-я]+", "_", wt).strip("_")
        grid_t = pd.DataFrame(
            {"lon": grid_ll[:, 0], "lat": grid_ll[:, 1], f"dist_m_{type_key}": d_t, f"white_spot_{type_key}": (d_t > float(radius_m)).astype(int)}
        )
        grid_t.to_csv(out_dir / f"grid_distances__{type_key}.csv", index=False, encoding="utf-8")

        stats_t = summarize_distances(d_t, radius_m=radius_m)
        per_type[wt] = {
            "n_points": int(len(df_t)),
            "density_points_per_km2_eligible": float(len(df_t) / max(eligible_area_km2, 1e-9)),
            **stats_t,
        }

    metrics["per_type"] = per_type

    # -----------------------------
    # Recommendations: where to open new points (per type)
    # -----------------------------
    recs_by_type: Dict[str, List[Dict[str, object]]] = {}

    if recommend_for is None:
        recommend_for = ["Пластик", "Стекло", "Батарейки"]
    recommend_for_norm = [wt for wt in (recommend_for or []) if wt in waste_types]

    # centroid of eligible territory (grid-based)
    centroid_lon = float(np.mean(grid_ll[:, 0]))
    centroid_lat = float(np.mean(grid_ll[:, 1]))

    if recommend_for_norm:
        for wt in recommend_for_norm:
            d_t = dist_by_type.get(wt)
            if d_t is None:
                recs_by_type[wt] = []
                continue

            points_count = int(per_type.get(wt, {}).get("n_points", 0))

            # If there are ZERO points for this type: create one minimal recommendation at centroid
            if points_count == 0:
                recs_by_type[wt] = [
                    {
                        "n_cells": int(len(grid_xy)),
                        "area_km2": float(eligible_area_km2),
                        "mean_distance_m": None,
                        "max_distance_m": None,
                        "score": float(eligible_area_km2),
                        "recommended_lon": centroid_lon,
                        "recommended_lat": centroid_lat,
                        "note": "В пределах выбранного региона не найдено ни одного пункта для этой фракции: требуется минимум 1 новый пункт.",
                    }
                ]
                continue

            # Normal clustering-based recommendations
            clusters = cluster_white_spots(
                grid_xy=grid_xy,
                grid_ll=grid_ll,
                distances_m=d_t,
                step_m=grid_step_m,
                radius_m=radius_m,
                inv=inv,
                min_cluster_cells=min_cluster_cells,
                connectivity=8,
            )
            top = clusters[: int(recommend_top)]
            recs_by_type[wt] = top

        # Optional reverse geocoding for top recommendations
        if reverse_geocode_recs and int(reverse_geocode_limit) > 0:
            for wt, recs in recs_by_type.items():
                if not recs:
                    continue
                lim = min(int(reverse_geocode_limit), len(recs))
                for i in range(lim):
                    r = recs[i]
                    lat_r = float(r.get("recommended_lat"))
                    lon_r = float(r.get("recommended_lon"))
                    addr = reverse_geocode(lat_r, lon_r, language="ru", min_delay_s=1.0)
                    if addr:
                        r["approx_address"] = addr

        # Save into metrics + outputs
        metrics["recommendations"] = {
            wt: [
                {
                    "rank": i + 1,
                    "recommended_lat": r.get("recommended_lat"),
                    "recommended_lon": r.get("recommended_lon"),
                    "area_km2": r.get("area_km2"),
                    "mean_distance_m": r.get("mean_distance_m"),
                    "max_distance_m": r.get("max_distance_m"),
                    "score": r.get("score"),
                    "note": r.get("note", ""),
                    **({"approx_address": r.get("approx_address")} if r.get("approx_address") else {}),
                }
                for i, r in enumerate(recs_by_type.get(wt, []))
            ]
            for wt in recs_by_type
        }

        try:
            write_recommendations_outputs(out_dir=out_dir, metrics=metrics, recs_by_type=recs_by_type)
        except Exception as e:
            print(f"[WARN] Failed to write recommendations outputs: {e}")

    # -----------------------------
    # District-level accessibility (optional): per-district tables + rankings (Top/Bottom)
    # -----------------------------
    if district_index is not None and grid_district_idx is not None:
        try:
            district_summary = compute_district_accessibility(
                out_dir=out_dir,
                district_index=district_index,
                grid_district_idx=grid_district_idx,
                points_df=df,
                distances_all=d_all,
                dist_by_type=dist_by_type,
                waste_types=waste_types,
                radius_m=radius_m,
                grid_step_m=grid_step_m,
                type_scheme=type_scheme,
                pop_by_district=pop_by_district,
                top_n=int(district_top_n),
            )
            metrics["district_analysis"] = district_summary
            metrics["districts_geojson"] = str(districts_geojson_path) if districts_geojson_path else None
        except Exception as e:
            print(f"[WARN] District analysis failed: {e}")
            metrics["district_analysis"] = {"enabled": False, "reason": str(e)}
            metrics["districts_geojson"] = str(districts_geojson_path) if districts_geojson_path else None

    # Save metrics.json
    (out_dir / "metrics.json").write_text(json.dumps(metrics, ensure_ascii=False, indent=2), encoding="utf-8")

    # -----------------------------
    # Build map
    # -----------------------------
    if folium is not None:
        m = folium.Map(location=[float(df["lat"].mean()), float(df["lon"].mean())], zoom_start=10, control_scale=True)

        # Optional: district boundaries layer
        if districts_geojson_path is not None:
            try:
                gj_obj = json.loads(districts_geojson_path.read_text(encoding="utf-8"))
                fg_dist = folium.FeatureGroup(name="Границы районов (старые)", show=False)
                try:
                    tooltip = folium.GeoJsonTooltip(fields=["NAME", "ABBREV_AO"], aliases=["Район", "АО"])
                except Exception:
                    tooltip = None
                folium.GeoJson(
                    data=gj_obj,
                    name="districts",
                    style_function=lambda feature: {"color": "#666666", "weight": 1, "fillOpacity": 0.0},
                    tooltip=tooltip,
                ).add_to(fg_dist)
                fg_dist.add_to(m)
            except Exception as e:
                print(f"[WARN] Districts layer skipped: {e}")


        # District choropleths (per district): coverage (R) + points per 10k + save PNG images
        if districts_geojson_path is not None:
            try:
                add_district_choropleths_to_map(
                    m=m,
                    districts_geojson_path=districts_geojson_path,
                    out_dir=out_dir,
                    waste_types=waste_types,
                    radius_m=radius_m,
                    save_images=True,
                )
            except Exception as e:
                print(f"[WARN] Choropleth layers skipped: {e}")


        # Layer: all points
        all_fg = folium.FeatureGroup(name="Точки: все", show=True)
        all_mc = MarkerCluster().add_to(all_fg)
        for _, r in df.iterrows():
            popup = folium.Popup(
                f"<b>{sanitize_text(r.get('title',''))}</b><br>"
                f"{sanitize_text(r.get('address',''))}<br>"
                f"<i>Фракции:</i> {sanitize_text(r.get('fractions','') or r.get('fractions_raw',''))}",
                max_width=380,
            )
            folium.Marker([float(r["lat"]), float(r["lon"])], popup=popup).add_to(all_mc)
        all_fg.add_to(m)

        # Layer: white spots overall (brighter circles)
        ws_fg = folium.FeatureGroup(name=f"Белые пятна: все (R={int(radius_m)}м)", show=False)
        ws_df = grid_base[grid_base["dist_m_all"] > float(radius_m)]
        if len(ws_df) > 0:
            # take deepest cells first to better highlight centers of "holes"
            ws_s = ws_df.nlargest(min(int(max_white_markers), len(ws_df)), "dist_m_all")
            for _, r in ws_s.iterrows():
                dist_val = float(r["dist_m_all"])
                # circle radius proportional to "depth" beyond radius_m (capped)
                if not math.isfinite(dist_val):
                    r_m = float(grid_step_m) * 0.75
                else:
                    depth = max(0.0, dist_val - float(radius_m))
                    r_m = max(float(grid_step_m) * 0.5, min(depth, float(grid_step_m) * 3.0))
                folium.Circle(
                    location=[float(r["lat"]), float(r["lon"])],
                    radius=r_m,
                    color="#ffffff",
                    weight=1,
                    opacity=0.9,
                    fill=True,
                    fill_color="#ffffff",
                    fill_opacity=0.32,
                    tooltip=f"dist={_fmt_dist_m(dist_val)} м",
                ).add_to(ws_fg)
        ws_fg.add_to(m)

        # Layers per waste type
        for wt in waste_types:
            type_key = re.sub(r"[^0-9A-Za-zА-Яа-я]+", "_", wt).strip("_")

            # points layer
            fg_pts = folium.FeatureGroup(name=f"Точки: {wt}", show=False)
            mc = MarkerCluster().add_to(fg_pts)
            accept_mask = df["fractions_search"].apply(lambda s: point_accepts_type(str(s), wt, scheme=type_scheme))
            df_t = df[accept_mask]
            for _, r in df_t.iterrows():
                popup = folium.Popup(
                    f"<b>{sanitize_text(r.get('title',''))}</b><br>"
                    f"{sanitize_text(r.get('address',''))}<br>"
                    f"<i>Фракции:</i> {sanitize_text(r.get('fractions','') or r.get('fractions_raw',''))}",
                    max_width=380,
                )
                folium.Marker([float(r["lat"]), float(r["lon"])], popup=popup).add_to(mc)
            fg_pts.add_to(m)

            # white spots layer (brighter circles)
            fg_ws = folium.FeatureGroup(name=f"Белые пятна: {wt} (R={int(radius_m)}м)", show=False)
            d_t = dist_by_type.get(wt)
            if d_t is not None:
                ws_mask_t = np.asarray(d_t, dtype=float) > float(radius_m)
                if ws_mask_t.any():
                    ws_ll = grid_ll[ws_mask_t]
                    ws_dt = np.asarray(d_t, dtype=float)[ws_mask_t]
                    # take deepest cells first (better "centers" of holes)
                    if len(ws_ll) > int(max_white_markers):
                        kmax = int(max_white_markers)
                        idx_sel = np.argpartition(ws_dt, -kmax)[-kmax:]
                        ws_ll = ws_ll[idx_sel]
                        ws_dt = ws_dt[idx_sel]
                    for (lon, lat), dist_val in zip(ws_ll, ws_dt):
                        dist_val = float(dist_val)
                        if not math.isfinite(dist_val):
                            r_m = float(grid_step_m) * 0.75
                        else:
                            depth = max(0.0, dist_val - float(radius_m))
                            r_m = max(float(grid_step_m) * 0.5, min(depth, float(grid_step_m) * 3.0))
                        folium.Circle(
                            location=[float(lat), float(lon)],
                            radius=r_m,
                            color="#ffffff",
                            weight=1,
                            opacity=0.9,
                            fill=True,
                            fill_color="#ffffff",
                            fill_opacity=0.32,
                            tooltip=f"dist={_fmt_dist_m(dist_val)} м",
                        ).add_to(fg_ws)
            fg_ws.add_to(m)

            # recommendations layer
            recs = recs_by_type.get(wt, []) if isinstance(recs_by_type, dict) else []
            if recs:
                fg_rec = folium.FeatureGroup(name=f"Рекомендации: {wt}", show=False)
                for rank, rec in enumerate(recs, start=1):
                    lat_r = float(rec.get("recommended_lat"))
                    lon_r = float(rec.get("recommended_lon"))
                    area_km2 = float(rec.get("area_km2", 0.0))
                    max_d = rec.get("max_distance_m", None)
                    mean_d = rec.get("mean_distance_m", None)
                    addr = sanitize_text(rec.get("approx_address", ""))
                    note = sanitize_text(rec.get("note", ""))

                    popup_html = (
                        f"<b>Рекомендация #{rank}: {sanitize_text(wt)}</b><br>"
                        f"Координаты: {lat_r:.6f}, {lon_r:.6f}<br>"
                        f"Площадь белого пятна: {area_km2:.3f} км²<br>"
                        f"Средняя дистанция: {_fmt_dist_m(mean_d)} м<br>"
                        f"Макс. дистанция: {_fmt_dist_m(max_d)} м<br>"
                    )
                    if addr:
                        popup_html += f"<i>Адрес (примерно):</i> {addr}<br>"
                    if note:
                        popup_html += f"<i>Примечание:</i> {note}<br>"

                    popup = folium.Popup(popup_html, max_width=450)
                    folium.Marker(
                        [lat_r, lon_r],
                        tooltip=f"#{rank} {wt}: max {_fmt_dist_m(max_d)} м, {area_km2:.2f} км²",
                        popup=popup,
                        icon=folium.Icon(color="green", icon="plus-sign"),
                    ).add_to(fg_rec)

                    # optional area circle (~ cluster footprint)
                    try:
                        n_cells = float(rec.get("n_cells", 0))
                        area_m2 = n_cells * (float(grid_step_m) ** 2)
                        r_m = math.sqrt(max(area_m2, 1.0) / math.pi)
                        folium.Circle(
                            location=[lat_r, lon_r],
                            radius=r_m,
                            weight=1,
                            fill=True,
                            fill_opacity=0.05,
                        ).add_to(fg_rec)
                    except Exception:
                        pass

                fg_rec.add_to(m)

        # Optional excluded layer (may be heavy)
        if show_excluded_layer and exclude_osm and exclusion_polys and folium is not None:
            try:
                ex_fg = folium.FeatureGroup(name="Исключённые зоны (OSM)", show=False)
                for g in exclusion_polys[:500]:
                    if not hasattr(g, "__geo_interface__"):
                        continue
                    folium.GeoJson(
                        data=g.__geo_interface__,
                        style_function=lambda feature: {"weight": 1, "fillOpacity": 0.05},
                    ).add_to(ex_fg)
                ex_fg.add_to(m)
            except Exception:
                pass

        folium.LayerControl().add_to(m)
        html_map = out_dir / "map.html"
        m.save(str(html_map))
        patch_folium_html_for_compat(html_map, prefer_unpkg_leaflet=True)

    return metrics


# -----------------------------
# Nearest points (for mini-service)
# -----------------------------

def haversine_m(lon1: float, lat1: float, lon2: float, lat2: float) -> float:
    R = 6371000.0
    phi1 = math.radians(lat1)
    phi2 = math.radians(lat2)
    dphi = math.radians(lat2 - lat1)
    dl = math.radians(lon2 - lon1)
    a = math.sin(dphi / 2) ** 2 + math.cos(phi1) * math.cos(phi2) * math.sin(dl / 2) ** 2
    return 2 * R * math.asin(math.sqrt(a))


def geocode_address(address: str, *, language: str = "ru") -> Tuple[float, float]:
    """
    Геокодирование адреса (перевод адреса в координаты) с несколькими источниками.

    Поддерживает ввод координат напрямую в формате: "55.75, 37.61" (широта, долгота),
    а также "37.61, 55.75" (долгота, широта).

    Порядок провайдеров:
      1) geocode.maps.co (если указан API‑ключ в переменной окружения GEOCODE_MAPSCO_KEY)
      2) Nominatim (OpenStreetMap)
      3) Photon (Komoot)

    Возвращает (lon, lat).
    """
    if requests is None:
        raise RuntimeError("requests is required. Install: pip install requests")

    addr = str(address or "").strip()
    if not addr:
        raise RuntimeError("Пустой адрес. Введите адрес или координаты (например: 55.75, 37.61).")

    # ---------------------------------------------------------
    # 0) Если пользователь ввёл координаты, парсим их без сети
    # ---------------------------------------------------------
    m = re.match(r"^\s*([+-]?\d+(?:[\.,]\d+)?)\s*[,;\s]\s*([+-]?\d+(?:[\.,]\d+)?)\s*$", addr)
    if m:
        a = float(m.group(1).replace(",", "."))
        b = float(m.group(2).replace(",", "."))
        # эвристика: если первая величина выходит за диапазон широты, то это долгота
        if abs(a) > 90 and abs(b) <= 90:
            lon, lat = a, b
        else:
            lat, lon = a, b
        if not (-90 <= lat <= 90 and -180 <= lon <= 180):
            raise RuntimeError("Координаты выглядят некорректно. Пример: 55.75, 37.61")
        return float(lon), float(lat)

    ua = "rso-school-project/1.0 (geocoding; educational use)"
    errors: List[str] = []

    def _req_json(url: str, params: Dict[str, object], headers: Dict[str, str], timeout: int = 20) -> object:
        r = requests.get(url, params=params, headers=headers, timeout=timeout)
        r.raise_for_status()
        return r.json()

    # ---------------------------------------------------------
    # 1) geocode.maps.co — предпочтительный провайдер при наличии ключа
    # ---------------------------------------------------------
    key = (
        os.environ.get("GEOCODE_MAPSCO_KEY")
        or os.environ.get("MAPSCO_API_KEY")
        or os.environ.get("GEOCODE_MAPSCO_API_KEY")
    )
    if key:
        try:
            url = "https://geocode.maps.co/search"
            params = {"q": addr, "limit": 1, "accept-language": language}
            headers = {"User-Agent": ua, "Accept-Language": language, "Authorization": f"Bearer {key}"}
            js = _req_json(url, params=params, headers=headers, timeout=20)
            if isinstance(js, list) and js:
                lon = float(js[0].get("lon"))
                lat = float(js[0].get("lat"))
                return lon, lat
            errors.append("geocode.maps.co: пустой результат")
        except Exception as e:
            # ключ не логируем
            errors.append(f"geocode.maps.co: {type(e).__name__}: {e}")

    # ---------------------------------------------------------
    # 2) Nominatim (OSM) — запасной вариант
    # ---------------------------------------------------------
    try:
        url = "https://nominatim.openstreetmap.org/search"
        params = {"q": addr, "format": "json", "limit": 1, "accept-language": language}
        headers = {"User-Agent": ua, "Accept-Language": language}
        js = _req_json(url, params=params, headers=headers, timeout=20)
        if isinstance(js, list) and js:
            lon = float(js[0]["lon"])
            lat = float(js[0]["lat"])
            return lon, lat
        errors.append("Nominatim: пустой результат")
    except Exception as e:
        errors.append(f"Nominatim: {type(e).__name__}: {e}")

    # ---------------------------------------------------------
    # 3) Photon — ещё один запасной вариант
    # ---------------------------------------------------------
    try:
        url = "https://photon.komoot.io/api"
        params = {"q": addr, "limit": 1, "lang": language}
        headers = {"User-Agent": ua, "Accept-Language": language}
        js = _req_json(url, params=params, headers=headers, timeout=20)
        if isinstance(js, dict):
            feats = js.get("features") or []
            if feats:
                coords = (feats[0].get("geometry") or {}).get("coordinates")
                if coords and len(coords) >= 2:
                    lon = float(coords[0])
                    lat = float(coords[1])
                    return lon, lat
        errors.append("Photon: пустой результат")
    except Exception as e:
        errors.append(f"Photon: {type(e).__name__}: {e}")

    hint = (
        "Не удалось определить координаты по адресу. Возможные причины: временная недоступность геокодера, "
        "блокировки в сети или слишком общий запрос.\n\n"
        "Попробуйте:\n"
        "• уточнить адрес (город, улица, дом),\n"
        "• или ввести координаты в формате: 55.75, 37.61\n\n"
        f"Ошибки: {' | '.join(errors) if errors else '(нет подробностей)'}"
    )
    raise RuntimeError(hint)


def nearest_points(
    points_csv: Path,
    lon: float,
    lat: float,
    k: int = 7,
    waste_type: Optional[str] = None,
    type_scheme: str = "categories",
) -> "pd.DataFrame":
    """Return k nearest points (optionally filtered by waste type)."""
    if pd is None:
        raise RuntimeError("pandas is required. Install: pip install pandas")
    df = pd.read_csv(points_csv)

    if df.empty:
        raise RuntimeError("Файл точек пуст.")

    # support both formats
    if "fractions_raw" not in df.columns:
        df["fractions_raw"] = df.get("fractions", "")
    df["fractions_raw"] = df["fractions_raw"].fillna("").astype(str)
    df["fractions"] = df.get("fractions", "").fillna("").astype(str)
    df["fractions_search"] = (df["fractions_raw"] + " " + df["fractions"]).fillna("").astype(str)

    if waste_type and waste_type.strip():
        mask = df["fractions_search"].apply(lambda s: point_accepts_type(str(s), waste_type.strip(), scheme=type_scheme))
        df = df[mask].copy()

    if df.empty:
        raise RuntimeError("Нет подходящих точек (фильтр по типу отходов слишком строгий или в данных нет этой фракции).")

    d = df.apply(lambda r: haversine_m(float(lon), float(lat), float(r["lon"]), float(r["lat"])), axis=1)
    df = df.assign(dist_m=d).sort_values("dist_m").head(int(k))
    return df[["dist_m", "title", "address", "fractions", "fractions_raw", "lon", "lat"]]


# -----------------------------
# CLI
# -----------------------------

def cmd_pipeline(args: argparse.Namespace) -> None:
    bbox = BBox(*args.bbox)
    out_dir = Path(args.out_dir)
    data_dir = Path(args.data_dir) if args.data_dir else (out_dir / "data")
    safe_mkdir(out_dir)
    safe_mkdir(data_dir)

    # points source
    points_csv: Optional[Path] = Path(args.points) if args.points else None
    if points_csv is None:
        points_csv = harvest_recyclemap_points_cached(
            data_dir=data_dir,
            bbox=bbox,
            point_type=args.point_type,
            start_id=args.start_id,
            end_id=args.end_id,
            reuse_cache=not args.no_reuse_data,
            refresh=args.refresh_data,
            scan_workers=args.scan_workers,
            rate_limit_rps=args.rate_limit,
            timeout_s=args.timeout,
            retries=args.retries,
            scan_chunk=args.scan_chunk,
            stop_after_misses=args.stop_after_misses,
            write_raw_cache=not args.no_raw_cache,
        )

    # Convenience: keep a copy of points CSV inside out-dir (easy to use in nearest/app)
    out_points_csv = out_dir / "points_filtered.csv"
    try:
        if points_csv.resolve() != out_points_csv.resolve():
            shutil.copy(points_csv, out_points_csv)
        points_csv = out_points_csv
    except Exception:
        pass

    # parse waste types
    waste_types: Optional[List[str]] = None
    if args.types:
        if args.types.strip().lower() == "all":
            waste_types = list(WASTE_CATEGORIES.keys())
        else:
            waste_types = [t.strip() for t in args.types.split(",") if t.strip()]

    recommend_for: Optional[List[str]] = None
    if args.recommend_for:
        if args.recommend_for.strip().lower() == "none":
            recommend_for = []
        elif args.recommend_for.strip().lower() == "all":
            recommend_for = waste_types or list(WASTE_CATEGORIES.keys())
        else:
            recommend_for = [t.strip() for t in args.recommend_for.split(",") if t.strip()]

    metrics = analyze_accessibility(
        points_csv=points_csv,
        out_dir=out_dir,
        bbox=bbox,
        radius_m=args.radius,
        grid_step_m=args.grid,
        data_dir=data_dir,
        exclude_osm=not args.no_exclude_osm,
        waste_types=waste_types,
        type_scheme=args.type_scheme,
        max_white_markers=args.max_white_markers,
        show_excluded_layer=args.show_excluded_layer,
        districts_geojson=(Path(args.districts_geojson) if getattr(args, 'districts_geojson', '') else None),
        district_population_csv=(Path(args.district_population_csv) if getattr(args, 'district_population_csv', '') else None),
        district_top_n=int(getattr(args, 'district_topn', 5)),
        recommend_for=recommend_for,
        recommend_top=args.recommend_top,
        min_cluster_cells=args.min_cluster_cells,
        reverse_geocode_recs=args.reverse_geocode_recs,
        reverse_geocode_limit=args.reverse_geocode_limit,
    )
    print(json.dumps(metrics, ensure_ascii=False, indent=2))


def cmd_nearest(args: argparse.Namespace) -> None:
    points_path = Path(args.points)
    if not points_path.exists():
        raise RuntimeError(f"Points file not found: {points_path}")

    if args.address:
        lon, lat = geocode_address(args.address)
    else:
        if args.lon is None or args.lat is None:
            raise ValueError("Provide --address OR both --lon and --lat")
        lon, lat = float(args.lon), float(args.lat)

    near = nearest_points(
        points_csv=points_path,
        lon=lon,
        lat=lat,
        k=args.k,
        waste_type=args.waste_type,
        type_scheme=args.type_scheme,
    )
    print(near.to_string(index=False))

    if args.out_html:
        if folium is None:
            print("[WARN] folium not installed; skipping html map export.")
            return
        m = folium.Map(location=[lat, lon], zoom_start=13, control_scale=True)
        folium.Marker([lat, lon], tooltip="Вы здесь").add_to(m)
        for _, r in near.iterrows():
            popup = folium.Popup(
                f"<b>{sanitize_text(r.get('title',''))}</b><br>"
                f"{sanitize_text(r.get('address',''))}<br>"
                f"<i>Фракции:</i> {sanitize_text(r.get('fractions','') or r.get('fractions_raw',''))}",
                max_width=380,
            )
            folium.Marker([float(r["lat"]), float(r["lon"])], tooltip=f"{_fmt_dist_m(r['dist_m'])} м", popup=popup).add_to(m)
        out_html = Path(args.out_html)
        m.save(str(out_html))
        patch_folium_html_for_compat(out_html, prefer_unpkg_leaflet=True)
        print(f"\nSaved map: {out_html.resolve()}")


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="rso_project.py", description="RSO accessibility project tools")
    sub = p.add_subparsers(dest="cmd", required=True)

    # pipeline
    sp = sub.add_parser("pipeline", help="Harvest + analyze + export map/metrics")
    sp.add_argument("--bbox", nargs=4, type=float, required=True, metavar=("LON_MIN", "LAT_MIN", "LON_MAX", "LAT_MAX"))
    sp.add_argument("--out-dir", type=str, default="project_run", help="Output directory")
    sp.add_argument("--data-dir", type=str, default="", help="Cache directory (default: <out-dir>/data)")
    sp.add_argument("--points", type=str, default="", help="Use existing points CSV instead of harvesting")

    sp.add_argument("--point-type", type=str, default="RC", help="Recyclemap point type filter (if available)")
    sp.add_argument("--start-id", type=int, default=1)
    sp.add_argument("--end-id", type=int, default=50000)

    # scan speed
    sp.add_argument("--scan-workers", type=int, default=12, help="Number of threads for scanning")
    sp.add_argument("--scan-chunk", type=int, default=400, help="Chunk size of IDs per batch")
    sp.add_argument("--rate-limit", type=float, default=4.0, help="Global requests per second limit")
    sp.add_argument("--timeout", type=int, default=20, help="HTTP timeout (seconds)")
    sp.add_argument("--retries", type=int, default=2, help="Retries per ID on network failure")
    sp.add_argument("--stop-after-misses", type=int, default=0, help="Early stop if this many non-existent IDs in a row (0=off)")
    sp.add_argument("--no-raw-cache", action="store_true", help="Do not write JSONL cache (faster/less disk)")

    # cache control
    sp.add_argument("--refresh-data", action="store_true", help="Ignore existing cache and start from scratch")
    sp.add_argument("--no-reuse-data", action="store_true", help="Do not reuse existing cache (always scan)")

    # analysis
    sp.add_argument("--radius", type=float, default=800.0, help="Accessibility radius in meters")
    sp.add_argument("--grid", type=float, default=500.0, help="Grid step in meters")
    sp.add_argument("--no-exclude-osm", action="store_true", help="Do not exclude OSM water/parks/industrial areas")
    sp.add_argument("--show-excluded-layer", action="store_true", help="Add excluded polygons layer on the map (heavy)")
    sp.add_argument("--types", type=str, default="", help="Comma-separated waste types to analyze, or 'all'")

    sp.add_argument("--type-scheme", type=str, default="categories", choices=["categories", "raw"], help="Type matching scheme")
    sp.add_argument("--max-white-markers", type=int, default=1500, help="Max markers per white-spot layer")

    # districts (optional)
    sp.add_argument("--districts-geojson", type=str, default="", help="GeoJSON с границами районов (например, Москва в старых границах) для отсечения города и расчёта метрик по районам")
    sp.add_argument("--district-population-csv", type=str, default="", help="CSV с населением районов (если пусто — попробуем скачать Moscow_Population_2018.csv автоматически)")
    sp.add_argument("--district-topn", type=int, default=5, help="TOP/BOTTOM N районов в итоговых таблицах")

    # recommendations
    sp.add_argument("--recommend-for", type=str, default="Пластик,Стекло,Батарейки", help="Types to generate recommendations for ('none'/'all'/csv list)")
    sp.add_argument("--recommend-top", type=int, default=8)
    sp.add_argument("--min-cluster-cells", type=int, default=4)
    sp.add_argument("--reverse-geocode-recs", action="store_true")
    sp.add_argument("--reverse-geocode-limit", type=int, default=0)

    sp.set_defaults(func=cmd_pipeline)

    # nearest
    sn = sub.add_parser("nearest", help="Nearest points by address or lon/lat")
    sn.add_argument("--points", type=str, required=True)
    sn.add_argument("--address", type=str, default="")
    sn.add_argument("--lon", type=float, default=None)
    sn.add_argument("--lat", type=float, default=None)
    sn.add_argument("--k", type=int, default=7)
    sn.add_argument("--waste-type", type=str, default="", help="Waste type filter (e.g., Пластик)")
    sn.add_argument("--type-scheme", type=str, default="categories", choices=["categories", "raw"])
    sn.add_argument("--out-html", type=str, default="", help="Optional HTML map output with results")
    sn.set_defaults(func=cmd_nearest)

    return p


def main(argv: Optional[List[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    args.func(args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
