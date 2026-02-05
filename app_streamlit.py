import streamlit as st
from pathlib import Path
import pandas as pd
import tempfile

import folium
from folium.plugins import MarkerCluster
import streamlit.components.v1 as components

import os

# --- geocode.maps.co API key (optional, but strongly recommended for stable geocoding) ---
# Put the key into Streamlit secrets as a root-level value:
#   GEOCODE_MAPSCO_KEY = "..."
# Streamlit will also expose root-level secrets as environment variables.
# To be extra robust, we mirror st.secrets -> os.environ.
try:
    _k = None
    try:
        _k = st.secrets.get("GEOCODE_MAPSCO_KEY")
    except Exception:
        _k = None
    if _k and not os.environ.get("GEOCODE_MAPSCO_KEY"):
        os.environ["GEOCODE_MAPSCO_KEY"] = str(_k)
except Exception:
    pass

# Import helpers from the project script (keep rso_project.py in the same folder)
try:
    from rso_project import (
        geocode_address,
        nearest_points,
        point_accepts_type,
        WASTE_CATEGORIES,
        patch_folium_html_for_compat,
        sanitize_text,
    )
except Exception:
    # fallback for local testing in this sandbox
    from rso_project_mapsco import (
        geocode_address,
        nearest_points,
        point_accepts_type,
        WASTE_CATEGORIES,
        patch_folium_html_for_compat,
        sanitize_text,
    )

st.set_page_config(page_title="Поиск ближайших пунктов РСО", layout="wide")
st.title("Доступность РСО: ближайшие пункты раздельного сбора отходов по адресу")

st.markdown(
    """
**Шаги:**
1) Введите адрес (например: *Москва, Тверская 7*).
2) Выберите тип отходов (или *(без фильтра)*).
3) Получите список ближайших точек и *что туда сдавать*.

✅ Фильтр поддерживает **коды Recyclemap** (например `PLASTIK`, `BATAREJKI`, `STEKLO`) и русские названия.
"""
)

default_points = Path("project_run/points_filtered.csv")
default_points_alt = Path("data/points_filtered.csv")

with st.sidebar:
    st.header("Настройки")
    points_path_str = st.text_input(
        "Путь к CSV точек",
        value=str(default_points if default_points.exists() else default_points_alt),
        help="CSV создаётся командой: python rso_project_final_v3_2.py pipeline ...",
    )
    k = st.number_input("Сколько точек показать", min_value=3, max_value=30, value=7, step=1)
    wt = st.selectbox("Тип отходов (фильтр)", ["(без фильтра)"] + list(WASTE_CATEGORIES.keys()))
    scheme = st.selectbox(
        "Схема фильтра",
        ["categories", "raw"],
        index=0,
        help="categories = словарь синонимов/кодов, raw = прямое совпадение подстроки",
    )

points_path = Path(points_path_str)

if not points_path.exists():
    st.error(
        f"Не найден файл точек: {points_path}.\n\n"
        "Сначала запусти пайплайн. Пример:\n"
        "python rso_project_final_v3_2.py pipeline --bbox 37.2 55.5 37.95 55.97 --out-dir project_run --data-dir data"
    )
    st.stop()


@st.cache_data(show_spinner=False)
def _load_points(p: str) -> pd.DataFrame:
    df = pd.read_csv(p)
    # normalize for filter count
    if "fractions_raw" not in df.columns:
        df["fractions_raw"] = df.get("fractions", "")
    df["fractions_raw"] = df["fractions_raw"].fillna("").astype(str)
    df["fractions"] = df.get("fractions", "").fillna("").astype(str)
    df["fractions_search"] = (df["fractions_raw"] + " " + df["fractions"]).fillna("").astype(str)
    return df


df_all = _load_points(str(points_path))
st.caption(f"Точек в базе: {len(df_all)} | Файл: {points_path}")

address = st.text_input("Адрес", value="Москва, Тверская 7")


def _show_map(lon: float, lat: float, near_df: pd.DataFrame) -> None:
    """Показывает выбранные точки на карте под таблицей."""
    m = folium.Map(location=[float(lat), float(lon)], zoom_start=14, control_scale=True)

    # marker for the input address
    folium.Marker(
        [float(lat), float(lon)],
        tooltip="Введённый адрес",
        popup=folium.Popup(f"<b>Адрес:</b> {sanitize_text(address)}", max_width=350),
        icon=folium.Icon(color="blue", icon="info-sign"),
    ).add_to(m)

    fg = folium.FeatureGroup(name="Найденные точки", show=True)
    mc = MarkerCluster().add_to(fg)

    for _, r in near_df.iterrows():
        title = sanitize_text(r.get("title", ""))
        addr = sanitize_text(r.get("address", ""))
        fr = sanitize_text(r.get("fractions", "") or r.get("fractions_raw", ""))
        dist = float(r.get("dist_m", 0.0))
        popup_html = f"<b>{title}</b><br>{addr}<br><i>Фракции:</i> {fr}<br><i>Дистанция:</i> {dist:.0f} м"
        folium.Marker(
            [float(r["lat"]), float(r["lon"])],
            popup=folium.Popup(popup_html, max_width=420),
            tooltip=f"{dist:.0f} м",
            icon=folium.Icon(color="green", icon="ok-sign"),
        ).add_to(mc)

    fg.add_to(m)
    folium.LayerControl().add_to(m)

    # Save -> patch -> render (fixes object spread + octal escapes; swaps CDN to unpkg)
    with tempfile.NamedTemporaryFile(mode="w", delete=False, suffix=".html", encoding="utf-8") as f:
        tmp_path = Path(f.name)
    m.save(str(tmp_path))
    patch_folium_html_for_compat(tmp_path, prefer_unpkg_leaflet=True)
    html = tmp_path.read_text(encoding="utf-8", errors="ignore")
    components.html(html, height=560, scrolling=False)


if st.button("Найти ближайшие") and address:
    try:
        lon, lat = geocode_address(address)
        waste_type = None if wt == "(без фильтра)" else wt

        if waste_type:
            msk = df_all["fractions_search"].apply(lambda s: point_accepts_type(str(s), waste_type, scheme=scheme))
            st.caption(f"Точек, подходящих под фильтр «{waste_type}»: {int(msk.sum())} из {len(df_all)}")

        near = nearest_points(points_path, lon, lat, k=int(k), waste_type=waste_type, type_scheme=scheme)

        st.success(f"Координаты: {lat:.6f}, {lon:.6f}")
        st.dataframe(near, use_container_width=True)

        st.subheader("Карта найденных точек")
        _show_map(lon, lat, near)

    except Exception as e:
        st.error(str(e))
