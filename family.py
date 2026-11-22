#!/usr/bin/env python3
"""Family dashboard for a kitchen kiosk (http://<your-server>:8096).

Serves index.html plus small JSON endpoints. Everything is fetched server-side and cached, so the
weak kiosk PC only renders a page and makes a handful of tiny requests.

  GET  /api/weather     current temperature + 3-day forecast (Open-Meteo, no key)
  GET  /api/week        this week's events, Monday to Sunday, from ICS links (Google secret iCal address)
  GET  /api/lists       to-do lists pushed by the iPhone Shortcut
  POST /api/lists       the Shortcut sends {"list": "Groceries", "items": "milk\\neggs"} here,
                        with header  Authorization: Bearer <LIST_TOKEN>
  GET  /api/photos      shuffled asset ids from one Immich album (optional)
  GET  /api/focus/<id>  where the faces are in that photo (for face-aware cropping)
  GET  /video/<id>      a short clip from the album, streamed from Immich (byte ranges)
  GET  /photo/<id>      that photo's preview-size JPEG, proxied with the Immich API key
  GET  /settings        page for changing the wallpaper and look from a phone or PC
  GET/POST /api/settings  wallpaper mode, image address, darken, glass blur, photo panel (data/settings.json)
  POST /api/background  upload a wallpaper image (the settings page shrinks it to screen size first)
  GET  /background      the uploaded wallpaper
  GET  /apod, /daily/<source>  today's picture-of-the-day wallpaper (apod, bing, commons, unsplash)

Standard library plus `icalendar` + `recurring-ical-events`, which the compose file pip-installs
into /app/vendor on first start.

Environment (see env.example):
  PORT          default 8096
  TZ            e.g. America/New_York
  ICS_URLS      comma-separated  Name|https://...ics   (Name|color|url also works, color like #e0679b)
  WX_PLACE      city name ("Portland, OR") or "lat,lon"
  WX_UNITS      us (default) or metric
                The calendar address, city and units can also be set on /settings, which wins over these.
  LIST_TOKEN    shared secret the Shortcut sends; POST /api/lists is refused without it
  LIST_STALE_H  hours after which a list shows "not updated since ..." (default 24)
  IMMICH_URL    e.g. http://<your-server>:2283   (blank = no photo panel)
  IMMICH_KEY    Immich API key (asset.read, asset.view, album.read)
  IMMICH_ALBUM  album id (the long id in the album's URL)
"""

import datetime as dt
import hashlib
import hmac
import json
import os
import random
import re
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

HERE = Path(__file__).resolve().parent
try:   # changes with each deploy; the kiosk reloads itself when it sees a new one
    BUILD = hashlib.sha1((HERE / "index.html").read_bytes()).hexdigest()[:10]
except OSError:
    BUILD = str(int(time.time()))
sys.path.insert(0, str(HERE / "vendor"))

try:
    import icalendar
    import recurring_ical_events
except ImportError:
    icalendar = None
    recurring_ical_events = None

try:
    from zoneinfo import ZoneInfo
    LOCAL_TZ = ZoneInfo(os.environ.get("TZ") or "UTC")
except Exception:
    LOCAL_TZ = dt.timezone.utc

PORT = int(os.environ.get("PORT", "8096"))
ICS_URLS = os.environ.get("ICS_URLS", "").strip()
WX_PLACE = os.environ.get("WX_PLACE", "").strip()
WX_UNITS = "metric" if os.environ.get("WX_UNITS", "us").strip().lower() == "metric" else "us"
LIST_TOKEN = os.environ.get("LIST_TOKEN", "").strip()
LIST_STALE_H = float(os.environ.get("LIST_STALE_H", "24") or 24)
IMMICH_URL = os.environ.get("IMMICH_URL", "").strip().rstrip("/")
IMMICH_KEY = os.environ.get("IMMICH_KEY", "").strip()
IMMICH_ALBUM = os.environ.get("IMMICH_ALBUM", "").strip()
LISTS_FILE = HERE / "data" / "lists.json"
SETTINGS_FILE = HERE / "data" / "settings.json"
BG_FILE = HERE / "data" / "background"
BG_TYPES = {"image/jpeg", "image/png", "image/webp"}
BG_MAX = 25 * 1024 * 1024
PRIVATE_FILE = HERE / "data" / "private.json"   # calendar address, Immich key: readable only by the server
LOOK_DEFAULTS = {"wx_place": "", "wx_units": "", "bg_mode": "default", "bg_url": "", "bg_dim": 30, "bg_every": 10, "blur": True, "photo_panel": True, "photo_fill": False, "photo_videos": False, "wx_days": 3, "wx_mono": False, "wx_bare": False, "text_scale": 100,
                 "color_rules": [{"words": "Kid 1", "color": "#f06262"}, {"words": "Kid 2", "color": "#a57cf5"},
                                 {"words": "Mom", "color": "#3cc48a"}, {"words": "Dad", "color": "#5b9bff"}],
                 "greet_name": "", "quotes": "", "quotes_only": False}
MAX_LISTS = 6
MAX_ITEMS = 60

GEO_API = "https://geocoding-api.open-meteo.com/v1/search"
WX_API = "https://api.open-meteo.com/v1/forecast"
WEATHER_CODES = {
    0: "Clear", 1: "Mostly clear", 2: "Partly cloudy", 3: "Cloudy", 45: "Fog", 48: "Freezing fog",
    51: "Light drizzle", 53: "Drizzle", 55: "Heavy drizzle", 56: "Freezing drizzle", 57: "Freezing drizzle",
    61: "Light rain", 63: "Rain", 65: "Heavy rain", 66: "Freezing rain", 67: "Freezing rain",
    71: "Light snow", 73: "Snow", 75: "Heavy snow", 77: "Snow grains", 80: "Showers",
    81: "Showers", 82: "Heavy showers", 85: "Snow showers", 86: "Heavy snow showers",
    95: "Storms", 96: "Storms, hail", 99: "Storms, hail"}
PALETTE = ["#5b9bff", "#ef7aa8", "#3cc48a", "#f0a53a", "#a57cf5", "#38bfd2"]


def log(*a):
    print(time.strftime("%H:%M:%S"), *a, flush=True)


# ---------------------------------------------------------------- cache + http
_cache = {}
_lock = threading.Lock()


def cached(key, ttl, fn):
    """Return fn() at most every ttl seconds; on failure keep serving the last good answer."""
    now = time.time()
    with _lock:
        hit = _cache.get(key)
        if hit and now - hit[0] < ttl:
            return hit[1]
    try:
        val = fn()
    except Exception as e:
        log(f"{key}: {e}")
        if hit:
            with _lock:
                _cache[key] = (now - ttl + 60, hit[1])  # retry in a minute
            return hit[1]
        val = {"error": str(e)}
        with _lock:
            _cache[key] = (now - ttl + 60, val)
        return val
    with _lock:
        _cache[key] = (now, val)
    return val


def fetch(url, headers=None, timeout=15, method="GET", body=None):
    h = {"User-Agent": "homelab-family/1"}
    h.update(headers or {})
    req = urllib.request.Request(url, headers=h, method=method, data=body)
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read(), r.headers.get("Content-Type", "")


# ---------------------------------------------------------------- weather
def cur_place():
    return load_settings().get("wx_place") or WX_PLACE


def cur_units():
    return load_settings().get("wx_units") or WX_UNITS


def cur_ics():
    """Calendar list: the address saved on /settings (kept out of /api/settings), else ICS_URLS."""
    url = load_private().get("ics_url", "")
    return f"Family|{url}" if url else ICS_URLS


def load_private():
    try:
        return json.loads(PRIVATE_FILE.read_text(encoding="utf-8"))
    except (FileNotFoundError, ValueError):
        return {}


def save_private(**kw):
    d = load_private()
    d.update(kw)
    write_json(PRIVATE_FILE, d)
    try:
        os.chmod(PRIVATE_FILE, 0o600)
    except OSError:
        pass


def wx_location(WX_PLACE):
    m = re.fullmatch(r"\s*(-?\d+(?:\.\d+)?)\s*,\s*(-?\d+(?:\.\d+)?)\s*", WX_PLACE)
    if m:
        return {"name": "", "lat": float(m[1]), "lon": float(m[2])}
    q = urllib.parse.urlencode({"name": WX_PLACE.split(",")[0].strip(), "count": 10, "language": "en"})
    res = json.loads(fetch(f"{GEO_API}?{q}")[0]).get("results") or []
    if not res:
        raise ValueError(f"couldn't find {WX_PLACE!r}; try just the city name, or lat,lon")
    # "Portland, OR" / "Portland, Oregon": prefer the match whose state or country contains the hint
    hint = WX_PLACE.split(",")[1].strip().lower() if "," in WX_PLACE else ""
    pick = next((r for r in res if hint and (hint in (r.get("admin1") or "").lower()
                                             or hint == (r.get("country_code") or "").lower())), res[0])
    return {"name": pick.get("name", ""), "lat": pick["latitude"], "lon": pick["longitude"]}


def weather_payload():
    place, units = cur_place(), cur_units()
    if not place:
        return {"error": "set your city on the Settings page (/settings)"}
    loc = cached("wxloc:" + place, 7 * 86400, lambda: wx_location(place))
    if "error" in loc:
        return loc
    metric = units == "metric"
    q = urllib.parse.urlencode({
        "latitude": loc["lat"], "longitude": loc["lon"], "timezone": "auto", "forecast_days": 7,
        "current": "temperature_2m,apparent_temperature,weather_code,is_day",
        "daily": "weather_code,temperature_2m_max,temperature_2m_min,precipitation_probability_max",
        "temperature_unit": "celsius" if metric else "fahrenheit"})
    d = json.loads(fetch(f"{WX_API}?{q}")[0])
    c, day = d.get("current", {}), d.get("daily", {})
    days = []
    for i, date in enumerate(day.get("time", [])[:7]):
        code = (day.get("weather_code") or [None] * 7)[i]
        days.append({"date": date, "code": code, "text": WEATHER_CODES.get(code, ""),
                     "high": day["temperature_2m_max"][i], "low": day["temperature_2m_min"][i],
                     "rain": (day.get("precipitation_probability_max") or [None] * 7)[i]})
    return {"place": loc["name"], "units": units, "temp": c.get("temperature_2m"),
            "feels": c.get("apparent_temperature"), "code": c.get("weather_code"),
            "text": WEATHER_CODES.get(c.get("weather_code"), ""), "is_day": c.get("is_day", 1),
            "days": days}


# ---------------------------------------------------------------- calendar (Mon-Sun)
def ics_sources():
    out = []
    for i, part in enumerate(p.strip() for p in cur_ics().split(",") if p.strip()):
        bits = part.split("|")
        url = bits[-1].strip().replace("webcal://", "https://", 1)
        name = bits[0].strip() if len(bits) > 1 else f"Calendar {i + 1}"
        color = bits[1].strip() if len(bits) > 2 else PALETTE[i % len(PALETTE)]
        out.append((name, color, url))
    return out


def to_local(v, all_day):
    if all_day:
        return dt.datetime.combine(v, dt.time(), LOCAL_TZ)
    if v.tzinfo is None:
        v = v.replace(tzinfo=LOCAL_TZ)
    return v.astimezone(LOCAL_TZ)


def week_payload():
    if icalendar is None:
        return {"error": "calendar libraries still installing; restart the container if this stays"}
    if not cur_ics():
        return {"error": "paste the Google calendar's secret iCal address on the Settings page (/settings)"}
    today = dt.datetime.now(LOCAL_TZ).replace(hour=0, minute=0, second=0, microsecond=0)
    monday = today - dt.timedelta(days=today.weekday())
    sunday_end = monday + dt.timedelta(days=7)
    events, errors = [], []
    for name, color, url in ics_sources():
        try:
            cal = icalendar.Calendar.from_ical(fetch(url, timeout=25)[0])
            occ = recurring_ical_events.of(cal).between(monday, sunday_end)
        except Exception as e:
            errors.append(f"{name}: {e}")
            continue
        for ev in occ:
            if str(ev.get("STATUS", "")).upper() == "CANCELLED":
                continue
            start = ev.get("DTSTART").dt
            all_day = not isinstance(start, dt.datetime)
            fin = ev.get("DTEND").dt if ev.get("DTEND") else None
            s = to_local(start, all_day)
            e = to_local(fin, all_day) if fin else s + (dt.timedelta(days=1) if all_day else dt.timedelta())
            events.append({"title": str(ev.get("SUMMARY", "") or "(no title)"),
                           "start": s.isoformat(), "end": e.isoformat(), "allDay": all_day,
                           "calendar": name, "color": color})
    if errors and not events:
        raise RuntimeError("; ".join(errors))  # cached() keeps the last good week
    events.sort(key=lambda x: (not x["allDay"], x["start"], x["title"]))
    return {"monday": monday.date().isoformat(), "events": events, "errors": errors}


# ---------------------------------------------------------------- lists (pushed by the Shortcut)
_list_lock = threading.Lock()


def load_lists():
    try:
        return json.loads(LISTS_FILE.read_text(encoding="utf-8"))
    except (FileNotFoundError, ValueError):
        return {}


def clean_items(raw):
    if isinstance(raw, list):
        lines = [str(x) for x in raw]
    else:
        lines = str(raw or "").replace("\r", "\n").split("\n")
    out = []
    for ln in lines:
        ln = re.sub(r"^\s*(?:[-*•◦☐☑✓✔]|\[[ xX]?\])\s*", "", ln).strip()
        if ln:
            out.append(ln[:120])
    return out[:MAX_ITEMS]


def save_list(body):
    name = re.sub(r"\s+", " ", str(body.get("list") or body.get("name") or "").strip())[:40]
    if not name:
        raise ValueError('missing "list" (the list name)')
    with _list_lock:
        lists = load_lists()
        if body.get("delete"):
            lists.pop(name, None)
        else:
            if name not in lists and len(lists) >= MAX_LISTS:
                raise ValueError(f"already showing {MAX_LISTS} lists; delete one first")
            lists[name] = {"items": clean_items(body.get("items")),
                           "updated": int(time.time()), "order": lists.get(name, {}).get("order", len(lists))}
        write_json(LISTS_FILE, lists)
    n = len(lists.get(name, {}).get("items", []))
    log(f"list {name!r}: {'deleted' if body.get('delete') else f'{n} items'}")
    return {"ok": True, "list": name, "items": n}


def lists_payload():
    lists = load_lists()
    ordered = sorted(lists.items(), key=lambda kv: (kv[1].get("order", 99), kv[0].lower()))
    return {"stale_after": int(LIST_STALE_H * 3600), "now": int(time.time()),
            "lists": [{"name": k, "items": v.get("items", []), "updated": v.get("updated")} for k, v in ordered]}


# ---------------------------------------------------------------- look (wallpaper, blur)
def load_settings():
    try:
        s = json.loads(SETTINGS_FILE.read_text(encoding="utf-8"))
    except (FileNotFoundError, ValueError):
        s = {}
    out = {k: s.get(k, v) for k, v in LOOK_DEFAULTS.items()}
    out["album_ready"] = immich_ready()
    out["build"] = BUILD
    src = out.get("bg_mode")
    if src in DAILY_LABELS:
        a = daily_info(src)
        out["daily"] = dict({k: a.get(k) for k in ("date", "title", "copyright", "link", "error")},
                            source=src, label=DAILY_LABELS[src], ready=daily_img(src).exists())
    else:
        out["daily"] = {}
    out["unsplash_key_set"] = bool(unsplash_key())
    out["immich_key_set"] = bool(im_key())
    out["immich_album"] = im_album()
    out["ics_set"] = bool(cur_ics_saved()) or bool(ICS_URLS)
    out["ics_from_settings"] = bool(cur_ics_saved())
    out["wx_place_env"] = WX_PLACE
    # shown on /settings so the Shortcut can be set up from a phone; same LAN-only reach as the page itself
    out["list_token"] = LIST_TOKEN
    return out


def cur_ics_saved():
    return load_private().get("ics_url", "")


def write_json(path, obj):
    path.parent.mkdir(exist_ok=True)
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(obj, indent=1), encoding="utf-8")
    tmp.replace(path)


def save_settings(body):
    s = {k: v for k, v in load_settings().items() if k in LOOK_DEFAULTS}
    s["bg_type"] = bg_type()
    if "bg_mode" in body:
        if body["bg_mode"] not in ("default", "image", "album", *DAILY_LABELS):
            raise ValueError("unknown wallpaper choice")
        s["bg_mode"] = body["bg_mode"]
        if s["bg_mode"] in DAILY_LABELS:
            src = s["bg_mode"]
            threading.Thread(target=refresh_daily, args=(src,),
                             kwargs={"force": not daily_img(src).exists() or bool(daily_info(src).get("error"))},
                             daemon=True).start()
    if "unsplash_key" in body:
        key = re.sub(r"[^A-Za-z0-9_-]", "", str(body["unsplash_key"]))[:100]
        if key:
            try:
                fetch("https://api.unsplash.com/topics/nature", headers={"Authorization": f"Client-ID {key}"})
            except Exception as e:
                raise ValueError(f"Unsplash didn't accept that key ({e}). Use the Access Key, not the Secret key.")
        save_private(unsplash_key=key)
        (HERE / "data" / "unsplash.json").unlink(missing_ok=True)
        if s.get("bg_mode") == "unsplash" and key:
            threading.Thread(target=refresh_daily, args=("unsplash",), kwargs={"force": True}, daemon=True).start()
    if "bg_url" in body:
        url = str(body["bg_url"]).strip()[:2000]
        if url and not (re.match(r"^https?://", url, re.I) or url.startswith("/background")):
            raise ValueError("wallpaper must be an http(s) image address")
        s["bg_url"] = url
        if url:
            s["bg_mode"] = "image"
        if not url.startswith("/background") and BG_FILE.exists():
            BG_FILE.unlink()  # an upload that's no longer used
    if "bg_dim" in body:
        s["bg_dim"] = max(0, min(85, int(body["bg_dim"])))
    if "bg_every" in body:
        s["bg_every"] = max(1, min(1440, int(body["bg_every"])))
    if "ics_url" in body:
        url = str(body["ics_url"]).strip().replace("webcal://", "https://", 1)[:2000]
        if url and not re.match(r"^https://\S+$", url, re.I):
            raise ValueError("the calendar address should start with https:// (Google: Secret address in iCal format)")
        if url:  # check it before saving, so a bad paste shows up here and not as an empty week
            try:
                if b"BEGIN:VCALENDAR" not in fetch(url, timeout=20)[0][:2000]:
                    raise ValueError("that address didn't return a calendar; copy the Secret address in iCal format")
            except ValueError:
                raise
            except Exception as e:
                raise ValueError(f"couldn't load that calendar: {e}")
        save_private(ics_url=url)
        _cache.pop("week", None)
    if "immich_key" in body:
        key = str(body["immich_key"]).strip()[:200]
        if key:  # check it can list albums before saving
            try:
                immich("/api/albums", key=key)
            except Exception as e:
                raise ValueError(f"Immich didn't accept that key ({e}). It needs album.read, asset.read and asset.view.")
        save_private(immich_key=key)
        _cache.pop("photos", None)
        _cache.pop("faceperm", None)
    if "immich_album" in body:
        alb = str(body["immich_album"])
        save_private(immich_album="favorites" if alb == "favorites" else re.sub(r"[^0-9a-fA-F-]", "", alb)[:36])
        _cache.pop("photos", None)
    if "wx_place" in body:
        place = re.sub(r"\s+", " ", str(body["wx_place"])).strip()[:80]
        if place:
            loc = wx_location(place)  # raises with a readable message if not found
            _cache["wxloc:" + place] = (time.time(), loc)
        s["wx_place"] = place
        _cache.pop("weather", None)
    if "wx_units" in body:
        s["wx_units"] = "metric" if body["wx_units"] == "metric" else "us"
    if "color_rules" in body:
        rules = []
        for r in (body["color_rules"] or [])[:20]:
            words = ", ".join(w.strip()[:30] for w in str(r.get("words", "")).split(",") if w.strip())[:120]
            color = str(r.get("color", "")).strip()
            if words and re.fullmatch(r"#[0-9a-fA-F]{6}", color):
                rules.append({"words": words, "color": color.lower()})
        s["color_rules"] = rules
    if "text_scale" in body:
        s["text_scale"] = max(70, min(160, int(round(float(body["text_scale"]) / 5) * 5)))
    if "wx_days" in body:
        s["wx_days"] = int(body["wx_days"]) if str(body["wx_days"]) in ("3", "5", "7") else 3
    for k in ("wx_mono", "wx_bare"):
        if k in body:
            s[k] = bool(body[k])
        _cache.pop("weather", None)
    if "greet_name" in body:
        s["greet_name"] = re.sub(r"\s+", " ", str(body["greet_name"])).strip()[:40]
    if "quotes" in body:
        lines = [ln.strip()[:200] for ln in str(body["quotes"]).splitlines() if ln.strip()]
        s["quotes"] = "\n".join(lines[:365])
    for k in ("blur", "photo_panel", "photo_fill", "photo_videos", "quotes_only"):
        if k in body:
            s[k] = bool(body[k])
    if "photo_videos" in body:
        _cache.pop("photos", None)
    write_json(SETTINGS_FILE, s)
    return load_settings()


def save_background(data, ctype):
    if ctype not in BG_TYPES:
        raise ValueError("pick a JPG, PNG or WebP image")
    BG_FILE.parent.mkdir(exist_ok=True)
    tmp = BG_FILE.with_suffix(".tmp")
    tmp.write_bytes(data)
    tmp.replace(BG_FILE)
    s = {k: v for k, v in load_settings().items() if k in LOOK_DEFAULTS}
    s.update(bg_mode="image", bg_url=f"/background?v={int(time.time())}", bg_type=ctype)
    write_json(SETTINGS_FILE, s)
    return load_settings()


def bg_type():
    try:
        return json.loads(SETTINGS_FILE.read_text(encoding="utf-8")).get("bg_type") or "image/jpeg"
    except (FileNotFoundError, ValueError):
        return "image/jpeg"


# ---------------------------------------------------------------- picture of the day (wallpaper)
# Each source keeps today's picture in data/<source> and its details in data/<source>.json
# ({date, title, copyright, link, type, error, tried}). NASA's stays at data/apod as before.
DAILY_LABELS = {"apod": "NASA picture of the day", "bing": "Bing picture of the day",
                "commons": "Wikimedia picture of the day", "unsplash": "Unsplash"}
APOD_IMG = HERE / "data" / "apod"
APOD_MAX = 25 * 1024 * 1024
_daily_locks = {k: threading.Lock() for k in DAILY_LABELS}


def daily_img(src):
    return HERE / "data" / src


def daily_info(src):
    try:
        return json.loads((HERE / "data" / f"{src}.json").read_text(encoding="utf-8"))
    except (FileNotFoundError, ValueError):
        return {}


def apod_info():
    return daily_info("apod")


def apod_today():
    try:  # APOD rolls over at midnight US Eastern
        return dt.datetime.now(ZoneInfo("America/New_York")).date().isoformat()
    except Exception:
        return (dt.datetime.utcnow() - dt.timedelta(hours=5)).date().isoformat()


def local_today():
    return dt.date.today().isoformat()


# NASA's APOD feed. Ported from the start page (homepage/apod-feed.py): APOD moved to science.nasa.gov
# in 2026 and the old api.nasa.gov endpoint answers with a "NASA Science" logo stand-in or errors.
APOD_FEED = os.environ.get("APOD_FEED", "https://science.nasa.gov/feed/apod-basic/")
_MONTHS = {m: i for i, m in enumerate(("january", "february", "march", "april", "may", "june", "july", "august",
                                         "september", "october", "november", "december"), 1)}


def _strip_tags(s):
    return re.sub(r"\s+", " ", re.sub(r"<[^>]+>", "", s or "")).strip()


def apod_feed_items():
    """Items newest first. Date from the link slug apod-YYYY-month-DD; apod:hdurl is the image
    (anything that isn't .jpg/.png/.gif/.webp is a video day)."""
    root = ET.fromstring(fetch(APOD_FEED, timeout=20)[0])
    ns = {"apod": "https://science.nasa.gov/apod/"}
    out = []
    for it in root.iter("item"):
        link = (it.findtext("link") or "").strip()
        m = re.search(r"apod-(\d{4})-([a-z]+)-(\d{1,2})", link)
        date = (f"{m.group(1)}-{_MONTHS.get(m.group(2), 0):02d}-{int(m.group(3)):02d}"
                if m and m.group(2) in _MONTHS else "")
        img = (it.findtext("apod:hdurl", "", ns) or "").strip()
        is_img = bool(re.search(r"\.(jpe?g|png|gif|webp)(/|$|\?)", img, re.I)) and "youtube" not in img
        out.append({"date": date, "title": _strip_tags(it.findtext("title")), "link": link,
                    "media_type": "image" if is_img else "video", "hdurl": img, "url": img,
                    "copyright": _strip_tags(it.findtext("apod:copyright", "", ns)
                                             or it.findtext("apod:credit", "", ns))})
    return out


def apod_fetch():
    """Latest picture from the feed, or None on a video day when we already have a picture.
    With nothing cached yet, a video day falls back to the most recent picture in the feed."""
    items = [i for i in apod_feed_items() if i["date"]]
    if not items:
        raise RuntimeError("NASA's APOD feed had no entries")
    latest = items[0]
    if latest["media_type"] == "image":
        return latest
    if APOD_IMG.exists() and apod_info().get("title") not in (None, "", "NASA Science"):
        return None
    for i in items[1:]:
        if i["media_type"] == "image":
            log(f"apod: {latest['date']} is a video, showing {i['date']} until there's a picture")
            return i
    raise RuntimeError("no recent APOD pictures in NASA's feed")


def bing_fetch():
    """Bing's homepage picture: almost always a landscape or wildlife shot. No key."""
    d = json.loads(fetch("https://www.bing.com/HPImageArchive.aspx?format=js&idx=0&n=1&mkt=en-US")[0])
    im = (d.get("images") or [None])[0]
    if not im:
        raise RuntimeError("Bing sent no picture")
    base = "https://www.bing.com" + im["urlbase"]
    sd = im.get("startdate", "")
    title, credit = im.get("title") or "", im.get("copyright") or ""
    m = re.match(r"(.*?)\s*\((©.*)\)\s*$", credit)
    if m:
        credit = m.group(2).lstrip("© ").strip()
        title = title or m.group(1)
    return {"date": f"{sd[:4]}-{sd[4:6]}-{sd[6:8]}" if len(sd) == 8 else local_today(),
            "title": title, "copyright": credit, "link": im.get("copyrightlink") or "https://www.bing.com",
            "hdurl": base + "_1920x1080.jpg", "url": "https://www.bing.com" + im["url"]}


def commons_fetch():
    """Wikimedia Commons picture of the day (via Wikipedia's featured feed). No key.
    Often nature, sometimes architecture or a portrait-shaped photo."""
    today = dt.date.today()
    d = json.loads(fetch(f"https://en.wikipedia.org/api/rest_v1/feed/featured/{today:%Y/%m/%d}",
                         headers={"Accept": "application/json"})[0])
    im = d.get("image")
    if not im:
        raise RuntimeError("no Wikimedia picture today")
    orig = (im.get("image") or {}).get("source", "")
    thumb = (im.get("thumbnail") or {}).get("source", "")
    width = (im.get("image") or {}).get("width") or 0
    big = re.sub(r"/\d+px-", "/1920px-", thumb) if thumb and width > 1920 else orig
    return {"date": today.isoformat(), "title": _strip_tags((im.get("description") or {}).get("text"))[:160]
            or _strip_tags(im.get("title", "")).removeprefix("File:"),
            "copyright": _strip_tags((im.get("artist") or {}).get("text")),
            "link": im.get("file_page") or "https://commons.wikimedia.org/wiki/Commons:Picture_of_the_day",
            "hdurl": big, "url": orig}


def unsplash_key():
    return load_private().get("unsplash_key", "")


def unsplash_fetch(key=None):
    """One random landscape nature photo a day from Unsplash (free key). Unsplash asks apps to credit the
    photographer and to ping the photo's download link when it's used; both are done here."""
    key = key or unsplash_key()
    if not key:
        raise RuntimeError("add an Unsplash key on the Settings page")
    hdr = {"Authorization": f"Client-ID {key}", "Accept-Version": "v1"}
    q = urllib.parse.urlencode({"query": load_settings().get("unsplash_query") or "nature",
                                "orientation": "landscape", "content_filter": "high"})
    d = json.loads(fetch(f"https://api.unsplash.com/photos/random?{q}", headers=hdr)[0])
    try:
        fetch(d["links"]["download_location"], headers=hdr)
    except Exception:
        pass
    raw = d["urls"]["raw"]
    user = d.get("user") or {}
    ref = "?utm_source=kitchen_dashboard&utm_medium=referral"
    return {"date": local_today(), "title": (d.get("description") or d.get("alt_description") or "").strip()[:160],
            "copyright": (user.get("name") or "") + " on Unsplash",
            "link": (d.get("links") or {}).get("html", "https://unsplash.com") + ref,
            "hdurl": raw + ("&" if "?" in raw else "?") + "w=1920&h=1080&fit=crop&fm=jpg&q=80",
            "url": d["urls"].get("regular") or raw}


DAILY_FETCH = {"apod": apod_fetch, "bing": bing_fetch, "commons": commons_fetch, "unsplash": unsplash_fetch}
DAILY_TODAY = {"apod": apod_today}


def refresh_daily(src, force=False):
    """Get today's picture for one source if we don't have it; try again hourly. NASA's video days keep
    the last picture. On failure with nothing cached, the dashboard shows the default gradient."""
    lock = _daily_locks[src]
    if not lock.acquire(blocking=False):
        return
    img, meta = daily_img(src), HERE / "data" / f"{src}.json"
    try:
        info, today = daily_info(src), DAILY_TODAY.get(src, local_today)()
        if not force and (info.get("date") == today or info.get("checked") == today
                          or time.time() - info.get("tried", 0) < 3600):
            return
        info["tried"] = time.time()
        try:
            d = DAILY_FETCH[src]()
            if not d:
                info.update(checked=today, error=None)
                log(f"{src}: video day, keeping the last picture")
            elif d.get("date") == info.get("date") and img.exists():
                info["error"] = None   # already have it; today's isn't out yet
            else:
                data, ctype = b"", ""
                for u in [x for x in (d.get("hdurl"), d.get("url")) if x]:
                    try:
                        data, ctype = fetch(u, timeout=60)
                    except Exception as e:
                        log(f"{src}: {u}: {e}")
                        continue
                    if 0 < len(data) <= APOD_MAX:
                        break
                if not data or len(data) > APOD_MAX:
                    raise RuntimeError("couldn't download the picture")
                tmp = img.with_suffix(".tmp")
                tmp.write_bytes(data)
                tmp.replace(img)
                ctype = (ctype or "").split(";")[0].strip()
                info.update(date=d.get("date") or today, checked=d.get("date") or today, title=d.get("title", ""),
                            copyright=(d.get("copyright") or "").strip().replace("\n", " "),
                            link=d.get("link") or "", error=None,
                            type=ctype if ctype.startswith("image/") else "image/jpeg")
                log(f"{src} {info['date']}: {info['title']} ({len(data) // 1024} KB)")
        except Exception as e:
            info["error"] = str(e)[:200]
            log(f"{src}: {e}")
        write_json(meta, info)
    finally:
        lock.release()


def refresh_apod(force=False):
    refresh_daily("apod", force)


def daily_loop():
    while True:
        try:
            mode = load_settings().get("bg_mode")
            if mode in DAILY_FETCH:
                refresh_daily(mode)
        except Exception as e:
            log(f"daily picture loop: {e}")
        time.sleep(600)


# ---------------------------------------------------------------- Immich album
def im_key():
    return load_private().get("immich_key") or IMMICH_KEY


def im_album():
    return load_private().get("immich_album") or IMMICH_ALBUM


def immich_ready():
    return bool(IMMICH_URL and im_key() and im_album())


def immich_albums():
    if not im_key():
        return {"albums": [], "error": "no Immich key yet"}
    al = immich("/api/albums")
    al += [a for a in immich("/api/albums?shared=true") if a.get("id") not in {x.get("id") for x in al}]
    out = [{"id": a.get("id"), "name": a.get("albumName") or "(untitled)", "count": a.get("assetCount", 0)} for a in al]
    out.sort(key=lambda a: a["name"].lower())
    return {"albums": out}


def immich(path, method="GET", body=None, key=None):
    data = json.dumps(body).encode() if body is not None else None
    hdr = {"x-api-key": key or im_key(), "Accept": "application/json"}
    if data:
        hdr["Content-Type"] = "application/json"
    return json.loads(fetch(f"{IMMICH_URL}{path}", headers=hdr, method=method, body=data, timeout=30)[0])


def photos_payload():
    if not immich_ready():
        return {"ids": []}
    want_video = load_settings().get("photo_videos")
    items = []
    try:  # newer servers: album contents through search
        page = 1
        while page and len(items) < 5000:
            # "favorites": every photo and video hearted in Immich (Favorites is a view there, not an album)
            q = {"isFavorite": True} if im_album() == "favorites" else {"albumIds": [im_album()]}
            q.update(size=1000, page=page)
            if not want_video:
                q["type"] = "IMAGE"
            r = immich("/api/search/metadata", "POST", q)
            assets = r.get("assets", {})
            items += assets.get("items", [])
            page = assets.get("nextPage")
            page = int(page) if page else None
    except Exception as e:
        log(f"immich search: {e}; trying the album endpoint")
        items = []
    if not items and im_album() != "favorites":
        items = immich(f"/api/albums/{urllib.parse.quote(im_album())}").get("assets", [])
    ids = [x["id"] for x in items if x.get("type", "IMAGE") == "IMAGE"]
    # short clips only (the kiosk plays them muted and on a loop until the next change)
    videos = [x["id"] for x in items if want_video and x.get("type") == "VIDEO"
              and 0 < clip_seconds(x.get("duration")) <= VIDEO_MAX_S]
    ids += videos
    random.shuffle(ids)
    all_v = [x for x in items if x.get("type") == "VIDEO"]
    return {"ids": ids, "videos": videos,
            # why a video might be missing, shown at /api/photos
            "video_info": {"switch_on": bool(want_video), "in_album": len(all_v) if want_video else "switch is off",
                           "too_long": sum(1 for x in all_v if clip_seconds(x.get("duration")) > VIDEO_MAX_S),
                           "max_seconds": VIDEO_MAX_S}}


VIDEO_MAX_S = int(os.environ.get("VIDEO_MAX_S", "60"))


def clip_seconds(d):
    """Immich durations look like "0:00:12.345"."""
    try:
        h, m, s = str(d).split(":")
        return int(h) * 3600 + int(m) * 60 + float(s)
    except ValueError:
        return 0


def with_faces(out):
    """Settings plus whether the key can read faces (kept apart from load_settings, which
    photos_payload calls)."""
    if out.get("album_ready"):
        out["faces"] = cached("faceperm", 3600, face_status)
    return out


def face_status():
    """"ok" if the key can read Immich's face data, "no_permission" if it lacks face.read."""
    ids = [i for i in (cached("photos", 3600, photos_payload).get("ids") or [])][:1]
    if not ids:
        return "unknown"
    try:
        immich(f"/api/faces?id={ids[0]}")
        return "ok"
    except urllib.error.HTTPError as e:
        return "no_permission" if e.code in (401, 403) else "unknown"
    except Exception:
        return "unknown"


# Where the people are in a photo, so a cropped photo keeps them in frame. Immich has already found
# the faces; this reads their boxes (needs face.read on the API key). Kept for the life of the server.
_focus = {}


def photo_focus(aid):
    if aid in _focus:
        return _focus[aid]
    out = {}
    try:
        faces = immich(f"/api/faces?id={aid}")
        boxes = [(f["boundingBoxX1"] / f["imageWidth"], f["boundingBoxY1"] / f["imageHeight"],
                  f["boundingBoxX2"] / f["imageWidth"], f["boundingBoxY2"] / f["imageHeight"])
                 for f in faces if f.get("imageWidth") and f.get("imageHeight")]
        if boxes:
            # the subjects: faces at least half as tall as the biggest one, so people in the
            # background don't stretch the crop past what fits
            big = max(b[3] - b[1] for b in boxes)
            main = [b for b in boxes if b[3] - b[1] >= big * 0.5]
            top = max(boxes, key=lambda b: b[3] - b[1])

            def padded(bs):
                x1, y1 = min(b[0] for b in bs), min(b[1] for b in bs)
                x2, y2 = max(b[2] for b in bs), max(b[3] for b in bs)
                fh = max(b[3] - b[1] for b in bs)   # a little room above heads, more below for shoulders
                return [round(x1, 4), round(max(0.0, y1 - fh * 0.4), 4), round(x2, 4), round(min(1.0, y2 + fh * 0.8), 4)]
            x1, y1, x2, y2 = padded(main)
            out = {"x1": x1, "y1": y1, "x2": x2, "y2": y2, "one": padded([top]), "faces": len(boxes)}
    except Exception as e:
        log(f"faces {aid}: {e}")
        return {}   # don't remember failures (key may get face.read later)
    if len(_focus) > 5000:
        _focus.clear()
    _focus[aid] = out
    return out


# ---------------------------------------------------------------- server
class Handler(BaseHTTPRequestHandler):
    server_version = "homelab-family"

    def log_message(self, fmt, *args):
        pass

    def send_body(self, body, ctype, cache="no-store", status=200):
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Cache-Control", cache)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def send_json(self, obj, status=200):
        self.send_body(json.dumps(obj).encode(), "application/json", status=status)

    def stream_video(self, aid):
        """Pass Immich's playback file (its smaller transcode when there is one) through, with byte
        ranges so Chromium can seek and loop, in chunks so memory stays flat."""
        h = {"x-api-key": im_key(), "User-Agent": "homelab-family/1"}
        if self.headers.get("Range"):
            h["Range"] = self.headers["Range"]
        req = urllib.request.Request(f"{IMMICH_URL}/api/assets/{aid}/video/playback", headers=h)
        try:
            r = urllib.request.urlopen(req, timeout=30)
        except urllib.error.HTTPError as e:
            self.send_error(e.code)
            return
        with r:
            self.send_response(r.status)
            for k in ("Content-Type", "Content-Length", "Content-Range", "Accept-Ranges"):
                if r.headers.get(k):
                    self.send_header(k, r.headers[k])
            self.send_header("Cache-Control", "public, max-age=86400")
            self.end_headers()
            try:
                while chunk := r.read(256 * 1024):
                    self.wfile.write(chunk)
            except (BrokenPipeError, ConnectionResetError):
                pass   # the browser often stops after the bytes it needs

    def do_POST(self):
        path = urllib.parse.urlparse(self.path).path
        if path == "/api/background":
            try:
                length = int(self.headers.get("Content-Length", 0))
                if not 0 < length <= BG_MAX:
                    raise ValueError("image must be under 25 MB")
                ctype = self.headers.get("Content-Type", "").split(";")[0].strip().lower()
                self.send_json(save_background(self.rfile.read(length), ctype))
            except Exception as e:
                self.close_connection = True
                self.send_json({"error": str(e)}, 400)
            return
        if path == "/api/settings":
            try:
                length = min(int(self.headers.get("Content-Length", 0)), 16 * 1024)
                self.send_json(with_faces(save_settings(json.loads(self.rfile.read(length) or b"{}"))))
            except Exception as e:
                self.send_json({"error": str(e)}, 400)
            return
        if path != "/api/lists":
            self.send_error(HTTPStatus.NOT_FOUND)
            return
        sent = self.headers.get("Authorization", "").removeprefix("Bearer ").strip()
        if not LIST_TOKEN or not hmac.compare_digest(sent, LIST_TOKEN):
            self.send_json({"error": "wrong or missing token (LIST_TOKEN)"}, 401)
            return
        try:
            length = min(int(self.headers.get("Content-Length", 0)), 128 * 1024)
            raw = self.rfile.read(length) or b"{}"
            ctype = self.headers.get("Content-Type", "")
            if "json" in ctype:
                body = json.loads(raw)
            else:  # form fields also work
                body = {k: v[0] for k, v in urllib.parse.parse_qs(raw.decode()).items()}
            self.send_json(save_list(body))
        except Exception as e:
            self.send_json({"error": str(e)}, 400)

    def do_GET(self):
        path = urllib.parse.urlparse(self.path).path
        try:
            if path in ("/", "/index.html"):
                page = (HERE / "index.html").read_bytes().replace(b"__PAGE_BUILD__", BUILD.encode())
                self.send_body(page, "text/html; charset=utf-8", "no-store")
            elif path == "/settings":
                self.send_body((HERE / "settings.html").read_bytes(), "text/html; charset=utf-8", "no-cache")
            elif path == "/api/settings":
                self.send_json(with_faces(load_settings()))
            elif path == "/background":
                if not BG_FILE.exists():
                    self.send_error(HTTPStatus.NOT_FOUND)
                    return
                self.send_body(BG_FILE.read_bytes(), bg_type(), "public, max-age=31536000, immutable")
            elif path == "/api/immich/albums":
                try:
                    self.send_json(immich_albums())
                except Exception as e:
                    self.send_json({"albums": [], "error": str(e)})
            elif path == "/apod" or (path.startswith("/daily/") and path[7:] in DAILY_LABELS):
                src = "apod" if path == "/apod" else path[7:]
                if not daily_img(src).exists():
                    self.send_error(HTTPStatus.NOT_FOUND)
                    return
                self.send_body(daily_img(src).read_bytes(), daily_info(src).get("type") or "image/jpeg",
                               "public, max-age=86400")
            elif path == "/api/weather":
                self.send_json(cached("weather", 900, weather_payload))
            elif path == "/api/week":
                self.send_json(cached("week", 300, week_payload))
            elif path == "/api/lists":
                self.send_json(lists_payload())
            elif path == "/api/photos":
                self.send_json(cached("photos", 3600, photos_payload))
            elif path.startswith("/api/focus/") and immich_ready():
                aid = path.split("/")[3]
                if not re.fullmatch(r"[0-9a-fA-F-]{36}", aid):
                    self.send_error(HTTPStatus.NOT_FOUND)
                    return
                self.send_json(photo_focus(aid))
            elif path.startswith("/video/") and immich_ready():
                aid = path.split("/")[2]
                if not re.fullmatch(r"[0-9a-fA-F-]{36}", aid):
                    self.send_error(HTTPStatus.NOT_FOUND)
                    return
                self.stream_video(aid)
            elif path.startswith("/photo/") and immich_ready():
                aid = path.split("/")[2]
                if not re.fullmatch(r"[0-9a-fA-F-]{36}", aid):
                    self.send_error(HTTPStatus.NOT_FOUND)
                    return
                body, ctype = fetch(f"{IMMICH_URL}/api/assets/{aid}/thumbnail?size=preview",
                                    headers={"x-api-key": im_key()}, timeout=30)
                self.send_body(body, ctype or "image/jpeg", "public, max-age=86400")
            elif path == "/healthz":
                self.send_json({"ok": True})
            else:
                self.send_error(HTTPStatus.NOT_FOUND)
        except Exception as e:
            log(f"{path}: {e}")
            self.send_json({"error": str(e)}, 500)


def main():
    log(f"listening on :{PORT}  calendars={len(ics_sources())}  calendar-libs={'yes' if icalendar else 'no'}  "
        f"weather={'yes' if cur_place() else 'no'}  list-token={'set' if LIST_TOKEN else 'MISSING'}  "
        f"photos={'yes' if immich_ready() else 'no'}  tz={LOCAL_TZ}")
    threading.Thread(target=daily_loop, daemon=True).start()
    ThreadingHTTPServer(("0.0.0.0", PORT), Handler).serve_forever()


if __name__ == "__main__":
    main()
