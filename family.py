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
  GET  /app             the family app for phones: lists, messages, settings (add it to the home screen)
  GET  /settings        old address of the settings page; sends you to /app#settings
  GET/POST /api/app/lists  lists made in the app (data/family.db), plus the Shortcut's lists read-only
  GET/POST /api/auth    the parent PIN: whether it's set, unlocking, changing it
  GET/POST /api/rpg     quests, characters, XP and levels, gold and the reward shop (data/family.db)
  GET/POST /api/screen  the Remote: which detail page a phone put on the kitchen screen, and until when
  GET  /api/month?m=YYYY-MM  six weeks of events around that month, for the month page
  GET/POST /api/settings  wallpaper mode, image address, darken, glass blur, photo panel (data/settings.json)
  POST /api/avatar      a profile picture (?person=&by=, body a small JPEG; empty body removes it)
  GET  /avatar/<name>   that picture
  POST /api/background  upload a wallpaper image (the settings page shrinks it to screen size first)
  GET  /background      the uploaded wallpaper
  GET  /apod, /daily/<source>  today's picture-of-the-day wallpaper (apod, bing, commons, unsplash)

Standard library plus `icalendar` + `recurring-ical-events`, which the compose file pip-installs
into /app/vendor on first start.

Environment (see env.example):
  PORT          default 8096
  TZ            e.g. America/Chicago
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
import base64
import email
import email.policy
import email.utils
import hashlib
import html as htmllib
import imaplib
import ipaddress
import hmac
import json
import os
import random
import re
import secrets
import sqlite3
import sys
import ssl
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
NOTES_FILE = HERE / "data" / "notes.json"
MAX_NOTES = 30
SETTINGS_FILE = HERE / "data" / "settings.json"
BG_FILE = HERE / "data" / "background"
BG_TYPES = {"image/jpeg", "image/png", "image/webp"}
BG_MAX = 25 * 1024 * 1024
AVATAR_DIR = HERE / "data" / "avatars"           # profile pictures, one small JPEG per person
AVATAR_MAX = 600 * 1024
DB_FILE = HERE / "data" / "family.db"           # lists made in the app, parent sign-ins (SQLite)
PRIVATE_FILE = HERE / "data" / "private.json"   # calendar address, Immich key: readable only by the server
LOOK_DEFAULTS = {"wx_place": "", "wx_units": "", "bg_mode": "default", "bg_url": "", "bg_dim": 30, "bg_every": 10, "blur": True, "photo_panel": True, "photo_fill": False, "photo_videos": False, "wx_days": 3, "wx_mono": False, "wx_bare": False, "text_scale": 100,
                 "color_rules": [{"words": "Kid 1", "color": "#f06262"}, {"words": "Kid 2", "color": "#a57cf5"},
                                 {"words": "Mom", "color": "#3cc48a"}, {"words": "Dad", "color": "#5b9bff"}],
                 "greet_name": "", "quotes": "", "quotes_only": False, "notes_days": 3, "msg_sound": True, "rpg_on": True, "kiosk_lists": False, "goals_on": True, "habits_on": True, "fitness_on": True,
                 "people": [{"name": "Kid 1", "color": "#f06262"}, {"name": "Kid 2", "color": "#a57cf5"},
                            {"name": "Mom", "color": "#3cc48a"}, {"name": "Dad", "color": "#5b9bff"}]}
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
        return {"error": "set your city in the family app's Settings (/app on a phone)"}
    loc = cached("wxloc:" + place, 7 * 86400, lambda: wx_location(place))
    if "error" in loc:
        return loc
    metric = units == "metric"
    q = urllib.parse.urlencode({
        "latitude": loc["lat"], "longitude": loc["lon"], "timezone": "auto", "forecast_days": 7, "forecast_hours": 24,
        "current": "temperature_2m,apparent_temperature,weather_code,is_day,relative_humidity_2m,wind_speed_10m",
        "daily": "weather_code,temperature_2m_max,temperature_2m_min,precipitation_probability_max,sunrise,sunset",
        "hourly": "temperature_2m,weather_code,precipitation_probability,is_day",
        "temperature_unit": "celsius" if metric else "fahrenheit", "wind_speed_unit": "kmh" if metric else "mph"})
    d = json.loads(fetch(f"{WX_API}?{q}")[0])
    c, day = d.get("current", {}), d.get("daily", {})
    days = []
    for i, date in enumerate(day.get("time", [])[:7]):
        code = (day.get("weather_code") or [None] * 7)[i]
        days.append({"date": date, "code": code, "text": WEATHER_CODES.get(code, ""),
                     "high": day["temperature_2m_max"][i], "low": day["temperature_2m_min"][i],
                     "rain": (day.get("precipitation_probability_max") or [None] * 7)[i],
                     "sunrise": (day.get("sunrise") or [""] * 7)[i], "sunset": (day.get("sunset") or [""] * 7)[i]})
    hr = d.get("hourly", {})
    hours = [{"time": t, "temp": hr["temperature_2m"][i], "code": hr["weather_code"][i],
              "rain": (hr.get("precipitation_probability") or [None] * 24)[i], "is_day": (hr.get("is_day") or [1] * 24)[i]}
             for i, t in enumerate(hr.get("time", [])[:24])]
    return {"place": loc["name"], "units": units, "temp": c.get("temperature_2m"),
            "feels": c.get("apparent_temperature"), "code": c.get("weather_code"),
            "text": WEATHER_CODES.get(c.get("weather_code"), ""), "is_day": c.get("is_day", 1),
            "humidity": c.get("relative_humidity_2m"), "wind": c.get("wind_speed_10m"), "days": days, "hours": hours}


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
    today = dt.datetime.now(LOCAL_TZ).replace(hour=0, minute=0, second=0, microsecond=0)
    monday = today - dt.timedelta(days=today.weekday())
    out = events_between(monday, monday + dt.timedelta(days=7))
    if "events" in out:
        out["monday"] = monday.date().isoformat()
    return out


def month_payload(ym):
    """A month grid for the kitchen screen's Remote pages: Monday on or before the 1st, six weeks."""
    y, m = (int(x) for x in ym.split("-"))
    first = dt.datetime(y, m, 1, tzinfo=LOCAL_TZ)
    start = first - dt.timedelta(days=first.weekday())
    out = events_between(start, start + dt.timedelta(days=42))
    out.update(month=f"{y:04d}-{m:02d}", start=start.date().isoformat())
    return out


def events_between(monday, sunday_end):
    if icalendar is None:
        return {"error": "calendar libraries still installing; restart the container if this stays"}
    if not cur_ics():
        return {"error": "paste the Google calendar's secret iCal address in the family app's Settings (/app on a phone)"}
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
    return {"events": events, "errors": errors}


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


# ---------------------------------------------------------------- notes (family message board)
def load_notes():
    try:
        return json.loads(NOTES_FILE.read_text(encoding="utf-8"))
    except (FileNotFoundError, ValueError):
        return []


def live_notes():
    """Newest first, minus the ones older than the "keep notes for" setting (0 keeps them until removed)."""
    try:
        days = int(json.loads(SETTINGS_FILE.read_text(encoding="utf-8")).get("notes_days", 3))
    except (FileNotFoundError, ValueError, TypeError):
        days = 3
    cutoff = time.time() - days * 86400 if days > 0 else 0
    return sorted((n for n in load_notes() if n.get("at", 0) >= cutoff), key=lambda n: -n.get("at", 0))


def save_note(body):
    with _list_lock:
        notes = load_notes()
        if body.get("clear"):
            notes = []
            what = "all cleared"
        elif body.get("delete"):
            nid = str(body["delete"])
            notes = [n for n in notes if n.get("id") != nid]
            what = f"{nid} removed"
        else:
            text = str(body.get("text") or body.get("note") or body.get("message") or "").replace("\r", "").strip()
            text = re.sub(r"\n{3,}", "\n\n", text)[:300]
            if not text:
                raise ValueError('missing "text" (the note)')
            who = re.sub(r"\s+", " ", str(body.get("from") or body.get("name") or "").strip())[:24]
            n = {"id": hashlib.sha1(f"{time.time()}{text}".encode()).hexdigest()[:10], "text": text,
                 "from": who, "at": int(time.time())}
            notes = sorted([n] + notes, key=lambda x: -x.get("at", 0))[:MAX_NOTES]
            what = f"from {who or '?'}: {len(text)} chars"
        write_json(NOTES_FILE, notes)
    log(f"note {what}")
    return {"ok": True, "notes": live_notes()}


# ---------------------------------------------------------------- notes by text message (Twilio)
def phone_key(num):
    d = re.sub(r"\D", "", str(num))
    return d[-10:] if len(d) >= 10 else ""


def sms_people():
    """Settings lines like "+1 405 555 1234 = Mom". Only these numbers can post; the name becomes "from"."""
    out = {}
    for ln in str(load_private().get("sms_people", "")).splitlines():
        num, _, name = ln.partition("=")
        k = num.strip().lower() if "@" in num else phone_key(num)   # an email address works too
        if k:
            out[k] = re.sub(r"\s+", " ", name.strip())[:24]
    return out


def twilio_ok(url, params, sig):
    """Twilio signs each webhook: base64 HMAC-SHA1 of the URL plus every POST field (sorted, name+value),
    keyed with the account's Auth Token. A forged request without the token can't match."""
    token = load_private().get("twilio_token", "")
    if not token or not sig:
        return False
    msg = url + "".join(k + v for k, v in sorted(params.items()))
    want = base64.b64encode(hmac.new(token.encode(), msg.encode(), hashlib.sha1).digest()).decode()
    return hmac.compare_digest(want, sig)


def sms_note(url, params, sig):
    if not twilio_ok(url, params, sig):
        log("sms refused: bad or missing Twilio signature (check the Auth Token in settings)")
        return "bad"
    who = sms_people().get(phone_key(params.get("From", "")))
    if who is None:
        log(f"sms ignored: {params.get('From', '?')[-4:].rjust(10, '*')} isn't on the allowed list")
        return "ignored"
    text = params.get("Body", "").strip()
    if text:
        save_note({"text": text, "from": who})
    return "ok"


# ---------------------------------------------------------------- notes by text message, free route
# An iPhone texting an email address (one that isn't an Apple ID) sends MMS, and the carrier delivers it
# as an email from <number>@mms.att.net / vzwpix.com / tmomail.net... The board reads that inbox.
MAIL_BOILER = re.compile(r"(this mobile text message is brought to you by|this message was sent using the picture|"
                         r"to learn how you can receive|^\s*--\s*$|^\s*sent from my)", re.I)
_mail_status = {}


def mail_text(msg):
    plain, htm = [], []
    for part in msg.walk():
        ctype = part.get_content_type()
        if part.is_multipart() or ctype not in ("text/plain", "text/html"):
            continue
        try:
            raw = part.get_payload(decode=True) or b""
            txt = raw.decode(part.get_content_charset() or "utf-8", "replace")
        except Exception:
            continue
        (plain if ctype == "text/plain" else htm).append(txt)
    if not plain and htm:
        t = re.sub(r"(?is)<(script|style).*?</\1>", "", "\n".join(htm))
        t = re.sub(r"(?i)<br\s*/?>|</p>|</div>|</tr>", "\n", t)
        plain = [htmllib.unescape(re.sub(r"<[^>]+>", "", t))]
    lines = []
    for ln in "\n".join(plain).splitlines():
        if MAIL_BOILER.search(ln):
            break       # carrier footers and signatures come last
        lines.append(ln.strip())
    return re.sub(r"\n{3,}", "\n\n", "\n".join(lines)).strip()


def mail_server(p):
    """"host" or "host:port"; blank is Gmail. 993 means TLS from the start, any other port starts plain and
    upgrades with STARTTLS (Proton Mail Bridge listens that way on 1143)."""
    raw = str(p.get("mail_host") or "").strip() or "imap.gmail.com"
    host, _, port = raw.rpartition(":") if re.search(r":\d+$", raw) else (raw, "", "993")
    return host, int(port)


def is_lan(host):
    try:
        return ipaddress.ip_address(host).is_private
    except ValueError:
        return host in ("localhost",) or "." not in host   # a container name on the same Docker network


def mail_login(p=None):
    p = p or load_private()
    host, port = mail_server(p)
    # Bridge and other home-network servers use a self-signed certificate; public servers must have a real one
    ctx = ssl.create_default_context()
    if is_lan(host):
        ctx.check_hostname, ctx.verify_mode = False, ssl.CERT_NONE
    if port == 993:
        M = imaplib.IMAP4_SSL(host, port, ssl_context=ctx, timeout=20)
    else:
        M = imaplib.IMAP4(host, port, timeout=20)
        if "STARTTLS" in M.capabilities:
            M.starttls(ssl_context=ctx)
        elif not is_lan(host):
            M.shutdown()
            raise ValueError(f"{host}:{port} doesn't offer STARTTLS; won't send the password unencrypted")
    M.login(p["mail_user"], p["mail_pass"])
    return M


def check_mail():
    p = load_private()
    if not (p.get("mail_user") and p.get("mail_pass")):
        return
    people = sms_people()
    M = mail_login(p)
    try:
        M.select("INBOX")
        # only mail sent to the board's own address: on Proton, Bridge signs in to the whole account,
        # so the inbox can also hold your personal mail, which the board leaves alone (and unread)
        user = p["mail_user"]
        _, data = M.search(None, "UNSEEN", "TO", '"' + user.replace('"', "") + '"') if "@" in user else M.search(None, "UNSEEN")
        for num in (data[0] or b"").split()[:20]:
            _, got = M.fetch(num, "(RFC822)")     # fetching marks it read, so each text posts once
            msg = email.message_from_bytes(got[0][1], policy=email.policy.default)
            sender = email.utils.parseaddr(msg.get("From", ""))[1]
            who = people.get(sender.lower(), people.get(phone_key(sender.split("@")[0])))
            if who is None:
                log(f"text-by-email ignored: {sender.split('@')[-1]} sender isn't a listed number")
                continue
            # the iPhone's subject field forces MMS; if someone types only a subject, show that
            text = (mail_text(msg) or str(msg.get("Subject", "")).strip())[:300]
            if text:
                save_note({"text": text, "from": who})
    finally:
        try:
            M.logout()
        except Exception:
            pass


def mail_loop():
    while True:
        try:
            check_mail()
            _mail_status.update(ok=int(time.time()), error="")
        except Exception as e:
            _mail_status.update(error=str(e)[:200])
            log(f"text-by-email: {e}")
        time.sleep(60)


def lists_payload(with_app=False):
    lists = load_lists()
    ordered = sorted(lists.items(), key=lambda kv: (kv[1].get("order", 99), kv[0].lower()))
    out = [{"name": k, "items": v.get("items", []), "updated": v.get("updated")} for k, v in ordered]
    if with_app:   # the kiosk: lists made in the app (unchecked items only) after the Shortcut's
        with _db_lock:
            con = db()
            try:
                out += app_lists(con, kiosk=True)
            finally:
                con.close()
    res = {"stale_after": int(LIST_STALE_H * 3600), "now": int(time.time()), "lists": out, "notes": live_notes()}
    if with_app:
        try:
            res["party"] = party_for_kiosk()
        except Exception as e:     # the lists must still show if the quest data has a problem
            log(f"party: {e}")
            res["party"] = {"on": False, "members": []}
    return res


# ---------------------------------------------------------------- the app's own data (SQLite)
# Lists made in the app live in data/family.db, next to (not mixed with) the Shortcut's lists.json:
# the Shortcut replaces a whole list each time it runs, so its lists stay read-only in the app.
_db_lock = threading.Lock()
APP_MAX_LISTS = 30
APP_MAX_ITEMS = 200
DONE_KEEP_DAYS = 30     # checked-off items stay under "Done" this long, so re-adding "milk" is one tap
SCHEMA = """
CREATE TABLE IF NOT EXISTS lists(id INTEGER PRIMARY KEY, name TEXT NOT NULL, pos INTEGER NOT NULL DEFAULT 0,
  show INTEGER NOT NULL DEFAULT 1, created INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS items(id INTEGER PRIMARY KEY, list_id INTEGER NOT NULL REFERENCES lists(id) ON DELETE CASCADE,
  text TEXT NOT NULL, done INTEGER NOT NULL DEFAULT 0, pos INTEGER NOT NULL DEFAULT 0, created INTEGER NOT NULL,
  added_by TEXT NOT NULL DEFAULT '', done_at INTEGER, done_by TEXT NOT NULL DEFAULT '');
CREATE INDEX IF NOT EXISTS items_list ON items(list_id, done, pos);
CREATE TABLE IF NOT EXISTS sessions(hash TEXT PRIMARY KEY, created INTEGER NOT NULL, seen INTEGER NOT NULL);
"""


def db():
    """One short-lived connection per call, under a lock: the server is small and writes are rare."""
    DB_FILE.parent.mkdir(exist_ok=True)
    con = sqlite3.connect(DB_FILE, timeout=10, isolation_level=None)
    con.row_factory = sqlite3.Row
    con.execute("PRAGMA foreign_keys=ON")
    return con


def db_init():
    with _db_lock:
        con = db()
        try:
            con.execute("PRAGMA journal_mode=WAL")
            con.executescript(SCHEMA + RPG_SCHEMA)
        finally:
            con.close()


def who_name(v):
    return re.sub(r"\s+", " ", str(v or "").strip())[:24]


def app_lists(con, kiosk=False):
    con.execute("DELETE FROM items WHERE done=1 AND done_at < ?", (int(time.time()) - DONE_KEEP_DAYS * 86400,))
    out = []
    for l in con.execute("SELECT * FROM lists ORDER BY pos, id"):
        if kiosk and not l["show"]:
            continue
        rows = con.execute("SELECT * FROM items WHERE list_id=? ORDER BY done, CASE WHEN done THEN -done_at ELSE pos END, id",
                           (l["id"],)).fetchall()
        items = [{"id": r["id"], "text": r["text"], "done": bool(r["done"]), "by": r["added_by"],
                  "done_by": r["done_by"], "done_at": r["done_at"]} for r in rows]
        if kiosk:
            items = [i["text"] for i in items if not i["done"]]
        out.append({"id": l["id"], "name": l["name"], "show": bool(l["show"]), "items": items, "app": True})
    return out


def app_lists_payload():
    with _db_lock:
        con = db()
        try:
            mine = app_lists(con)
        finally:
            con.close()
    rem = lists_payload()
    return {"now": int(time.time()), "lists": mine, "reminders": rem["lists"], "stale_after": rem["stale_after"]}


def list_name(v):
    name = re.sub(r"\s+", " ", str(v or "").strip())[:40]
    if not name:
        raise ValueError("give the list a name")
    return name


def app_list_change(body, parent):
    """Every change the app makes to its lists. Answers with all the lists, so the phone redraws from the truth."""
    op = str(body.get("op", ""))
    now = int(time.time())
    by = who_name(body.get("by"))
    if op == "reminders_remove":         # take a Shortcut list off the screen (the old Remove on /settings)
        if not parent:
            raise PermissionError("parent PIN needed to remove a list")
        save_list({"list": body.get("name"), "delete": True})
        return app_lists_payload()
    with _db_lock:
        con = db()
        try:
            con.execute("BEGIN IMMEDIATE")
            if op == "list_add":
                name = list_name(body.get("name"))
                if con.execute("SELECT COUNT(*) FROM lists").fetchone()[0] >= APP_MAX_LISTS:
                    raise ValueError(f"that's {APP_MAX_LISTS} lists already; delete one first")
                if con.execute("SELECT 1 FROM lists WHERE lower(name)=lower(?)", (name,)).fetchone():
                    raise ValueError(f"there's already a list called {name}")
                pos = con.execute("SELECT COALESCE(MAX(pos),0)+1 FROM lists").fetchone()[0]
                con.execute("INSERT INTO lists(name,pos,created) VALUES(?,?,?)", (name, pos, now))
            elif op == "list_rename":
                con.execute("UPDATE lists SET name=? WHERE id=?", (list_name(body.get("name")), int(body["id"])))
            elif op == "list_show":
                con.execute("UPDATE lists SET show=? WHERE id=?", (1 if body.get("show") else 0, int(body["id"])))
            elif op == "list_move":         # one step up (-1) or down (+1)
                ids = [r[0] for r in con.execute("SELECT id FROM lists ORDER BY pos, id")]
                i, step = ids.index(int(body["id"])), (1 if int(body.get("dir", 1)) > 0 else -1)
                if 0 <= i + step < len(ids):
                    ids[i], ids[i + step] = ids[i + step], ids[i]
                con.executemany("UPDATE lists SET pos=? WHERE id=?", [(n, x) for n, x in enumerate(ids)])
            elif op == "list_delete":
                if not parent:
                    raise PermissionError("parent PIN needed to delete a list")
                con.execute("DELETE FROM lists WHERE id=?", (int(body["id"]),))
            elif op == "item_add":          # one item per line, so a pasted list works
                lid = int(body["list"])
                if not con.execute("SELECT 1 FROM lists WHERE id=?", (lid,)).fetchone():
                    raise ValueError("that list is gone; pull down to refresh")
                for text in clean_items(body.get("text"))[:50]:
                    old = con.execute("SELECT id, done FROM items WHERE list_id=? AND lower(text)=lower(?)", (lid, text)).fetchone()
                    if old:                 # already there: bring a checked-off one back instead of a duplicate
                        if old["done"]:
                            pos = con.execute("SELECT COALESCE(MAX(pos),0)+1 FROM items WHERE list_id=?", (lid,)).fetchone()[0]
                            con.execute("UPDATE items SET done=0, done_at=NULL, done_by='', pos=?, added_by=? WHERE id=?", (pos, by, old["id"]))
                        continue
                    if con.execute("SELECT COUNT(*) FROM items WHERE list_id=?", (lid,)).fetchone()[0] >= APP_MAX_ITEMS:
                        raise ValueError(f"a list holds {APP_MAX_ITEMS} items; clear some done ones first")
                    pos = con.execute("SELECT COALESCE(MAX(pos),0)+1 FROM items WHERE list_id=?", (lid,)).fetchone()[0]
                    con.execute("INSERT INTO items(list_id,text,pos,created,added_by) VALUES(?,?,?,?,?)", (lid, text, pos, now, by))
            elif op == "item_edit":
                text = clean_items(body.get("text"))
                if not text:
                    raise ValueError("an item needs some text")
                con.execute("UPDATE items SET text=? WHERE id=?", (text[0], int(body["id"])))
            elif op == "item_done":
                iid = int(body["id"])
                if body.get("done"):
                    con.execute("UPDATE items SET done=1, done_at=?, done_by=? WHERE id=?", (now, by, iid))
                else:
                    lid = con.execute("SELECT list_id FROM items WHERE id=?", (iid,)).fetchone()
                    pos = con.execute("SELECT COALESCE(MAX(pos),0)+1 FROM items WHERE list_id=?", (lid[0] if lid else 0,)).fetchone()[0]
                    con.execute("UPDATE items SET done=0, done_at=NULL, done_by='', pos=? WHERE id=?", (pos, iid))
            elif op == "item_delete":
                con.execute("DELETE FROM items WHERE id=?", (int(body["id"]),))
            elif op == "clear_done":
                con.execute("DELETE FROM items WHERE list_id=? AND done=1", (int(body["list"]),))
            else:
                raise ValueError(f"unknown change {op!r}")
            con.execute("COMMIT")
        except Exception:
            if con.in_transaction:
                con.execute("ROLLBACK")
            raise
        finally:
            con.close()
    if op not in ("item_done",):
        log(f"app list: {op}" + (f" by {by}" if by else ""))
    return app_lists_payload()


# ---------------------------------------------------------------- quests: chores as an RPG
# Everyone in the family has a character: XP and levels that only go up, six D&D stats that grow with
# the kind of quests they do, and gold to spend in a reward shop the parents stock. Nothing is ever
# taken away for a missed quest. Daily quests count "days done this week" instead of a streak that
# resets. Quests that need a parent's OK wait in a queue; a parent's own phone (unlocked) skips it.
STATS = {"STR": "Fitness", "CON": "Healthy habits", "DEX": "Chores", "INT": "Reading and learning",
         "WIS": "Self-care", "CHA": "Kindness and helping"}
DIFFS = {"easy": (10, 2), "medium": (25, 5), "hard": (50, 10), "epic": (100, 20)}
GOAL_SIZES = {"small": (50, 10), "big": (150, 30), "huge": (300, 60), "legendary": (600, 120)}
FIT_KINDS = ["Walk", "Run", "Bike", "Swim", "Sports", "Strength", "Yoga", "Dance", "Play outside", "Other"]
FIT_XP_PER = 3          # 1 XP for every 3 active minutes (30 minutes = 10 XP, an easy quest)
FIT_DAY_CAP = 60        # most XP workouts can earn in a day
FIT_WEEK_BONUS = (50, 10)
FIT_DEFAULT_TARGET = 150
HABIT_KID = (5, 0)      # what a habit someone made for themselves earns until a parent changes it
HABIT_PARENT = (5, 1)
CLASSES = ["Adventurer", "Ranger", "Bard", "Paladin", "Wizard", "Rogue", "Cleric", "Druid", "Monk", "Barbarian", "Artificer"]
RPG_SCHEMA = """
CREATE TABLE IF NOT EXISTS chars(name TEXT PRIMARY KEY COLLATE NOCASE, cls TEXT NOT NULL DEFAULT '', created INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS quests(id INTEGER PRIMARY KEY, title TEXT NOT NULL, notes TEXT NOT NULL DEFAULT '',
  stat TEXT NOT NULL, diff TEXT NOT NULL, xp INTEGER NOT NULL, gold INTEGER NOT NULL,
  repeat TEXT NOT NULL, days INTEGER NOT NULL DEFAULT 127, who TEXT NOT NULL DEFAULT '',
  needs_ok INTEGER NOT NULL DEFAULT 1, active INTEGER NOT NULL DEFAULT 1, created INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS done(id INTEGER PRIMARY KEY, quest_id INTEGER, person TEXT NOT NULL COLLATE NOCASE,
  day TEXT NOT NULL, status TEXT NOT NULL, title TEXT NOT NULL, stat TEXT NOT NULL, xp INTEGER NOT NULL,
  gold INTEGER NOT NULL, at INTEGER NOT NULL, decided_by TEXT NOT NULL DEFAULT '', decided_at INTEGER, note TEXT NOT NULL DEFAULT '');
CREATE INDEX IF NOT EXISTS done_day ON done(day, quest_id);
CREATE INDEX IF NOT EXISTS done_person ON done(person, status);
CREATE TABLE IF NOT EXISTS rewards(id INTEGER PRIMARY KEY, title TEXT NOT NULL, cost INTEGER NOT NULL,
  who TEXT NOT NULL DEFAULT '', active INTEGER NOT NULL DEFAULT 1, created INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS redeems(id INTEGER PRIMARY KEY, reward_id INTEGER, person TEXT NOT NULL COLLATE NOCASE,
  title TEXT NOT NULL, cost INTEGER NOT NULL, status TEXT NOT NULL, at INTEGER NOT NULL,
  decided_by TEXT NOT NULL DEFAULT '', decided_at INTEGER);
CREATE TABLE IF NOT EXISTS goals(id INTEGER PRIMARY KEY, person TEXT NOT NULL COLLATE NOCASE, title TEXT NOT NULL,
  why TEXT NOT NULL DEFAULT '', target INTEGER NOT NULL DEFAULT 1, unit TEXT NOT NULL DEFAULT '', progress INTEGER NOT NULL DEFAULT 0,
  stat TEXT NOT NULL, size TEXT NOT NULL DEFAULT 'big', xp INTEGER NOT NULL DEFAULT 0, gold INTEGER NOT NULL DEFAULT 0, due TEXT NOT NULL DEFAULT '',
  status TEXT NOT NULL, proposed_by TEXT NOT NULL DEFAULT '', created INTEGER NOT NULL,
  decided_by TEXT NOT NULL DEFAULT '', decided_at INTEGER, done_at INTEGER, note TEXT NOT NULL DEFAULT '');
CREATE TABLE IF NOT EXISTS goal_log(id INTEGER PRIMARY KEY, goal_id INTEGER NOT NULL, person TEXT NOT NULL, delta INTEGER NOT NULL,
  note TEXT NOT NULL DEFAULT '', at INTEGER NOT NULL);
CREATE INDEX IF NOT EXISTS goal_log_goal ON goal_log(goal_id);
CREATE TABLE IF NOT EXISTS habits(id INTEGER PRIMARY KEY, person TEXT NOT NULL COLLATE NOCASE, title TEXT NOT NULL,
  stat TEXT NOT NULL, per_day INTEGER NOT NULL DEFAULT 1, week_aim INTEGER NOT NULL DEFAULT 7, xp INTEGER NOT NULL,
  gold INTEGER NOT NULL, active INTEGER NOT NULL DEFAULT 1, created INTEGER NOT NULL, created_by TEXT NOT NULL DEFAULT '');
CREATE TABLE IF NOT EXISTS habit_log(habit_id INTEGER NOT NULL, day TEXT NOT NULL, n INTEGER NOT NULL, done_id INTEGER,
  PRIMARY KEY(habit_id, day));
CREATE TABLE IF NOT EXISTS workouts(id INTEGER PRIMARY KEY, person TEXT NOT NULL COLLATE NOCASE, day TEXT NOT NULL,
  kind TEXT NOT NULL, minutes INTEGER NOT NULL, note TEXT NOT NULL DEFAULT '', done_id INTEGER, at INTEGER NOT NULL, by TEXT NOT NULL DEFAULT '');
CREATE INDEX IF NOT EXISTS workouts_day ON workouts(person, day);
CREATE TABLE IF NOT EXISTS fit_targets(name TEXT PRIMARY KEY COLLATE NOCASE, minutes INTEGER NOT NULL);
"""


def level_of(xp):
    """Level L starts at 50*L*(L-1) XP: 2 at 100, 3 at 300, 5 at 1,000, 10 at 4,500, 20 at 19,000."""
    lvl = int((1 + (1 + 0.08 * max(0, xp)) ** 0.5) / 2)
    return lvl, 50 * lvl * (lvl - 1), 50 * (lvl + 1) * lvl


def stat_score(xp):
    s = min(30, 10 + int((max(0, xp) / 25) ** 0.5))
    return {"score": s, "mod": (s - 10) // 2, "xp": xp}


def people_names():
    return [p["name"] for p in load_settings().get("people", [])]


def who_list(who):
    return [w for w in (x.strip() for x in str(who or "").split(",")) if w]


def scheduled(q, today):
    if not q["active"]:
        return False
    if q["repeat"] == "daily":
        return True
    if q["repeat"] == "days":
        return bool(q["days"] & (1 << today.weekday()))
    return True     # once: stays up until it's done


def rpg_payload():
    now = dt.datetime.now(LOCAL_TZ)
    today, day = now.date(), now.date().isoformat()
    monday = today - dt.timedelta(days=today.weekday())
    settings = load_settings()
    people = settings.get("people", [])
    with _db_lock:
        con = db()
        try:
            quests = [dict(r) for r in con.execute("SELECT * FROM quests ORDER BY active DESC, id")]
            classes = {r["name"].lower(): r["cls"] for r in con.execute("SELECT * FROM chars")}
            earned = {}
            for r in con.execute("SELECT person, stat, SUM(xp) xp, SUM(gold) gold FROM done WHERE status='approved' GROUP BY person, stat"):
                e = earned.setdefault(r["person"].lower(), {"xp": 0, "gold": 0, "stats": {}})
                e["xp"] += r["xp"]
                e["gold"] += r["gold"]
                e["stats"][r["stat"]] = e["stats"].get(r["stat"], 0) + r["xp"]
            spent = {r["p"]: r["c"] for r in con.execute(
                "SELECT lower(person) p, SUM(cost) c FROM redeems WHERE status IN ('approved','pending') GROUP BY lower(person)")}
            today_done = [dict(r) for r in con.execute("SELECT * FROM done WHERE day=? AND status!='rejected' AND quest_id IS NOT NULL", (day,))]
            once_done = [dict(r) for r in con.execute(
                "SELECT d.* FROM done d JOIN quests q ON q.id=d.quest_id WHERE q.repeat='once' AND d.status!='rejected'")]
            week = {}
            for r in con.execute("SELECT quest_id, lower(person) p, COUNT(DISTINCT day) n FROM done WHERE day>=? AND status!='rejected' GROUP BY quest_id, lower(person)",
                                 (monday.isoformat(),)):
                week[(r["quest_id"], r["p"])] = r["n"]
            pending = [dict(r) for r in con.execute("SELECT * FROM done WHERE status='pending' ORDER BY at")]
            rewards = [dict(r) for r in con.execute("SELECT * FROM rewards ORDER BY active DESC, cost, id")]
            redeems = [dict(r) for r in con.execute("SELECT * FROM redeems ORDER BY at DESC LIMIT 200")]
            log_rows = [dict(r) for r in con.execute("SELECT * FROM done ORDER BY at DESC LIMIT 300")]
            goals = [dict(r) for r in con.execute(
                "SELECT * FROM goals WHERE status IN ('proposed','active','claimed') OR (status IN ('done','declined') AND COALESCE(done_at, decided_at, created) > ?) "
                "ORDER BY CASE status WHEN 'claimed' THEN 0 WHEN 'proposed' THEN 1 WHEN 'active' THEN 2 ELSE 3 END, COALESCE(due,'') = '', due, id",
                (int(time.time()) - 90 * 86400,))]
            glog = {}
            for r in con.execute("SELECT * FROM goal_log WHERE goal_id IN (SELECT id FROM goals WHERE status IN ('active','claimed')) ORDER BY at DESC"):
                if len(glog.setdefault(r["goal_id"], [])) < 5:
                    glog[r["goal_id"]].append(dict(r))
            goals_done = {r["p"]: r["n"] for r in con.execute("SELECT lower(person) p, COUNT(*) n FROM goals WHERE status='done' GROUP BY lower(person)")}
            habits = [dict(r) for r in con.execute("SELECT * FROM habits ORDER BY active DESC, id")]
            hlog = {}
            for r in con.execute("SELECT * FROM habit_log WHERE day>=?", (monday.isoformat(),)):
                hlog[(r["habit_id"], r["day"])] = r["n"]
            wk = [dict(r) for r in con.execute("SELECT * FROM workouts WHERE day>=? ORDER BY at DESC", (monday.isoformat(),))]
            recent_wk = [dict(r) for r in con.execute("SELECT * FROM workouts ORDER BY at DESC LIMIT 60")]
            targets = {r["name"].lower(): r["minutes"] for r in con.execute("SELECT * FROM fit_targets")}
            bonus_wk = {r["p"] for r in con.execute("SELECT DISTINCT lower(person) p FROM done WHERE note='fitweek' AND day>=?", (monday.isoformat(),))}
        finally:
            con.close()
    days_so_far = today.weekday() + 1
    goals_on = settings.get("goals_on", True)
    for g in goals:
        g["pct"] = min(100, round(100 * g["progress"] / max(1, g["target"])))
        g["recent"] = glog.get(g["id"], [])
    habits_on, fitness_on = settings.get("habits_on", True), settings.get("fitness_on", True)
    week_days = [(monday + dt.timedelta(days=i)).isoformat() for i in range(7)]
    for h in habits:
        h["today"] = hlog.get((h["id"], day), 0)
        h["week"] = [hlog.get((h["id"], d), 0) >= h["per_day"] for d in week_days]
        h["week_done"] = sum(h["week"])
    fitness = {}
    for p in people:
        k = p["name"].lower()
        mine = [w for w in wk if w["person"].lower() == k]
        fitness[p["name"]] = {"target": targets.get(k, FIT_DEFAULT_TARGET), "week": sum(w["minutes"] for w in mine),
                              "today": sum(w["minutes"] for w in mine if w["day"] == day),
                              "by_day": [sum(w["minutes"] for w in mine if w["day"] == d) for d in week_days],
                              "bonus": k in bonus_wk,
                              "recent": [w for w in recent_wk if w["person"].lower() == k][:10]}

    def state_for(q, person):
        pool = once_done if q["repeat"] == "once" else today_done
        mine = [d for d in pool if d["quest_id"] == q["id"] and d["person"].lower() == person.lower()]
        if mine:
            return {"state": mine[0]["status"], "done_id": mine[0]["id"]}
        if not who_list(q["who"]):    # bounty: first one to finish it takes it
            other = [d for d in pool if d["quest_id"] == q["id"]]
            if other:
                return {"state": "taken", "by": other[0]["person"]}
        return {"state": "todo"}

    chars, todo = [], {}
    for p in people:
        n = p["name"]
        e = earned.get(n.lower(), {"xp": 0, "gold": 0, "stats": {}})
        lvl, floor, nxt = level_of(e["xp"])
        mine = []
        for q in quests:
            if not scheduled(q, today):
                continue
            who = who_list(q["who"])
            if who and n.lower() not in (w.lower() for w in who):
                continue
            st = state_for(q, n)
            if not who and st["state"] == "taken":
                continue
            item = {k: q[k] for k in ("id", "title", "notes", "stat", "xp", "gold", "needs_ok", "repeat")}
            item.update(st, bounty=not who)
            if q["repeat"] == "daily":
                item["week"] = f"{week.get((q['id'], n.lower()), 0)} of {days_so_far} days this week"
            mine.append(item)
        todo[n] = mine
        chars.append({"name": n, "color": p["color"], "cls": classes.get(n.lower()) or "Adventurer",
                      "xp": e["xp"], "level": lvl, "lvl_floor": floor, "lvl_next": nxt,
                      "gold": e["gold"] - spent.get(n.lower(), 0),
                      "stats": {k: stat_score(e["stats"].get(k, 0)) for k in STATS},
                      "left": sum(1 for i in mine if i["state"] == "todo" and not i["bounty"]),
                      "done_today": sum(1 for i in mine if i["state"] in ("approved", "pending")),
                      "goals_done": goals_done.get(n.lower(), 0), "photo": avatar_version(n)})
    bounty = [dict({k: q[k] for k in ("id", "title", "notes", "stat", "xp", "gold", "needs_ok", "repeat")},
                   **state_for(q, "\x00"), bounty=True)
              for q in quests if scheduled(q, today) and not who_list(q["who"])]
    return {"now": int(time.time()), "today": day, "stats": STATS, "diffs": DIFFS, "classes": CLASSES,
            "chars": chars, "todo": todo, "bounty": bounty, "pending": pending, "quests": quests,
            "rewards": rewards, "redeems": redeems, "log": log_rows, "on": settings.get("rpg_on", True),
            "goals_on": goals_on, "goals": goals if goals_on else [], "goal_sizes": GOAL_SIZES,
            "habits_on": habits_on, "habits": habits if habits_on else [],
            "fitness_on": fitness_on, "fitness": fitness if fitness_on else {}, "fit_kinds": FIT_KINDS,
            "fit_rules": {"xp_per": FIT_XP_PER, "day_cap": FIT_DAY_CAP, "bonus": FIT_WEEK_BONUS}, "photos": avatar_versions()}


def party_for_kiosk():
    """The kitchen screen's Party panel: just levels, XP bars and what's left today."""
    if not load_settings().get("rpg_on", True):
        return {"on": False, "members": []}
    p = rpg_payload()
    last = {}
    for g in sorted((g for g in p["goals"] if g["status"] == "done"), key=lambda g: g["done_at"] or 0):
        last[g["person"].lower()] = g["title"]
    return {"on": True, "quests": any(q["active"] for q in p["quests"]), "members": [{"name": c["name"], "color": c["color"], "cls": c["cls"], "level": c["level"],
             "pct": round(100 * (c["xp"] - c["lvl_floor"]) / max(1, c["lvl_next"] - c["lvl_floor"])),
             "left": c["left"], "done": c["done_today"], "gold": c["gold"],
             "goals": c["goals_done"], "goal": last.get(c["name"].lower(), ""), "photo": c["photo"]} for c in p["chars"]]}


def person_of(v):
    name = who_name(v)
    for n in people_names():
        if n.lower() == name.lower():
            return n
    raise ValueError("pick who you are at the top of the app first")


def rpg_change(body, parent):
    op = str(body.get("op", ""))
    now = int(time.time())
    day = dt.datetime.now(LOCAL_TZ).date().isoformat()
    by = who_name(body.get("by"))

    def need_parent():
        if not parent:
            raise PermissionError("that needs the parent PIN")

    with _db_lock:
        con = db()
        try:
            con.execute("BEGIN IMMEDIATE")
            if op == "quest_done":
                person = person_of(body.get("person") or by)
                if person.lower() != by.lower() and not parent:
                    raise PermissionError("you can only finish your own quests")
                q = con.execute("SELECT * FROM quests WHERE id=? AND active=1", (int(body["id"]),)).fetchone()
                if not q:
                    raise ValueError("that quest is gone; pull down to refresh")
                if not scheduled(q, dt.datetime.now(LOCAL_TZ).date()):
                    raise ValueError("that quest isn't on for today")
                who = who_list(q["who"])
                if who and person.lower() not in (w.lower() for w in who):
                    raise ValueError("that quest belongs to someone else")
                where = "" if q["repeat"] == "once" else " AND day=?"
                args = (q["id"],) if q["repeat"] == "once" else (q["id"], day)
                taken = con.execute(f"SELECT person FROM done WHERE quest_id=? AND status!='rejected'{where}"
                                    + ("" if not who else " AND person=?"), args + ((person,) if who else ())).fetchone()
                if taken:
                    raise ValueError(f"{taken['person']} already finished that one" if not who else "already done")
                status = "pending" if q["needs_ok"] and not parent else "approved"
                con.execute("INSERT INTO done(quest_id,person,day,status,title,stat,xp,gold,at,decided_by,decided_at) VALUES(?,?,?,?,?,?,?,?,?,?,?)",
                            (q["id"], person, day, status, q["title"], q["stat"], q["xp"], q["gold"], now,
                             by if status == "approved" and q["needs_ok"] else "", now if status == "approved" else None))
                msg = f"{person} finished {q['title']!r} ({status})"
            elif op == "quest_undo":
                d = con.execute("SELECT * FROM done WHERE id=?", (int(body["id"]),)).fetchone()
                if not d:
                    raise ValueError("already undone")
                if not parent and not (d["person"].lower() == by.lower() and d["day"] == day):
                    raise PermissionError("only a parent can undo that")
                con.execute("DELETE FROM done WHERE id=?", (d["id"],))
                msg = f"undid {d['title']!r} for {d['person']}"
            elif op in ("approve", "reject"):
                need_parent()
                ids = [int(i) for i in (body.get("ids") or [body.get("id")])]
                con.executemany("UPDATE done SET status=?, decided_by=?, decided_at=? WHERE id=? AND status='pending'",
                                [("approved" if op == "approve" else "rejected", by, now, i) for i in ids])
                msg = f"{op}d {len(ids)}"
            elif op == "bonus":
                need_parent()
                person = person_of(body.get("person"))
                xp, gold = max(0, min(1000, int(body.get("xp") or 0))), max(0, min(1000, int(body.get("gold") or 0)))
                stat = body.get("stat") if body.get("stat") in STATS else "CHA"
                note = re.sub(r"\s+", " ", str(body.get("note") or "")).strip()[:80] or "Bonus"
                if not (xp or gold):
                    raise ValueError("give some XP or gold")
                con.execute("INSERT INTO done(quest_id,person,day,status,title,stat,xp,gold,at,decided_by,decided_at,note) VALUES(NULL,?,?,'approved',?,?,?,?,?,?,?,'bonus')",
                            (person, day, note, stat, xp, gold, now, by, now))
                msg = f"bonus for {person}: {xp} XP, {gold} gold"
            elif op == "quest_save":
                need_parent()
                title = re.sub(r"\s+", " ", str(body.get("title") or "")).strip()[:80]
                if not title:
                    raise ValueError("give the quest a name")
                stat = body.get("stat") if body.get("stat") in STATS else "DEX"
                diff = body.get("diff") if body.get("diff") in DIFFS else "easy"
                xp = max(0, min(1000, int(body.get("xp") if body.get("xp") not in (None, "") else DIFFS[diff][0])))
                gold = max(0, min(1000, int(body.get("gold") if body.get("gold") not in (None, "") else DIFFS[diff][1])))
                repeat = body.get("repeat") if body.get("repeat") in ("daily", "days", "once") else "daily"
                days = int(body.get("days") or 0) & 127
                if repeat == "days" and not days:
                    raise ValueError("pick at least one day")
                names = {n.lower(): n for n in people_names()}
                who = ",".join(names[w.lower()] for w in who_list(body.get("who")) if w.lower() in names)
                vals = (title, str(body.get("notes") or "").strip()[:300], stat, diff, xp, gold, repeat, days or 127, who,
                        1 if body.get("needs_ok", True) else 0, 1 if body.get("active", True) else 0)
                if body.get("id"):
                    con.execute("UPDATE quests SET title=?,notes=?,stat=?,diff=?,xp=?,gold=?,repeat=?,days=?,who=?,needs_ok=?,active=? WHERE id=?",
                                vals + (int(body["id"]),))
                else:
                    if con.execute("SELECT COUNT(*) FROM quests").fetchone()[0] >= 300:
                        raise ValueError("that's a lot of quests; delete some old ones first")
                    con.execute("INSERT INTO quests(title,notes,stat,diff,xp,gold,repeat,days,who,needs_ok,active,created) VALUES(?,?,?,?,?,?,?,?,?,?,?,?)",
                                vals + (now,))
                msg = f"quest saved: {title!r}"
            elif op == "quest_delete":
                need_parent()
                con.execute("DELETE FROM quests WHERE id=?", (int(body["id"]),))   # finished ones stay in the log
                msg = "quest deleted"
            elif op == "reward_save":
                need_parent()
                title = re.sub(r"\s+", " ", str(body.get("title") or "")).strip()[:80]
                if not title:
                    raise ValueError("give the reward a name")
                cost = max(1, min(100000, int(body.get("cost") or 0)))
                names = {n.lower(): n for n in people_names()}
                who = ",".join(names[w.lower()] for w in who_list(body.get("who")) if w.lower() in names)
                if body.get("id"):
                    con.execute("UPDATE rewards SET title=?, cost=?, who=?, active=? WHERE id=?",
                                (title, cost, who, 1 if body.get("active", True) else 0, int(body["id"])))
                else:
                    con.execute("INSERT INTO rewards(title,cost,who,active,created) VALUES(?,?,?,1,?)", (title, cost, who, now))
                msg = f"reward saved: {title!r}"
            elif op == "reward_delete":
                need_parent()
                con.execute("DELETE FROM rewards WHERE id=?", (int(body["id"]),))
                msg = "reward deleted"
            elif op == "redeem":
                person = person_of(body.get("person") or by)
                if person.lower() != by.lower() and not parent:
                    raise PermissionError("you can only spend your own gold")
                r = con.execute("SELECT * FROM rewards WHERE id=? AND active=1", (int(body["id"]),)).fetchone()
                if not r:
                    raise ValueError("that reward is gone; pull down to refresh")
                if who_list(r["who"]) and person.lower() not in (w.lower() for w in who_list(r["who"])):
                    raise ValueError("that reward is for someone else")
                gold = (con.execute("SELECT COALESCE(SUM(gold),0) FROM done WHERE status='approved' AND person=?", (person,)).fetchone()[0]
                        - con.execute("SELECT COALESCE(SUM(cost),0) FROM redeems WHERE status IN ('approved','pending') AND person=?", (person,)).fetchone()[0])
                if gold < r["cost"]:
                    raise ValueError(f"that costs {r['cost']} gold; {person} has {gold}")
                status = "approved" if parent else "pending"
                con.execute("INSERT INTO redeems(reward_id,person,title,cost,status,at,decided_by,decided_at) VALUES(?,?,?,?,?,?,?,?)",
                            (r["id"], person, r["title"], r["cost"], status, now, by if parent else "", now if parent else None))
                msg = f"{person} redeemed {r['title']!r} ({status})"
            elif op in ("redeem_ok", "redeem_no"):
                need_parent()
                con.execute("UPDATE redeems SET status=?, decided_by=?, decided_at=? WHERE id=? AND status='pending'",
                            ("approved" if op == "redeem_ok" else "denied", by, now, int(body["id"])))
                msg = op
            elif op.startswith("goal_"):
                msg = goal_change(con, op, body, parent, by, now, day)
            elif op.startswith("habit_"):
                msg = habit_change(con, op, body, parent, by, now, day)
            elif op.startswith("fit_"):
                msg = fit_change(con, op, body, parent, by, now, day)
            elif op == "char_save":
                person = person_of(body.get("person") or by)
                if person.lower() != by.lower() and not parent:
                    raise PermissionError("you can only change your own character")
                cls = re.sub(r"\s+", " ", str(body.get("cls") or "")).strip()[:24]
                con.execute("INSERT INTO chars(name,cls,created) VALUES(?,?,?) ON CONFLICT(name) DO UPDATE SET cls=excluded.cls", (person, cls, now))
                msg = f"{person} is now a {cls}"
            else:
                raise ValueError(f"unknown change {op!r}")
            con.execute("COMMIT")
        except Exception:
            if con.in_transaction:
                con.execute("ROLLBACK")
            raise
        finally:
            con.close()
    log(f"quests: {msg}")
    return rpg_payload()


def goal_finish(con, g, by, now, day):
    """A finished goal lands in the same ledger as quests, so its XP and gold count everywhere."""
    con.execute("UPDATE goals SET status='done', progress=target, done_at=?, decided_by=?, decided_at=? WHERE id=?", (now, by, now, g["id"]))
    con.execute("INSERT INTO done(quest_id,person,day,status,title,stat,xp,gold,at,decided_by,decided_at,note) VALUES(NULL,?,?,'approved',?,?,?,?,?,?,?,'goal')",
                (g["person"], day, g["title"], g["stat"], g["xp"], g["gold"], now, by, now))


def goal_change(con, op, body, parent, by, now, day):
    """Goals: long quests with a progress bar. Kids propose their own, parents set the reward and approve.
    Progress only adds up; a goal that stalls just waits. Nothing is ever lost."""
    if not load_settings().get("goals_on", True):
        raise ValueError("goals are turned off in the app's Manage page")

    def need_parent():
        if not parent:
            raise PermissionError("that needs the parent PIN")

    def goal():
        g = con.execute("SELECT * FROM goals WHERE id=?", (int(body.get("id") or 0),)).fetchone()
        if not g:
            raise ValueError("that goal is gone; pull down to refresh")
        return g

    def fields():
        title = re.sub(r"\s+", " ", str(body.get("title") or "")).strip()[:80]
        if not title:
            raise ValueError("give the goal a name")
        target = max(1, min(100000, int(body.get("target") or 1)))
        unit = re.sub(r"\s+", " ", str(body.get("unit") or "")).strip()[:20]
        due = str(body.get("due") or "")
        if due and not re.fullmatch(r"\d{4}-\d{2}-\d{2}", due):
            raise ValueError("bad date")
        return (title, re.sub(r"\s+", " ", str(body.get("why") or "")).strip()[:200], target, unit,
                body.get("stat") if body.get("stat") in STATS else "INT", due)

    def reward():
        size = body.get("size") if body.get("size") in GOAL_SIZES else "big"
        xp = max(0, min(5000, int(body.get("xp") if body.get("xp") not in (None, "") else GOAL_SIZES[size][0])))
        gold = max(0, min(5000, int(body.get("gold") if body.get("gold") not in (None, "") else GOAL_SIZES[size][1])))
        return size, xp, gold

    if op == "goal_propose":
        person = person_of(body.get("person") or by)
        if person.lower() != by.lower() and not parent:
            raise PermissionError("you can only propose your own goals")
        if con.execute("SELECT COUNT(*) FROM goals WHERE person=? AND status IN ('proposed','active','claimed')", (person,)).fetchone()[0] >= 20:
            raise ValueError("that's a lot of goals at once; finish a few first")
        title, why, target, unit, stat, due = fields()
        size, xp, gold = reward() if parent else ("big", 0, 0)
        status = "active" if parent else "proposed"
        con.execute("INSERT INTO goals(person,title,why,target,unit,stat,size,xp,gold,due,status,proposed_by,created,decided_by,decided_at) "
                    "VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                    (person, title, why, target, unit, stat, size, xp, gold, due, status, by, now, by if parent else "", now if parent else None))
        return f"goal for {person}: {title!r} ({status})"
    if op == "goal_save":       # parents: edit any goal, and approving a proposal is saving it with a reward
        need_parent()
        g = goal()
        title, why, target, unit, stat, due = fields()
        size, xp, gold = reward()
        status = "active" if g["status"] in ("proposed", "declined") else g["status"]
        con.execute("UPDATE goals SET title=?,why=?,target=?,unit=?,stat=?,due=?,size=?,xp=?,gold=?,status=?,progress=MIN(progress,?),"
                    "decided_by=CASE WHEN status='proposed' THEN ? ELSE decided_by END, decided_at=CASE WHEN status='proposed' THEN ? ELSE decided_at END WHERE id=?",
                    (title, why, target, unit, stat, due, size, xp, gold, status, target, by, now, g["id"]))
        return f"goal saved: {title!r}"
    if op == "goal_decline":
        g = goal()
        if not parent and not (g["status"] == "proposed" and g["person"].lower() == by.lower()):
            raise PermissionError("that needs the parent PIN")
        if g["status"] == "proposed" and not parent:      # kids can take back their own idea
            con.execute("DELETE FROM goals WHERE id=?", (g["id"],))
            return "proposal withdrawn"
        con.execute("UPDATE goals SET status='declined', note=?, decided_by=?, decided_at=? WHERE id=?",
                    (re.sub(r"\s+", " ", str(body.get("note") or "")).strip()[:120], by, now, g["id"]))
        return f"goal set aside: {g['title']!r}"
    if op == "goal_progress":
        g = goal()
        if g["person"].lower() != by.lower() and not parent:
            raise PermissionError("you can only log your own goals")
        if g["status"] != "active":
            raise ValueError("that goal isn't active")
        delta = int(body.get("delta") or 0)
        new = max(0, min(g["target"], g["progress"] + delta))
        if new == g["progress"]:
            raise ValueError("no change")
        con.execute("UPDATE goals SET progress=? WHERE id=?", (new, g["id"]))
        con.execute("INSERT INTO goal_log(goal_id,person,delta,note,at) VALUES(?,?,?,?,?)",
                    (g["id"], by or g["person"], new - g["progress"], re.sub(r"\s+", " ", str(body.get("note") or "")).strip()[:80], now))
        if new >= g["target"]:
            if parent:
                goal_finish(con, dict(g), by, now, day)
                return f"{g['person']} finished goal {g['title']!r}"
            con.execute("UPDATE goals SET status='claimed' WHERE id=?", (g["id"],))
            return f"{g['person']} reached goal {g['title']!r}; waiting for a parent"
        return f"goal progress {g['title']!r}: {new}/{g['target']}"
    if op == "goal_ok":
        need_parent()
        g = goal()
        if g["status"] not in ("claimed", "active"):
            raise ValueError("that goal is already settled")
        goal_finish(con, dict(g), by, now, day)
        return f"goal done: {g['title']!r}"
    if op == "goal_notyet":     # back to active, a step short of the target, with no other change
        need_parent()
        g = goal()
        if g["status"] != "claimed":
            raise ValueError("that goal isn't waiting")
        con.execute("UPDATE goals SET status='active', progress=MAX(0, target-1) WHERE id=?", (g["id"],))
        return f"goal not yet: {g['title']!r}"
    if op == "goal_delete":
        need_parent()
        g = goal()
        con.execute("DELETE FROM goals WHERE id=?", (g["id"],))
        con.execute("DELETE FROM goal_log WHERE goal_id=?", (g["id"],))
        return f"goal deleted: {g['title']!r}"   # a finished goal's XP stays in the log
    raise ValueError(f"unknown change {op!r}")


def habit_change(con, op, body, parent, by, now, day):
    """Habits: small things done every day (or a few times a day), tapped off on the phone. No approval,
    no streaks: the week shows which days happened, and a missed day costs nothing."""
    if not load_settings().get("habits_on", True):
        raise ValueError("habits are turned off in the app's Manage page")

    def habit():
        h = con.execute("SELECT * FROM habits WHERE id=?", (int(body.get("id") or 0),)).fetchone()
        if not h:
            raise ValueError("that habit is gone; pull down to refresh")
        if h["person"].lower() != by.lower() and not parent:
            raise PermissionError("that's someone else's habit")
        return h

    if op == "habit_save":
        h = habit() if body.get("id") else None
        person = h["person"] if h else person_of(body.get("person") or by)
        if person.lower() != by.lower() and not parent:
            raise PermissionError("you can only make your own habits")
        title = re.sub(r"\s+", " ", str(body.get("title") or "")).strip()[:60]
        if not title:
            raise ValueError("give the habit a name")
        stat = body.get("stat") if body.get("stat") in STATS else "CON"
        per_day = max(1, min(20, int(body.get("per_day") or 1)))
        week_aim = max(1, min(7, int(body.get("week_aim") or 7)))
        if parent:
            dx, dg = HABIT_PARENT
            xp = max(0, min(100, int(body.get("xp") if body.get("xp") not in (None, "") else (h["xp"] if h else dx))))
            gold = max(0, min(20, int(body.get("gold") if body.get("gold") not in (None, "") else (h["gold"] if h else dg))))
        else:
            xp, gold = (h["xp"], h["gold"]) if h else HABIT_KID
        active = 1 if body.get("active", True) else 0
        if h:
            con.execute("UPDATE habits SET title=?,stat=?,per_day=?,week_aim=?,xp=?,gold=?,active=? WHERE id=?",
                        (title, stat, per_day, week_aim, xp, gold, active, h["id"]))
        else:
            if con.execute("SELECT COUNT(*) FROM habits WHERE person=? AND active=1", (person,)).fetchone()[0] >= 10:
                raise ValueError("10 habits is plenty; pause one first")
            con.execute("INSERT INTO habits(person,title,stat,per_day,week_aim,xp,gold,active,created,created_by) VALUES(?,?,?,?,?,?,?,?,?,?)",
                        (person, title, stat, per_day, week_aim, xp, gold, active, now, by))
        return f"habit saved for {person}: {title!r}"
    if op == "habit_delete":
        h = habit()
        con.execute("DELETE FROM habits WHERE id=?", (h["id"],))
        con.execute("DELETE FROM habit_log WHERE habit_id=?", (h["id"],))    # XP already earned stays
        return f"habit deleted: {h['title']!r}"
    if op == "habit_tick":
        h = habit()
        if not h["active"]:
            raise ValueError("that habit is paused")
        row = con.execute("SELECT * FROM habit_log WHERE habit_id=? AND day=?", (h["id"], day)).fetchone()
        n0 = row["n"] if row else 0
        n = max(0, min(h["per_day"], n0 + (1 if int(body.get("delta") or 1) > 0 else -1)))
        if n == n0:
            raise ValueError("already done for today" if n0 else "nothing to undo")
        done_id = row["done_id"] if row else None
        if n >= h["per_day"] and not done_id:
            cur = con.execute("INSERT INTO done(quest_id,person,day,status,title,stat,xp,gold,at,decided_by,decided_at,note) VALUES(NULL,?,?,'approved',?,?,?,?,?,'',?,'habit')",
                              (h["person"], day, h["title"], h["stat"], h["xp"], h["gold"], now, now))
            done_id = cur.lastrowid
        elif n < h["per_day"] and done_id:
            con.execute("DELETE FROM done WHERE id=?", (done_id,))
            done_id = None
        con.execute("INSERT INTO habit_log(habit_id,day,n,done_id) VALUES(?,?,?,?) ON CONFLICT(habit_id,day) DO UPDATE SET n=excluded.n, done_id=excluded.done_id",
                    (h["id"], day, n, done_id))
        return f"habit {h['title']!r} for {h['person']}: {n}/{h['per_day']}"
    raise ValueError(f"unknown change {op!r}")


def fit_week_bonus(con, person, day, now, take_back=True):
    """Reaching the weekly active-minutes target pays a one-time bonus; an undo that drops below takes it back."""
    d = dt.date.fromisoformat(day)
    monday = (d - dt.timedelta(days=d.weekday())).isoformat()
    mins = con.execute("SELECT COALESCE(SUM(minutes),0) FROM workouts WHERE person=? AND day>=?", (person, monday)).fetchone()[0]
    t = con.execute("SELECT minutes FROM fit_targets WHERE name=?", (person,)).fetchone()
    target = t["minutes"] if t else FIT_DEFAULT_TARGET
    have = con.execute("SELECT id FROM done WHERE person=? AND note='fitweek' AND day>=?", (person, monday)).fetchone()
    if mins >= target and not have:
        con.execute("INSERT INTO done(quest_id,person,day,status,title,stat,xp,gold,at,decided_by,decided_at,note) VALUES(NULL,?,?,'approved',?,'STR',?,?,?,'',?,'fitweek')",
                    (person, day, f"Weekly activity goal: {target} minutes", FIT_WEEK_BONUS[0], FIT_WEEK_BONUS[1], now, now))
    elif mins < target and have and take_back:     # only an undo takes it back, never a new target
        con.execute("DELETE FROM done WHERE id=?", (have["id"],))


def fit_change(con, op, body, parent, by, now, day):
    """Fitness: log active minutes. Each workout earns STR XP (capped per day), and hitting the
    week's target earns a bonus. Honor system, like the lists; parents can remove any entry."""
    if not load_settings().get("fitness_on", True):
        raise ValueError("fitness is turned off in the app's Manage page")
    if op == "fit_log":
        person = person_of(body.get("person") or by)
        if person.lower() != by.lower() and not parent:
            raise PermissionError("you can only log your own activity")
        kind = body.get("kind") if body.get("kind") in FIT_KINDS else "Other"
        minutes = int(body.get("minutes") or 0)
        if not 1 <= minutes <= 600:
            raise ValueError("minutes should be between 1 and 600")
        note = re.sub(r"\s+", " ", str(body.get("note") or "")).strip()[:60]
        when = str(body.get("day") or day)
        if when != day:      # yesterday is allowed, for the evening someone forgot
            y = (dt.date.fromisoformat(day) - dt.timedelta(days=1)).isoformat()
            if when != y:
                raise ValueError("you can log today or yesterday")
        earned = con.execute("SELECT COALESCE(SUM(d.xp),0) FROM workouts w JOIN done d ON d.id=w.done_id WHERE w.person=? AND w.day=?",
                             (person, when)).fetchone()[0]
        xp = max(0, min(minutes // FIT_XP_PER, FIT_DAY_CAP - earned))
        title = f"{kind} {minutes} min" + (f" ({note})" if note else "")
        done_id = None
        if xp:
            done_id = con.execute("INSERT INTO done(quest_id,person,day,status,title,stat,xp,gold,at,decided_by,decided_at,note) VALUES(NULL,?,?,'approved',?,'STR',?,0,?,'',?,'workout')",
                                  (person, when, title, xp, now, now)).lastrowid
        con.execute("INSERT INTO workouts(person,day,kind,minutes,note,done_id,at,by) VALUES(?,?,?,?,?,?,?,?)",
                    (person, when, kind, minutes, note, done_id, now, by))
        fit_week_bonus(con, person, when, now)
        return f"{person} logged {title}"
    if op == "fit_undo":
        w = con.execute("SELECT * FROM workouts WHERE id=?", (int(body.get("id") or 0),)).fetchone()
        if not w:
            raise ValueError("already removed")
        if not parent and not (w["person"].lower() == by.lower() and w["at"] > now - 2 * 86400):
            raise PermissionError("only a parent can remove that one")
        con.execute("DELETE FROM workouts WHERE id=?", (w["id"],))
        if w["done_id"]:
            con.execute("DELETE FROM done WHERE id=?", (w["done_id"],))
        fit_week_bonus(con, w["person"], w["day"], now)
        return f"removed {w['kind']} {w['minutes']} min for {w['person']}"
    if op == "fit_target":
        if not parent:
            raise PermissionError("that needs the parent PIN")
        person = person_of(body.get("person"))
        minutes = max(10, min(2000, int(body.get("minutes") or FIT_DEFAULT_TARGET)))
        con.execute("INSERT INTO fit_targets(name,minutes) VALUES(?,?) ON CONFLICT(name) DO UPDATE SET minutes=excluded.minutes", (person, minutes))
        fit_week_bonus(con, person, day, now, take_back=False)
        return f"weekly activity target for {person}: {minutes}"
    raise ValueError(f"unknown change {op!r}")


# ---------------------------------------------------------------- profile pictures
# The phone crops and shrinks the picture to a small square JPEG before sending it, so the server only
# checks it is a JPEG and keeps it. Files are named by a hash of the name, so any name is a safe file name.
def avatar_path(name):
    return AVATAR_DIR / (hashlib.sha256(name.strip().lower().encode()).hexdigest()[:16] + ".jpg")


def avatar_version(name):
    try:
        return int(avatar_path(name).stat().st_mtime)
    except OSError:
        return 0


def avatar_versions():
    return {n: v for n in people_names() if (v := avatar_version(n))}


def avatar_save(person, data):
    if not data:
        avatar_path(person).unlink(missing_ok=True)
        return
    if not data.startswith(b"\xff\xd8\xff") or len(data) > AVATAR_MAX:
        raise ValueError("that picture didn't come through as a small JPEG; try another")
    AVATAR_DIR.mkdir(parents=True, exist_ok=True)
    tmp = avatar_path(person).with_suffix(".tmp")
    tmp.write_bytes(data)
    tmp.replace(avatar_path(person))


# ---------------------------------------------------------------- the Remote: phones put a detail page on the kitchen screen
# The kiosk has no mouse or touch, so a phone picks what it shows: a character sheet, the weather in detail,
# a month of the calendar or one day. The kiosk asks every 3 seconds (a few bytes) and goes back to the
# dashboard on its own when the time runs out or someone taps Back.
SCREEN_PAGES = ("sheet", "weather", "month", "day")
_screen = {"page": "", "arg": "", "until": 0, "seq": 0, "by": ""}


def screen_state():
    if _screen["page"] and _screen["until"] < time.time():
        _screen.update(page="", arg="", until=0, seq=_screen["seq"] + 1, by="")
    return dict(_screen, now=int(time.time()))


def screen_set(body):
    page = str(body.get("page") or "")
    if page and page not in SCREEN_PAGES:
        raise ValueError("unknown page")
    arg = str(body.get("arg") or "")[:40]
    if page in ("month", "day") and arg and not re.fullmatch(r"\d{4}-\d{2}(-\d{2})?", arg):
        raise ValueError("bad date")
    secs = max(15, min(1800, int(body.get("secs") or 120)))
    _screen.update(page=page, arg=arg if page else "", until=int(time.time()) + secs if page else 0,
                   seq=_screen["seq"] + 1, by=who_name(body.get("by")) if page else "")
    return screen_state()


# ---------------------------------------------------------------- parent PIN
# No PIN set: everything is open to the home network, as before. Once a PIN is set, settings, deleting
# lists and clearing all messages need it. Unlocking gives the phone a long-lived sign-in token
# (header X-Parent), stored hashed in family.db, so a parent types the PIN once per phone.
SESSION_DAYS = 180
_pin_fails = []
_pin_lock = threading.Lock()


def pin_hash(pin, salt):
    return hashlib.pbkdf2_hmac("sha256", pin.encode(), bytes.fromhex(salt), 200_000).hex()


def pin_set():
    return bool(load_private().get("pin", {}).get("hash"))


def check_pin(pin):
    p = load_private().get("pin", {})
    return bool(p.get("hash")) and hmac.compare_digest(pin_hash(str(pin), p["salt"]), p["hash"])


def token_ok(token):
    if not token:
        return False
    h, now = hashlib.sha256(token.encode()).hexdigest(), int(time.time())
    with _db_lock:
        con = db()
        try:
            row = con.execute("SELECT seen FROM sessions WHERE hash=?", (h,)).fetchone()
            if not row or row["seen"] < now - SESSION_DAYS * 86400:
                return False
            if row["seen"] < now - 3600:
                con.execute("UPDATE sessions SET seen=? WHERE hash=?", (now, h))
            return True
        finally:
            con.close()


def new_session(drop_others_than=None):
    token, now = secrets.token_urlsafe(24), int(time.time())
    with _db_lock:
        con = db()
        try:
            if drop_others_than is not None:
                con.execute("DELETE FROM sessions")
            con.execute("INSERT INTO sessions(hash,created,seen) VALUES(?,?,?)", (hashlib.sha256(token.encode()).hexdigest(), now, now))
        finally:
            con.close()
    return token


def drop_session(token):
    with _db_lock:
        con = db()
        try:
            con.execute("DELETE FROM sessions WHERE hash=?", (hashlib.sha256(str(token).encode()).hexdigest(),))
        finally:
            con.close()


def auth_change(body, token):
    """{"pin": "1234"} unlocks; {"new_pin": "...", "pin": "old"} sets or changes it ("" removes it);
    {"lock": true} signs this phone out."""
    if body.get("lock"):
        drop_session(token)
        return {"ok": True, "pin_set": pin_set(), "parent": not pin_set()}
    with _pin_lock:
        now = time.time()
        _pin_fails[:] = [t for t in _pin_fails if t > now - 600]
        if len(_pin_fails) >= 5:
            wait = int(_pin_fails[0] + 600 - now) // 60 + 1
            raise PermissionError(f"too many wrong PINs; try again in {wait} minute{'s' if wait > 1 else ''}")
        if pin_set() and not (check_pin(body.get("pin", "")) or ("new_pin" in body and token_ok(token))):
            _pin_fails.append(now)
            log("parent PIN: wrong PIN entered")
            raise PermissionError("wrong PIN")
    if "new_pin" in body:
        new = str(body["new_pin"]).strip()
        if new and not re.fullmatch(r"\d{4,8}", new):
            raise ValueError("the PIN should be 4 to 8 digits")
        if new:
            salt = secrets.token_hex(16)
            save_private(pin={"salt": salt, "hash": pin_hash(new, salt)})
            log("parent PIN set")
            return {"ok": True, "pin_set": True, "parent": True, "token": new_session(drop_others_than=token)}
        save_private(pin={})
        with _db_lock:                          # clears every sign-in
            con = db()
            try:
                con.execute("DELETE FROM sessions")
            finally:
                con.close()
        log("parent PIN removed")
        return {"ok": True, "pin_set": False, "parent": True}
    return {"ok": True, "pin_set": True, "parent": True, "token": new_session()}


# settings fields only a parent sees once a PIN is set (the kiosk reads /api/settings too, without a PIN)
PRIVATE_SETTINGS = ("list_token", "sms_people", "mail_user", "mail_host", "mail_status")


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
    out["twilio_token_set"] = bool(load_private().get("twilio_token"))
    out["sms_people"] = load_private().get("sms_people", "")
    out["mail_user"] = load_private().get("mail_user", "")
    out["mail_pass_set"] = bool(load_private().get("mail_pass"))
    out["mail_host"] = load_private().get("mail_host", "")
    out["mail_status"] = dict(_mail_status)
    out["immich_key_set"] = bool(im_key())
    out["immich_album"] = im_album()
    out["ics_set"] = bool(cur_ics_saved()) or bool(ICS_URLS)
    out["ics_from_settings"] = bool(cur_ics_saved())
    out["wx_place_env"] = WX_PLACE
    # shown in the app's Settings so the Shortcut can be set up from a phone; hidden from non-parents once a PIN is set
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
    if "people" in body:
        people, seen = [], set()
        for r in (body["people"] or [])[:12]:
            name, color = who_name(r.get("name")), str(r.get("color", "")).strip().lower()
            if name and name.lower() not in seen and re.fullmatch(r"#[0-9a-f]{6}", color):
                people.append({"name": name, "color": color})
                seen.add(name.lower())
        s["people"] = people
    if "text_scale" in body:
        s["text_scale"] = max(70, min(160, int(round(float(body["text_scale"]) / 5) * 5)))
    if "twilio_token" in body:
        save_private(twilio_token=re.sub(r"[^A-Za-z0-9]", "", str(body["twilio_token"]))[:64])
    if "mail_user" in body or "mail_pass" in body or "mail_host" in body:
        cur = load_private()
        user = str(body.get("mail_user", cur.get("mail_user", ""))).strip()[:200]
        pw = re.sub(r"\s", "", str(body.get("mail_pass") or cur.get("mail_pass", "")))[:200]
        mhost = re.sub(r"\s", "", str(body.get("mail_host", cur.get("mail_host", ""))))[:200]
        mhost = re.sub(r"^(imaps?://)", "", mhost, flags=re.I)
        new = {"mail_user": user, "mail_pass": pw if user else "", "mail_host": mhost}
        if any(new[k] != cur.get(k, "") for k in new):
            if user and pw:
                try:
                    mail_login(new).logout()
                except Exception as e:
                    if isinstance(e, (OSError, EOFError)) or "socket" in str(e).lower() or "EOF" in str(e):
                        hint = "Couldn't reach the mail server: check the address and port, and that Bridge is running."
                    else:
                        hint = "For Gmail use an app password." if not mhost else "For Proton use the Bridge password, not your account password."
                    raise ValueError(f"couldn't sign in to that mailbox ({e or type(e).__name__}). {hint}")
            save_private(**new)
            _mail_status.clear()
    if "sms_people" in body:
        save_private(sms_people=str(body["sms_people"])[:2000])
    if "notes_days" in body:
        s["notes_days"] = int(body["notes_days"]) if str(body["notes_days"]) in ("0", "1", "3", "7", "30") else 3
    if "wx_days" in body:
        s["wx_days"] = int(body["wx_days"]) if str(body["wx_days"]) in ("1", "3", "5", "7") else 3
    for k in ("wx_mono", "wx_bare"):
        if k in body:
            s[k] = bool(body[k])
        _cache.pop("weather", None)
    if "msg_sound" in body:
        s["msg_sound"] = bool(body["msg_sound"])
    if "greet_name" in body:
        s["greet_name"] = re.sub(r"\s+", " ", str(body["greet_name"])).strip()[:40]
    if "quotes" in body:
        lines = [ln.strip()[:200] for ln in str(body["quotes"]).splitlines() if ln.strip()]
        s["quotes"] = "\n".join(lines[:365])
    for k in ("blur", "photo_panel", "photo_fill", "photo_videos", "quotes_only", "rpg_on", "kiosk_lists", "goals_on", "habits_on", "fitness_on"):
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
APP_MANIFEST = {"name": "Family", "short_name": "Family", "start_url": "/app", "scope": "/", "display": "standalone",
                "background_color": "#0f1115", "theme_color": "#0f1115",
                "icons": [{"src": "/app-icon-192.png", "sizes": "192x192", "type": "image/png"},
                          {"src": "/app-icon-512.png", "sizes": "512x512", "type": "image/png", "purpose": "any maskable"}]}


class Handler(BaseHTTPRequestHandler):
    server_version = "homelab-family"

    def log_message(self, fmt, *args):
        pass

    def send_body(self, body, ctype, cache="no-store", status=200):
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Cache-Control", cache)
        if cache == "no-store":
            self.send_header("Pragma", "no-cache")
            self.send_header("Expires", "0")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def send_json(self, obj, status=200):
        self.send_body(json.dumps(obj).encode(), "application/json", status=status)

    def parent(self):
        """True when no PIN is set (open to the home network, as before) or this phone has unlocked."""
        return not pin_set() or token_ok(self.headers.get("X-Parent", "").strip())

    def read_json(self, limit=16 * 1024):
        length = min(int(self.headers.get("Content-Length", 0)), limit)
        return json.loads(self.rfile.read(length) or b"{}")

    def settings_view(self, st):
        st = with_faces(st)
        st["pin_set"], st["parent"] = pin_set(), self.parent()
        if not st["parent"]:
            for k in PRIVATE_SETTINGS:
                st.pop(k, None)
        return st

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
        if path in ("/api/background", "/api/settings") and not self.parent():
            self.close_connection = True
            self.send_json({"error": "Settings are locked. Unlock them with the parent PIN.", "locked": True}, 403)
            return
        if path == "/api/auth":
            try:
                self.send_json(auth_change(self.read_json(), self.headers.get("X-Parent", "").strip()))
            except PermissionError as e:
                self.send_json({"error": str(e), "locked": True}, 403)
            except Exception as e:
                self.send_json({"error": str(e)}, 400)
            return
        if path == "/api/app/lists":   # anyone at home can add and check off; deleting a list needs the PIN
            try:
                self.send_json(app_list_change(self.read_json(64 * 1024), self.parent()))
            except PermissionError as e:
                self.send_json({"error": str(e), "locked": True}, 403)
            except Exception as e:
                self.send_json({"error": str(e) if not isinstance(e, (KeyError, TypeError)) else "that change was missing something"}, 400)
            return
        if path == "/api/screen":   # the Remote: anyone at home can change what the kitchen screen shows
            try:
                self.send_json(screen_set(self.read_json()))
            except Exception as e:
                self.send_json({"error": str(e)}, 400)
            return
        if path == "/api/rpg":   # quests: anyone finishes their own; making quests and approving needs the PIN
            try:
                self.send_json(rpg_change(self.read_json(32 * 1024), self.parent()))
            except PermissionError as e:
                self.send_json({"error": str(e), "locked": True}, 403)
            except Exception as e:
                self.send_json({"error": str(e) if not isinstance(e, (KeyError, TypeError)) else "that change was missing something"}, 400)
            return
        if path == "/api/avatar":   # anyone sets their own picture; parents anyone's
            try:
                q = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
                person, by = person_of(q.get("person", [""])[0]), who_name(q.get("by", [""])[0])
                if person.lower() != by.lower() and not self.parent():
                    raise PermissionError("only " + person + " or a parent can change that picture")
                length = int(self.headers.get("Content-Length", 0))
                if length > AVATAR_MAX:
                    raise ValueError("that picture is too big")
                avatar_save(person, self.rfile.read(length) if length else b"")
                log(f"profile picture {'set' if length else 'removed'} for {person}")
                self.send_json({"ok": True, "photos": avatar_versions()})
            except PermissionError as e:
                self.close_connection = True
                self.send_json({"error": str(e), "locked": True}, 403)
            except Exception as e:
                self.close_connection = True
                self.send_json({"error": str(e)}, 400)
            return
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
                self.send_json(self.settings_view(save_settings(json.loads(self.rfile.read(length) or b"{}"))))
            except Exception as e:
                self.send_json({"error": str(e)}, 400)
            return
        if path == "/api/sms":   # Twilio's webhook; the only path the public tunnel name should allow
            try:
                length = min(int(self.headers.get("Content-Length", 0)), 16 * 1024)
                params = {k: v[0] for k, v in urllib.parse.parse_qs(self.rfile.read(length).decode(), keep_blank_values=True).items()}
                url = "https://" + self.headers.get("Host", "") + self.path
                ok = sms_note(url, params, self.headers.get("X-Twilio-Signature", ""))
                body = b'<?xml version="1.0" encoding="UTF-8"?><Response></Response>'
                self.send_body(body, "text/xml", status=403 if ok == "bad" else 200)
            except Exception as e:
                self.send_json({"error": str(e)}, 400)
            return
        if path == "/api/notes":   # same trust as the settings page: anyone on the home network
            try:
                length = min(int(self.headers.get("Content-Length", 0)), 16 * 1024)
                raw = self.rfile.read(length) or b"{}"
                if "json" in self.headers.get("Content-Type", ""):
                    body = json.loads(raw)
                else:  # form fields or plain text work too, for a Shortcut
                    q = urllib.parse.parse_qs(raw.decode())
                    body = {k: v[0] for k, v in q.items()} if q and "=" in raw.decode() else {"text": raw.decode()}
                if body.get("clear") and not self.parent():
                    self.send_json({"error": "Clearing every message needs the parent PIN.", "locked": True}, 403)
                    return
                self.send_json(save_note(body))
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
            elif path == "/app":
                self.send_body((HERE / "app.html").read_bytes(), "text/html; charset=utf-8", "no-cache")
            elif path == "/settings":   # the old settings page now lives in the app
                self.send_response(302)
                self.send_header("Location", "/app#settings")
                self.send_header("Content-Length", "0")
                self.end_headers()
            elif path == "/app.webmanifest":
                self.send_body(json.dumps(APP_MANIFEST).encode(), "application/manifest+json", "public, max-age=86400")
            elif re.fullmatch(r"/app-icon-(180|192|512)\.png", path):
                f = HERE / "app-icons" / path.lstrip("/")
                if not f.exists():
                    self.send_error(HTTPStatus.NOT_FOUND)
                    return
                self.send_body(f.read_bytes(), "image/png", "public, max-age=604800")
            elif path == "/api/settings":
                self.send_json(self.settings_view(load_settings()))
            elif path == "/api/auth":
                self.send_json({"pin_set": pin_set(), "parent": self.parent()})
            elif path == "/api/app/lists":
                self.send_json(app_lists_payload())
            elif path == "/api/rpg":
                self.send_json(rpg_payload())
            elif path == "/api/screen":
                self.send_json(screen_state())
            elif path == "/api/month":
                ym = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query).get("m", [""])[0]
                if not re.fullmatch(r"\d{4}-(0[1-9]|1[0-2])", ym):
                    ym = dt.datetime.now(LOCAL_TZ).strftime("%Y-%m")
                self.send_json(cached("month:" + ym, 300, lambda: month_payload(ym)))
            elif path.startswith("/avatar/"):
                f = avatar_path(urllib.parse.unquote(path[8:]))
                if not f.exists():
                    self.send_error(HTTPStatus.NOT_FOUND)
                    return
                self.send_body(f.read_bytes(), "image/jpeg", "public, max-age=31536000, immutable")
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
                self.send_json(lists_payload(with_app=True))
            elif path == "/api/notes":
                self.send_json({"now": int(time.time()), "notes": live_notes()})
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
    db_init()
    threading.Thread(target=daily_loop, daemon=True).start()
    threading.Thread(target=mail_loop, daemon=True).start()
    ThreadingHTTPServer(("0.0.0.0", PORT), Handler).serve_forever()


if __name__ == "__main__":
    main()
