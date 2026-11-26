#!/usr/bin/env python3
"""BioLab Hub server.

Serves the web pages (public/) and a small JSON API with real accounts.
Data lives in JSON files inside the data/ folder. Only this script writes to them,
and it checks who is asking before it changes anything.

Run locally:      python app.py
Create an admin:  python app.py create-admin
Production:       gunicorn app:app   (or the WSGI file of your host, see README.md)
"""
import datetime, getpass, hashlib, json, os, re, secrets, shutil, sys, threading, time
from contextlib import contextmanager
from urllib.parse import urlparse

from flask import Flask, abort, jsonify, make_response, request, send_from_directory
from werkzeug.security import check_password_hash, generate_password_hash

try:
    import fcntl                      # file locking between worker processes (Linux/macOS)
except ImportError:                   # Windows: threads are still protected below
    fcntl = None
try:
    from zoneinfo import ZoneInfo
except ImportError:
    ZoneInfo = None

BASE = os.path.dirname(os.path.abspath(__file__))
PUBLIC = os.path.join(BASE, "public")            # pages: anyone may download these
PDF_DIR = os.path.join(BASE, "pdf")              # PDFs: only signed-in, approved members
SEED = os.path.join(BASE, "seed")                # starting data, never served
DATA = os.environ.get("DATA_DIR", os.path.join(BASE, "data"))
os.makedirs(DATA, exist_ok=True)

SESSION_DAYS = 14
ROOM_START, ROOM_END, STEP = 8 * 60, 22 * 60, 30
SLOT_IDS = {"m", "d", "e"}
LOC = {"S1", "S2", "S5", "S6", "F"}
SEC = {"r", "s", "h", "f"}

app = Flask(__name__, static_folder=None)
app.config["MAX_CONTENT_LENGTH"] = 1_000_000


# ------------------------------------------------------------------ storage
_thread_lock = threading.RLock()


@contextmanager
def locked():
    """One writer at a time, across threads and (on Linux) across processes. Do not nest."""
    with _thread_lock:
        fh = None
        if fcntl:
            fh = open(os.path.join(DATA, ".lock"), "w")
            fcntl.flock(fh, fcntl.LOCK_EX)
        try:
            yield
        finally:
            if fh:
                fcntl.flock(fh, fcntl.LOCK_UN)
                fh.close()


def _path(name):
    return os.path.join(DATA, name + ".json")


def read(name, default):
    try:
        with open(_path(name), encoding="utf-8") as f:
            return json.load(f)
    except FileNotFoundError:
        return default


def write(name, obj):
    """Atomic write: the file is either the old version or the new one, never half-written."""
    p = _path(name)
    tmp = p + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, indent=1)
        f.flush()
        os.fsync(f.fileno())
    if os.path.exists(p):
        shutil.copy2(p, p + ".bak")              # one-step backup
    os.replace(tmp, p)


def now_ms():
    return int(time.time() * 1000)


def lab_now():
    tz = os.environ.get("LAB_TZ", "UTC")
    try:
        return datetime.datetime.now(ZoneInfo(tz)) if ZoneInfo else datetime.datetime.now()
    except Exception:
        return datetime.datetime.now(datetime.timezone.utc)


def init_data():
    with locked():
        for name in ("chemicals", "buffers", "docs"):
            if not os.path.exists(_path("inv_" + name)):
                seed = os.path.join(SEED, name + ".json")
                items = json.load(open(seed, encoding="utf-8"))["items"] if os.path.exists(seed) else []
                write("inv_" + name, {"items": items, "at": now_ms(), "by": "seed"})
        if not os.path.exists(_path("users")):
            write("users", {"users": {}})
        if not os.path.exists(_path("bookings")):
            write("bookings", {"b": {}})


# ------------------------------------------------------------------ helpers
def clean(v, n):
    return re.sub(r"[\x00-\x1f\x7f]", "", str(v if v is not None else "")).strip()[:n]


def err(msg, code=400):
    return jsonify({"error": msg}), code


def client_ip():
    xff = request.headers.get("X-Forwarded-For", "")
    return (xff.split(",")[-1].strip() if xff else request.remote_addr) or "?"


_fails = {}


def too_many(key, limit, window):
    t = time.time()
    _fails[key] = [x for x in _fails.get(key, []) if t - x < window]
    return len(_fails[key]) >= limit


def note_fail(key):
    _fails.setdefault(key, []).append(time.time())


# ------------------------------------------------------------------ sessions and users
def make_session(uid):
    token = secrets.token_urlsafe(32)
    with locked():
        s = read("sessions", {})
        t = time.time()
        s = {h: v for h, v in s.items() if v["exp"] > t}
        mine = sorted([h for h, v in s.items() if v["uid"] == uid], key=lambda h: s[h]["exp"])
        for h in mine[:-9]:                       # keep at most 10 sessions per person
            s.pop(h)
        s[hashlib.sha256(token.encode()).hexdigest()] = {"uid": uid, "exp": t + SESSION_DAYS * 86400}
        write("sessions", s)
    return token


def set_cookie(resp, token, max_age=SESSION_DAYS * 86400):
    secure = request.is_secure or request.headers.get("X-Forwarded-Proto") == "https" or os.environ.get("COOKIE_SECURE") == "1"
    resp.set_cookie("sid", token, max_age=max_age, httponly=True, samesite="Lax", secure=secure, path="/")
    return resp


def current_user():
    tok = request.cookies.get("sid")
    if not tok:
        return None
    s = read("sessions", {}).get(hashlib.sha256(tok.encode()).hexdigest())
    if not s or s["exp"] < time.time():
        return None
    return read("users", {"users": {}})["users"].get(s["uid"])


def public_user(u):
    return {"id": u["id"], "username": u["username"], "name": u["name"], "grp": u.get("grp", ""),
            "note": u.get("note", ""), "at": u.get("at", 0), "status": u["status"], "role": u["role"]}


def require(level):
    """level: 'login' (any account), 'member' (approved or admin), 'admin'."""
    u = current_user()
    if not u:
        return None, err("Please sign in.", 401)
    if level == "admin" and not (u["role"] == "admin" and u["status"] == "approved"):
        return None, err("Administrators only.", 403)
    if level == "member" and not (u["status"] == "approved"):
        return None, err("Your account is not approved yet.", 403)
    return u, None


@app.before_request
def csrf_guard():
    if request.method in ("POST", "PUT", "PATCH", "DELETE") and request.path.startswith("/api/"):
        if request.headers.get("X-Requested-With") != "biolab" or not request.is_json:
            return err("Bad request.", 400)


@app.after_request
def headers(resp):
    resp.headers["X-Content-Type-Options"] = "nosniff"
    resp.headers["Referrer-Policy"] = "same-origin"
    resp.headers["X-Frame-Options"] = "SAMEORIGIN"
    resp.headers["Content-Security-Policy"] = (
        "default-src 'self'; script-src 'self' 'unsafe-inline'; "
        "style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; font-src https://fonts.gstatic.com; "
        "img-src 'self' data:; frame-src 'self' https://drive.google.com https://docs.google.com; "
        "connect-src 'self'; object-src 'self'; base-uri 'self'; form-action 'self'; frame-ancestors 'self'")
    if request.path.startswith("/api/"):
        resp.headers["Cache-Control"] = "no-store"
    return resp


@app.errorhandler(404)
def nf(e):
    return err("Not found.", 404) if request.path.startswith("/api/") else ("Not found", 404)


@app.errorhandler(413)
def too_big(e):
    return err("Request is too large.", 413)


# ------------------------------------------------------------------ accounts
USERNAME = re.compile(r"^[a-z0-9][a-z0-9._-]{2,31}$")
_DUMMY = generate_password_hash("not-a-real-password")


@app.post("/api/register")
def register():
    d = request.get_json(silent=True) or {}
    username = clean(d.get("username"), 32).lower()
    password = str(d.get("password") or "")
    name, grp, note = clean(d.get("name"), 60), clean(d.get("grp"), 80), clean(d.get("note"), 200)
    if not USERNAME.match(username):
        return err("Username: 3-32 characters, letters, digits, dot, dash or underscore.")
    if not 8 <= len(password) <= 128 or password.lower() == username:
        return err("Password must be 8-128 characters.")
    if not name or not grp:
        return err("Please fill in your name and group.")
    if too_many("reg|" + client_ip(), 10, 3600):
        return err("Too many sign-ups from this address. Try again later.", 429)
    note_fail("reg|" + client_ip())
    with locked():
        users = read("users", {"users": {}})
        if any(u["username"] == username for u in users["users"].values()):
            return err("That username is taken.", 409)
        uid = secrets.token_hex(8)
        users["users"][uid] = {"id": uid, "username": username, "pw": generate_password_hash(password), "name": name,
                               "grp": grp, "note": note, "role": "member", "status": "pending", "at": now_ms()}
        write("users", users)
    return set_cookie(make_response(jsonify({"ok": True})), make_session(uid))


@app.post("/api/login")
def login():
    d = request.get_json(silent=True) or {}
    username, password = clean(d.get("username"), 32).lower(), str(d.get("password") or "")[:128]
    key = "login|" + username + "|" + client_ip()
    if too_many(key, 8, 600):
        return err("Too many attempts. Please wait 10 minutes.", 429)
    u = next((x for x in read("users", {"users": {}})["users"].values() if x["username"] == username), None)
    ok = check_password_hash(u["pw"] if u else _DUMMY, password)      # same work whether or not the user exists
    if not (u and ok):
        note_fail(key)
        return err("Wrong username or password.", 401)
    _fails.pop(key, None)
    return set_cookie(make_response(jsonify({"ok": True})), make_session(u["id"]))


@app.post("/api/logout")
def logout():
    tok = request.cookies.get("sid")
    if tok:
        with locked():
            s = read("sessions", {})
            if s.pop(hashlib.sha256(tok.encode()).hexdigest(), None):
                write("sessions", s)
    return set_cookie(make_response(jsonify({"ok": True})), "", 0)


@app.get("/api/me")
def me():
    u = current_user()
    return jsonify({"id": None} if not u else public_user(u))


@app.get("/api/members")
def members():
    u, e = require("admin")
    if e:
        return e
    return jsonify({"members": [public_user(x) for x in read("users", {"users": {}})["users"].values()]})


def _change_user(uid, field, value):
    admin, e = require("admin")
    if e:
        return e
    if uid == admin["id"]:
        return err("You cannot change your own account here.", 400)
    with locked():
        users = read("users", {"users": {}})
        if uid not in users["users"]:
            return err("No such user.", 404)
        users["users"][uid][field] = value
        write("users", users)
    return jsonify({"ok": True})


@app.post("/api/members/<uid>/status")
def member_status(uid):
    v = (request.get_json(silent=True) or {}).get("status")
    return _change_user(uid, "status", v) if v in ("approved", "rejected", "pending") else err("Bad status.")


@app.post("/api/members/<uid>/role")
def member_role(uid):
    v = (request.get_json(silent=True) or {}).get("role")
    return _change_user(uid, "role", v) if v in ("admin", "member") else err("Bad role.")


# ------------------------------------------------------------------ inventory (chemicals, buffers, documents)
LOCAL_PDF = re.compile(r"^(?!.*\.\.)\w[\w ./()-]*\.pdf$", re.I | re.A)


def _id(x, seen):
    i = clean(x.get("id"), 40)
    if not re.fullmatch(r"[\w-]{1,40}", i, re.A):
        i = secrets.token_hex(4)
    if i in seen:
        raise ValueError("Duplicate id.")
    seen.add(i)
    return i


def _name(x):
    n = clean(x.get("n"), 120)
    if not n:
        raise ValueError("Every record needs a name.")
    return n


def valid_link(u):
    u = clean(u, 400)
    if not u:
        return ""
    if LOCAL_PDF.match(u) and "//" not in u:
        return u
    p = urlparse(u)
    if p.scheme != "https" or not p.netloc:
        raise ValueError("Links must start with https:// or be a PDF path like pdf/name.pdf.")
    return u


def valid_date(s):
    s = clean(s, 10)
    if s:
        datetime.date.fromisoformat(s)
    return s


def clean_items(name, items):
    if not isinstance(items, list) or len(items) > {"chemicals": 3000, "buffers": 1000, "docs": 1000}[name]:
        raise ValueError("Bad list.")
    out, seen = [], set()
    for x in items:
        if not isinstance(x, dict):
            raise ValueError("Bad record.")
        r = {"id": _id(x, seen), "n": _name(x)}
        if name == "chemicals":
            if x.get("l") not in LOC or x.get("s") not in SEC:
                raise ValueError("Bad location or section.")
            r.update(a=clean(x.get("a"), 120), l=x["l"], s=x["s"], d=bool(x.get("d")), t=clean(x.get("t"), 120))
        elif name == "buffers":
            r.update(v=clean(x.get("v"), 120), p=valid_date(x.get("p")), t=clean(x.get("t"), 120))
        else:
            r.update(u=valid_link(x.get("u")), g=clean(x.get("g"), 60) or "General", x=clean(x.get("x"), 200))
        out.append(r)
    return out


@app.get("/api/inventory/<name>")
def inv_get(name):
    if name not in ("chemicals", "buffers", "docs"):
        abort(404)
    u, e = require("member")
    return e or jsonify(read("inv_" + name, {"items": [], "at": 0}))


@app.put("/api/inventory/<name>")
def inv_put(name):
    if name not in ("chemicals", "buffers", "docs"):
        abort(404)
    u, e = require("admin")
    if e:
        return e
    try:
        items = clean_items(name, (request.get_json(silent=True) or {}).get("items"))
    except (ValueError, TypeError) as ex:
        return err(str(ex) or "Invalid data.")
    with locked():
        write("inv_" + name, {"items": items, "at": now_ms(), "by": u["id"]})
    return jsonify({"ok": True})


# ------------------------------------------------------------------ bookings
KEY = re.compile(r"^(room|akta|pcr)\|(\d{4}-\d{2}-\d{2})\|([A-Za-z0-9-]{1,12})$")


def parse_key(key):
    m = KEY.match(key or "")
    if not m:
        raise ValueError("Bad booking.")
    res, date, sid = m.groups()
    day = datetime.date.fromisoformat(date)
    now = lab_now()
    if day < now.date():
        raise ValueError("Past dates cannot be booked.")
    if day > now.date() + datetime.timedelta(days=400):
        raise ValueError("That date is too far ahead.")
    span = None
    if res == "room":
        mm = re.fullmatch(r"(\d{2})(\d{2})-(\d{2})(\d{2})", sid)
        if not mm:
            raise ValueError("Bad time range.")
        a, b = int(mm[1]) * 60 + int(mm[2]), int(mm[3]) * 60 + int(mm[4])
        if a % STEP or b % STEP or not ROOM_START <= a < b <= ROOM_END:
            raise ValueError("Room A can be booked between 08:00 and 22:00 in 30-minute steps.")
        if day == now.date() and a < now.hour * 60 + now.minute:
            raise ValueError("That time has already passed.")
        span = (a, b)
    elif sid not in SLOT_IDS:
        raise ValueError("Bad slot.")
    return res, date, sid, span


def _span(k):
    sid = k.split("|")[2]
    if sid == "day":
        return ROOM_START, ROOM_END
    a, b = sid.split("-")
    return int(a[:2]) * 60 + int(a[2:]), int(b[:2]) * 60 + int(b[2:])


@app.get("/api/bookings")
def bookings_get():
    u, e = require("member")
    return e or jsonify({"bookings": read("bookings", {"b": {}})["b"]})


@app.post("/api/bookings")
def bookings_add():
    u, e = require("member")
    if e:
        return e
    d = request.get_json(silent=True) or {}
    key = clean(d.get("key"), 40)
    try:
        res, date, sid, span = parse_key(key)
    except ValueError as ex:
        return err(str(ex))
    with locked():
        data = read("bookings", {"b": {}})
        b = data["b"]
        if res == "room":
            clash = any(k.startswith("room|" + date + "|") and _span(k)[0] < span[1] and _span(k)[1] > span[0] for k in b)
        else:
            clash = key in b
        if clash:
            return err("Those hours are already booked. Please choose another time.", 409)
        b[key] = {"n": u["name"], "c": clean(d.get("note"), 80), "by": u["id"], "at": now_ms()}
        cutoff = (lab_now().date() - datetime.timedelta(days=60)).isoformat()
        data["b"] = {k: v for k, v in b.items() if k.split("|")[1] >= cutoff}
        write("bookings", data)
    return jsonify({"ok": True}), 201


@app.post("/api/bookings/cancel")
def bookings_cancel():
    u, e = require("member")
    if e:
        return e
    key = clean((request.get_json(silent=True) or {}).get("key"), 40)
    with locked():
        data = read("bookings", {"b": {}})
        rec = data["b"].get(key)
        if not rec:
            return err("Booking not found.", 404)
        admin = u["role"] == "admin"
        if not admin and (rec["by"] != u["id"] or key.split("|")[1] < lab_now().date().isoformat()):
            return err("Only the person who booked it or an administrator can cancel this.", 403)
        del data["b"][key]
        write("bookings", data)
    return jsonify({"ok": True})


# ------------------------------------------------------------------ pages and PDFs
@app.get("/pdf/<path:f>")
def pdf(f):
    u, e = require("member")
    if e:
        return e
    return send_from_directory(PDF_DIR, f, mimetype="application/pdf")


@app.get("/")
def home():
    return send_from_directory(PUBLIC, "index.html")


@app.get("/<path:p>")
def files(p):
    if p.startswith("api/") or any(part.startswith(".") for part in p.split("/")):
        abort(404)
    return send_from_directory(PUBLIC, p)


init_data()


# ------------------------------------------------------------------ command line
def create_admin():
    username = input("Admin username: ").strip().lower()
    if not USERNAME.match(username):
        sys.exit("Username: 3-32 characters, letters, digits, dot, dash or underscore.")
    pw = getpass.getpass("Password (min 8 characters): ")
    if len(pw) < 8 or pw != getpass.getpass("Repeat password: "):
        sys.exit("Passwords do not match or are too short.")
    name = input("Full name: ").strip()[:60] or username
    with locked():
        users = read("users", {"users": {}})
        u = next((x for x in users["users"].values() if x["username"] == username), None)
        if u:
            u.update(pw=generate_password_hash(pw), role="admin", status="approved")
            print("Existing account updated: new password, administrator.")
        else:
            uid = secrets.token_hex(8)
            users["users"][uid] = {"id": uid, "username": username, "pw": generate_password_hash(pw), "name": name,
                                   "grp": "", "note": "", "role": "admin", "status": "approved", "at": now_ms()}
            print("Administrator created.")
        write("users", users)
        write("sessions", {})                       # sign everyone out after a password change


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "create-admin":
        create_admin()
    else:
        port = int(os.environ.get("PORT", 8000))
        print(f"BioLab Hub on http://127.0.0.1:{port}  (create the first admin with: python app.py create-admin)")
        app.run(host=os.environ.get("HOST", "127.0.0.1"), port=port)
