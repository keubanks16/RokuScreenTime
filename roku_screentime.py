#!/usr/bin/env python3
"""
Roku Screen Time
================
Runs on a Raspberry Pi (or any always-on computer) that can reach your Roku TVs.
It watches what each TV is doing and, per TV, enforces:
  * a Lock button (TV is switched back off until you unlock it)
  * a daily time limit (separate weekday / weekend minutes)
  * blocked apps (a parent can unlock any of them for a while)
  * a bedtime lockout (TV is switched off during set hours)
The control panel is a web page served by this script: http://<pi-name>.local:8080

No extra packages needed - Python 3 standard library only.

  python3 roku_screentime.py                  run it
  sudo python3 roku_screentime.py --install   start automatically on every boot
"""
import hashlib
import json
import os
import secrets
import socket
import subprocess
import sys
import threading
import time
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

PORT = int(os.environ.get("SCREENTIME_PORT", "8080"))
ROKU_PORT = int(os.environ.get("ROKU_PORT", "8060"))
DATA = os.environ.get(
    "SCREENTIME_DATA", os.path.join(os.path.expanduser("~"), ".roku_screentime.json")
)
UPDATE_URL = os.environ.get(
    "SCREENTIME_UPDATE_URL",
    "https://raw.githubusercontent.com/keubanks16/RokuScreenTime/main/roku_screentime.py",
)
ME = os.path.abspath(__file__)
POLL_SECONDS = 5
KEEP_DAYS = 14

# Rules are kept per TV. A newly added TV starts with every rule off.
TV_DEFAULTS = {
    "ip": "",
    "name": "",
    "label": "",
    "limit_on": False,
    "limit_weekday": 120,
    "limit_weekend": 180,
    "bed_on": False,
    "bed_start": "20:30",
    "bed_end": "06:30",
    "blocked": [],
    "usage": {},
    "bonus": {},
    "pause_until": 0,
    "tv_locked": False,
    "unlock_until": {},
    "apps": {},
}
RULE_KEYS = [k for k in TV_DEFAULTS if k not in ("ip", "name", "label")]

LOCK = threading.RLock()
S = {"pin": None, "tvs": []}
LIVE = {}  # ip -> live status
_dirty = False
_last_save = 0.0
_pin_fails = {"count": 0, "until": 0.0}


def new_tv(ip, name=""):
    tv = json.loads(json.dumps(TV_DEFAULTS))
    tv["ip"], tv["name"] = ip, name
    return tv


def find_tv(ip):
    for tv in S["tvs"]:
        if tv["ip"] == ip:
            return tv
    return None


def live(ip):
    return LIVE.setdefault(ip, {"reachable": False, "on": False, "app_id": None, "app_name": "",
                                "is_tv": True, "last_action": "", "screensaver": False,
                                "ecp_mode": ""})


# ---------------------------------------------------------------- storage
def load():
    global S
    try:
        with open(DATA) as f:
            saved = json.load(f)
    except (OSError, ValueError):
        saved = {}
    tvs = []
    for t in saved.get("tvs", []):
        tv = new_tv(t.get("ip", ""))
        tv.update(t)
        if tv["ip"]:
            tvs.append(tv)
    if not tvs and saved.get("roku_ip"):  # upgrade from the single-TV version
        tv = new_tv(saved["roku_ip"])
        for k in RULE_KEYS:
            if k in saved:
                tv[k] = saved[k]
        tvs.append(tv)
    S = {"pin": saved.get("pin"), "tvs": tvs}


def save(force=False):
    global _dirty, _last_save
    with LOCK:
        if not force and (not _dirty or time.time() - _last_save < 60):
            return
        tmp = DATA + ".tmp"
        with open(tmp, "w") as f:
            json.dump(S, f)
        os.replace(tmp, DATA)
        _dirty = False
        _last_save = time.time()


def today():
    return datetime.now().strftime("%Y-%m-%d")


# ---------------------------------------------------------------- roku (ECP)
def ecp(ip, path, post=False, timeout=3):
    req = urllib.request.Request(
        "http://%s:%d/%s" % (ip, ROKU_PORT, path),
        data=b"" if post else None,
        method="POST" if post else "GET",
    )
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def device_info(ip):
    root = ET.fromstring(ecp(ip, "query/device-info"))
    get = lambda tag: (root.findtext(tag) or "").strip()
    return {
        "name": get("user-device-name") or get("friendly-device-name") or get("model-name") or ip,
        "power": get("power-mode") or "PowerOn",
        "is_tv": get("is-tv").lower() == "true",
        "ecp_mode": get("ecp-setting-mode").lower(),
    }


def active_app(ip):
    root = ET.fromstring(ecp(ip, "query/active-app"))
    app = root.find("app")
    app_id = app.get("id") if app is not None else None
    name = (app.text or "").strip() if app is not None else ""
    return app_id, name, root.find("screensaver") is not None


def installed_apps(ip):
    root = ET.fromstring(ecp(ip, "query/apps", timeout=10))
    return {a.get("id"): (a.text or "").strip() for a in root.findall("app") if a.get("id")}


def why(e):
    code = getattr(e, "code", None)
    if code in (401, 403):
        return ("the TV refused it (error %d). On the TV set Settings > System > Advanced system "
                "settings > Control by mobile apps > Network access to Enabled (or Permissive)" % code)
    return "error %s" % (code or type(e).__name__)


def press(ip, key):
    """Send a remote key. Returns None if it worked, else a reason."""
    try:
        ecp(ip, "keypress/" + key, post=True)
        return None
    except Exception as e:
        return why(e)


def tv_off(ip, is_tv):
    err = press(ip, "Home")
    if is_tv and not err:
        err = press(ip, "PowerOff")
    return err


def local_ips():
    """Every IPv4 address this computer has (ethernet and WiFi can be on different networks)."""
    ips = []
    try:
        out = subprocess.run(["hostname", "-I"], capture_output=True, text=True, timeout=3).stdout
        ips = [x for x in out.split() if "." in x and not x.startswith("127.")]
    except Exception:
        pass
    return ips or [""]


def discover(wait=3):
    """Find Rokus with SSDP, searching on every network this computer is connected to."""
    msg = ("M-SEARCH * HTTP/1.1\r\nHost: 239.255.255.250:1900\r\n"
           'Man: "ssdp:discover"\r\nST: roku:ecp\r\nMX: 2\r\n\r\n').encode()
    socks = []
    for ip in local_ips():
        try:
            sk = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            if ip:
                sk.bind((ip, 0))
                sk.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_IF, socket.inet_aton(ip))
            sk.setblocking(False)
            sk.sendto(msg, ("239.255.255.250", 1900))
            sk.sendto(msg, ("239.255.255.250", 1900))
            socks.append(sk)
        except OSError:
            pass
    found = []
    end = time.time() + wait
    while time.time() < end:
        for sk in socks:
            try:
                data, addr = sk.recvfrom(2048)
            except OSError:
                continue
            if b"roku" in data.lower() and addr[0] not in found:
                found.append(addr[0])
        time.sleep(0.1)
    for sk in socks:
        sk.close()
    out = []
    for ip in found:
        try:
            name = device_info(ip)["name"]
        except Exception:
            name = ip
        out.append({"ip": ip, "name": name, "added": find_tv(ip) is not None})
    return out


# ---------------------------------------------------------------- rules
def limit_minutes_today(tv):
    weekend = datetime.now().weekday() >= 5
    base = tv["limit_weekend"] if weekend else tv["limit_weekday"]
    return int(base) + int(tv["bonus"].get(today(), 0))


def used_seconds_today(tv):
    return sum(tv["usage"].get(today(), {}).values())


def in_bedtime(tv, now=None):
    now = now or datetime.now()
    try:
        sh, sm = [int(x) for x in tv["bed_start"].split(":")]
        eh, em = [int(x) for x in tv["bed_end"].split(":")]
    except ValueError:
        return False
    cur, start, end = now.hour * 60 + now.minute, sh * 60 + sm, eh * 60 + em
    if start == end:
        return False
    if start < end:
        return start <= cur < end
    return cur >= start or cur < end


def note(ip, text):
    live(ip)["last_action"] = "%s - %s" % (datetime.now().strftime("%-I:%M %p"), text)


def tick(ip, dt):
    global _dirty
    L = live(ip)
    try:
        info = device_info(ip)
        app_id, app_name, saver = active_app(ip)
    except Exception:
        L.update(reachable=False, on=False, app_id=None, app_name="")
        return

    on = info["power"] == "PowerOn"
    with LOCK:
        tv = find_tv(ip)
        if tv is None:  # removed while we were asking it
            return
        L.update(reachable=True, on=on, app_id=app_id, app_name=app_name,
                 is_tv=info["is_tv"], screensaver=saver, ecp_mode=info["ecp_mode"])
        now = time.time()
        if tv["name"] != info["name"]:
            tv["name"] = info["name"]
            _dirty = True
        if app_id and app_name and tv["apps"].get(app_id) != app_name:
            tv["apps"][app_id] = app_name
            _dirty = True

        if on and app_id and not saver:
            day = tv["usage"].setdefault(today(), {})
            day[app_id] = day.get(app_id, 0) + dt
            _dirty = True

        if not on:
            return
        if tv["tv_locked"]:
            action = ("off", "TV is locked - turned it off")
        elif tv["pause_until"] > now:
            return
        elif tv["bed_on"] and in_bedtime(tv):
            action = ("off", "Bedtime - turned the TV off")
        elif tv["limit_on"] and app_id and used_seconds_today(tv) >= limit_minutes_today(tv) * 60:
            action = ("off", "Daily limit reached - turned the TV off")
        elif app_id in tv["blocked"] and tv["unlock_until"].get(app_id, 0) < now:
            action = ("home", "Blocked %s - sent the TV to Home" % (app_name or app_id))
        else:
            return

    err = tv_off(ip, info["is_tv"]) if action[0] == "off" else press(ip, "Home")
    note(ip, "Tried to enforce a rule but " + err if err else action[1])


def refresh_apps(ip):
    apps = installed_apps(ip)
    with LOCK:
        tv = find_tv(ip)
        if tv is not None:
            tv["apps"].update(apps)
    save(force=True)


def watch(ip, stop):
    """One watcher thread per TV, so a TV that is off never slows down the others."""
    last = time.time()
    last_apps = 0.0
    while not stop.is_set():
        now = time.time()
        dt = min(now - last, POLL_SECONDS * 3)
        last = now
        try:
            tick(ip, dt)
            if live(ip)["reachable"] and now - last_apps > 300:
                last_apps = now
                try:
                    refresh_apps(ip)
                except Exception as e:
                    print("app list %s: %s" % (ip, why(e)), flush=True)
        except Exception as e:  # never let a watcher die
            print("watch error %s: %s" % (ip, e), flush=True)
        stop.wait(POLL_SECONDS)


WATCHERS = {}  # ip -> stop event


def sync_watchers():
    with LOCK:
        wanted = {tv["ip"] for tv in S["tvs"]}
        for ip in list(WATCHERS):
            if ip not in wanted:
                WATCHERS.pop(ip).set()
                LIVE.pop(ip, None)
        for ip in wanted:
            if ip not in WATCHERS:
                stop = threading.Event()
                WATCHERS[ip] = stop
                threading.Thread(target=watch, args=(ip, stop), daemon=True).start()


def housekeeping():
    last_day = today()
    while True:
        time.sleep(30)
        try:
            if today() != last_day:
                last_day = today()
                cutoff = (datetime.now() - timedelta(days=KEEP_DAYS)).strftime("%Y-%m-%d")
                with LOCK:
                    for tv in S["tvs"]:
                        for key in ("usage", "bonus"):
                            tv[key] = {d: v for d, v in tv[key].items() if d >= cutoff}
                save(force=True)
            save()
        except Exception as e:
            print("housekeeping error:", e, flush=True)


# ---------------------------------------------------------------- self-update
def version():
    try:
        with open(ME, "rb") as f:
            return hashlib.sha1(f.read()).hexdigest()[:7]
    except OSError:
        return "unknown"


def restart():
    save(force=True)
    os.execv(sys.executable, [sys.executable, ME])


def update():
    """Download the newest copy of this script, check it, swap it in and restart."""
    try:
        req = urllib.request.Request(UPDATE_URL + "?t=%d" % time.time(),
                                     headers={"Cache-Control": "no-cache"})
        with urllib.request.urlopen(req, timeout=20) as r:
            new = r.read()
    except Exception as e:
        return {"error": "Couldn't download the update (%s). Is the Pi online?" % why(e)}
    if hashlib.sha1(new).hexdigest()[:7] == version():
        return {"ok": True, "message": "Already up to date."}
    try:
        if b"Roku Screen Time" not in new or b"def main()" not in new:
            raise ValueError("not the app")
        compile(new, ME, "exec")
    except Exception:
        return {"error": "The downloaded update looked broken, so nothing was changed."}
    try:
        with open(ME, "rb") as f:
            old = f.read()
        with open(ME + ".bak", "wb") as f:
            f.write(old)
        tmp = ME + ".new"
        with open(tmp, "wb") as f:
            f.write(new)
        os.replace(tmp, ME)
    except OSError as e:
        return {"error": "Couldn't save the update: %s" % e}
    threading.Timer(1.0, restart).start()
    return {"ok": True, "restarting": True, "message": "Updated. Restarting..."}


# ---------------------------------------------------------------- web
def hash_pin(pin, salt):
    return hashlib.sha256((salt + pin).encode()).hexdigest()


def pin_ok(pin):
    if time.time() < _pin_fails["until"]:
        return False
    p = S["pin"]
    ok = bool(p) and bool(pin) and secrets.compare_digest(hash_pin(pin, p["salt"]), p["hash"])
    if ok:
        _pin_fails["count"] = 0
    elif pin:
        _pin_fails["count"] += 1
        if _pin_fails["count"] >= 5:
            _pin_fails.update(count=0, until=time.time() + 60)
    return ok


def valid_time(t):
    try:
        h, m = t.split(":")
        return 0 <= int(h) < 24 and 0 <= int(m) < 60
    except (ValueError, AttributeError):
        return False


def tv_state(tv):
    now = time.time()
    usage = tv["usage"].get(today(), {})
    apps = [{"id": i, "name": n, "blocked": i in tv["blocked"],
             "unlock_until": tv["unlock_until"].get(i, 0) if tv["unlock_until"].get(i, 0) > now else 0}
            for i, n in tv["apps"].items()]
    apps.sort(key=lambda a: (not a["blocked"], a["name"].lower()))
    return {
        "ip": tv["ip"], "name": tv["label"] or tv["name"] or tv["ip"],
        "label": tv["label"], "model": tv["name"],
        "live": dict(live(tv["ip"])),
        "limit_on": tv["limit_on"], "limit_weekday": tv["limit_weekday"],
        "limit_weekend": tv["limit_weekend"],
        "bed_on": tv["bed_on"], "bed_start": tv["bed_start"], "bed_end": tv["bed_end"],
        "bonus_today": tv["bonus"].get(today(), 0),
        "limit_today": limit_minutes_today(tv),
        "used_seconds": int(used_seconds_today(tv)),
        "bedtime_now": bool(tv["bed_on"] and in_bedtime(tv)),
        "pause_until": tv["pause_until"] if tv["pause_until"] > now else 0,
        "tv_locked": bool(tv["tv_locked"]),
        "apps": apps,
        "usage": sorted(
            [{"name": tv["apps"].get(i, i), "seconds": int(s)} for i, s in usage.items()],
            key=lambda u: -u["seconds"]),
    }


def state():
    with LOCK:
        return {"tvs": [tv_state(tv) for tv in S["tvs"]], "version": VERSION}


def do_action(a):
    global _dirty
    kind = a.get("type")
    ip = str(a.get("tv", "")).strip()

    if kind == "discover":
        return {"found": discover()}

    if kind == "update":
        return update()

    if kind == "change_pin":
        new = str(a.get("new", ""))
        if not (new.isdigit() and 4 <= len(new) <= 8):
            return {"error": "PIN must be 4-8 digits"}
        salt = secrets.token_hex(8)
        with LOCK:
            S["pin"] = {"salt": salt, "hash": hash_pin(new, salt)}
        save(force=True)
        return {"ok": True}

    if kind == "add_tv":
        if not ip:
            return {"error": "Type the TV's address first"}
        try:
            info = device_info(ip)
        except Exception:
            return {"error": "The Pi can't reach a Roku at %s. Check the address and that the TV is on." % ip}
        with LOCK:
            if find_tv(ip) is None:
                S["tvs"].append(new_tv(ip, info["name"]))
        save(force=True)
        sync_watchers()
        try:
            refresh_apps(ip)
        except Exception as e:
            return {"ok": True, "warning": "Added, but couldn't load its app list: " + why(e)}
        return {"ok": True}

    with LOCK:
        tv = find_tv(ip)
        if tv is None:
            return {"error": "Pick a TV first"}
        now = time.time()
        if kind == "remove_tv":
            S["tvs"] = [t for t in S["tvs"] if t["ip"] != ip]
        elif kind == "rename":
            tv["label"] = " ".join(str(a.get("label", "")).split())[:30]
        elif kind == "settings":
            for k in ("limit_on", "bed_on"):
                if k in a:
                    tv[k] = bool(a[k])
            for k in ("limit_weekday", "limit_weekend"):
                if k in a:
                    tv[k] = max(0, min(1440, int(a[k])))
            for k in ("bed_start", "bed_end"):
                if k in a and valid_time(a[k]):
                    tv[k] = a[k]
        elif kind == "bonus":
            tv["bonus"][today()] = max(0, tv["bonus"].get(today(), 0) + int(a.get("minutes", 0)))
        elif kind == "pause":
            tv["pause_until"] = now + max(1, min(1440, int(a.get("minutes", 60)))) * 60
            note(ip, "Rules paused by parent")
        elif kind == "resume":
            tv["pause_until"] = 0
            tv["unlock_until"] = {}
            note(ip, "Rules back on")
        elif kind == "lock":
            tv["tv_locked"] = True
            note(ip, "TV locked by parent")
        elif kind == "unlock_tv":
            tv["tv_locked"] = False
            note(ip, "TV unlocked by parent")
        elif kind == "block":
            app = str(a.get("app", ""))
            tv["blocked"] = [x for x in tv["blocked"] if x != app]
            if a.get("on"):
                tv["blocked"].append(app)
            tv["unlock_until"].pop(app, None)
        elif kind == "unlock":
            tv["unlock_until"][str(a.get("app", ""))] = now + max(1, min(1440, int(a.get("minutes", 30)))) * 60
        elif kind == "relock":
            tv["unlock_until"].pop(str(a.get("app", "")), None)
        elif kind == "reset_today":
            tv["usage"].pop(today(), None)
            tv["bonus"].pop(today(), None)
        elif kind == "tv_off":
            pass
        else:
            return {"error": "unknown action"}
        _dirty = True
    save(force=True)
    if kind == "remove_tv":
        sync_watchers()
    if kind in ("lock", "tv_off"):
        L = live(ip)
        if L["reachable"] and L["on"]:
            err = tv_off(ip, L.get("is_tv", True))
            if err:
                note(ip, "Couldn't turn the TV off: " + err)
                return {"error": "Couldn't turn the TV off: " + err}
            if kind == "tv_off":
                note(ip, "Turned off by parent")
    return {"ok": True}


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *args):
        pass

    def send_json(self, obj, code=200):
        body = json.dumps(obj).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def authed(self):
        return pin_ok(self.headers.get("X-Pin", ""))

    def do_GET(self):
        if self.path in ("/", "/index.html"):
            body = PAGE.encode()
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(body)
        elif self.path == "/api/state":
            if not S["pin"]:
                self.send_json({"setup": True})
            elif not self.authed():
                self.send_json({"error": "pin"}, 401)
            else:
                self.send_json(state())
        else:
            self.send_json({"error": "not found"}, 404)

    def do_POST(self):
        try:
            n = int(self.headers.get("Content-Length", 0))
            data = json.loads(self.rfile.read(min(n, 65536)) or b"{}")
        except ValueError:
            return self.send_json({"error": "bad request"}, 400)
        if self.path != "/api/action":
            return self.send_json({"error": "not found"}, 404)
        first_run = not S["pin"] and data.get("type") == "change_pin"
        if not first_run and not self.authed():
            return self.send_json({"error": "pin"}, 401)
        try:
            self.send_json(do_action(data))
        except (ValueError, TypeError):
            self.send_json({"error": "bad value"}, 400)


PAGE = r"""<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="theme-color" content="#14121f">
<title>Roku Screen Time</title>
<style>
:root{--bg:#14121f;--card:#1e1b2e;--line:#2f2b45;--ink:#f3f1fa;--dim:#9c97b8;--go:#7be0a4;--warn:#ffc65c;--stop:#ff7a7a;--pop:#a48bff}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--ink);font:16px/1.4 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;padding:16px 14px 60px;max-width:560px;margin:auto}
h1{font-size:22px;margin:4px 0 14px;letter-spacing:-.3px}
h2{font-size:13px;text-transform:uppercase;letter-spacing:1.2px;color:var(--dim);margin:0 0 10px}
.card{background:var(--card);border:1px solid var(--line);border-radius:16px;padding:16px;margin-bottom:14px}
.row{display:flex;align-items:center;justify-content:space-between;gap:10px;padding:8px 0}
.row+.row{border-top:1px solid var(--line)}
.big{font-size:40px;font-weight:700;letter-spacing:-1px;line-height:1}
.dim{color:var(--dim);font-size:14px}
.warn{color:var(--warn);font-size:14px;margin-top:6px}
.bar{height:10px;background:var(--line);border-radius:6px;overflow:hidden;margin:12px 0 6px}
.bar i{display:block;height:100%;background:var(--go);border-radius:6px;transition:width .4s}
.pill{display:inline-block;padding:3px 10px;border-radius:20px;font-size:13px;font-weight:600;background:var(--line)}
.pill.go{background:#1d3b2c;color:var(--go)}.pill.warn{background:#3d3219;color:var(--warn);margin:0}.pill.stop{background:#402024;color:var(--stop)}
button{font:inherit;font-weight:600;color:var(--ink);background:var(--line);border:0;border-radius:11px;padding:10px 14px;cursor:pointer}
button:active{transform:scale(.97)}
button.pop{background:var(--pop);color:#14121f}button.stop{background:#402024;color:var(--stop)}
button.sm{padding:6px 10px;font-size:13px}
button.lk{min-width:96px;padding:14px 12px;font-size:16px;flex:none}
.btns{display:flex;flex-wrap:wrap;gap:8px;margin-top:12px}
input[type=number],input[type=time],input[type=text],input[type=password]{font:inherit;color:var(--ink);background:var(--bg);border:1px solid var(--line);border-radius:10px;padding:8px 10px;width:110px;text-align:center}
input.wide{width:100%;text-align:left}
.sw{position:relative;width:50px;height:30px;flex:none}
.sw input{opacity:0;width:100%;height:100%;margin:0;position:absolute;z-index:1;cursor:pointer}
.sw span{position:absolute;inset:0;background:var(--line);border-radius:30px;transition:.2s}
.sw span:before{content:"";position:absolute;width:24px;height:24px;left:3px;top:3px;background:#fff;border-radius:50%;transition:.2s}
.sw input:checked+span{background:var(--pop)}.sw input:checked+span:before{transform:translateX(20px)}
.app{flex:1;min-width:0}.app b{display:block;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;font-weight:600}
.tv{cursor:pointer;border-radius:12px;padding:10px;margin:0 -10px}
.tv.sel{background:#272341}
.tv+.tv{border-top:0}
#msg{color:var(--stop);min-height:20px;font-size:14px;margin-top:8px}
.hide{display:none}
</style></head><body>
<h1>Roku Screen Time</h1>

<div id="gate" class="card hide">
  <h2 id="gateTitle">Parent PIN</h2>
  <p class="dim" id="gateHelp"></p>
  <input id="pin" class="wide" type="password" inputmode="numeric" maxlength="8" placeholder="PIN">
  <div class="btns"><button class="pop" id="pinGo">Continue</button></div>
  <div id="msg"></div>
</div>

<div id="main" class="hide">
  <div class="card">
    <h2>TVs</h2>
    <div id="tvs"></div>
    <div class="dim" id="tvHint"></div>
    <div class="btns"><button class="sm" id="addToggle">Add a TV</button></div>
    <div id="addBox" class="hide">
      <div class="btns"><button id="scan">Find my Rokus</button></div>
      <div id="found"></div>
      <div class="row" style="border:0"><input id="ip" class="wide" type="text" inputmode="decimal" placeholder="or type the TV's IP address"><button id="ipGo">Add</button></div>
      <div class="dim" id="addMsg"></div>
    </div>
  </div>

  <div id="detail" class="hide">
  <div class="card">
    <h2 id="dName">Today</h2>
    <div class="warn" id="tvWarn"></div>
    <div class="row" style="padding-top:0;border:0"><div><div class="big" id="left">--</div><div class="dim" id="leftSub"></div></div><span class="pill" id="status"></span></div>
    <div class="bar"><i id="fill" style="width:0"></i></div>
    <div class="dim" id="watching"></div>
    <div class="dim" id="last"></div>
    <div class="btns">
      <button data-a='{"type":"bonus","minutes":15}'>+15 min</button>
      <button data-a='{"type":"bonus","minutes":30}'>+30 min</button>
      <button id="pauseBtn" class="pop">Pause rules 1 hr</button>
      <button class="stop" data-a='{"type":"tv_off"}'>TV off now</button>
    </div>
  </div>

  <div class="card">
    <h2>TV name</h2>
    <div class="row" style="padding:0;border:0"><input id="label" class="wide" type="text" maxlength="30" placeholder="e.g. Kids Den"><button id="labelGo">Save</button></div>
    <div class="dim" id="model" style="margin-top:6px"></div>
  </div>

  <div class="card">
    <h2>Daily limit</h2>
    <div class="row"><span>Limit on</span><label class="sw"><input type="checkbox" id="limit_on"><span></span></label></div>
    <div class="row"><span>Mon-Fri minutes</span><input type="number" id="limit_weekday" min="0" max="1440" inputmode="numeric"></div>
    <div class="row"><span>Sat-Sun minutes</span><input type="number" id="limit_weekend" min="0" max="1440" inputmode="numeric"></div>
  </div>

  <div class="card">
    <h2>Bedtime lockout</h2>
    <div class="row"><span>Lockout on</span><label class="sw"><input type="checkbox" id="bed_on"><span></span></label></div>
    <div class="row"><span>TV off at</span><input type="time" id="bed_start"></div>
    <div class="row"><span>Allowed again at</span><input type="time" id="bed_end"></div>
  </div>

  <div class="card">
    <h2>Apps</h2>
    <div class="dim">Flip the switch to block an app. Blocked apps get an Allow button for when you want to watch.</div>
    <div id="apps" style="margin-top:8px"></div>
  </div>

  <div class="card">
    <h2>Watched today</h2>
    <div id="usage" class="dim">Nothing yet</div>
    <div class="btns"><button class="sm" data-a='{"type":"reset_today"}'>Reset today</button><button class="sm stop" id="removeBtn">Remove this TV</button></div>
  </div>
  </div>

  <div class="card">
    <h2>App</h2>
    <div class="btns" style="margin-top:0"><button id="updBtn">Get update and restart</button></div>
    <div class="dim" id="updMsg" style="margin-top:8px"></div>
  </div>
</div>

<script>
var updBusy=false,$=function(i){return document.getElementById(i)},pin="",setup=false,sel="",filledFor="",cur=null,removeArmed=0;
try{pin=localStorage.getItem("stpin")||"";sel=localStorage.getItem("sttv")||""}catch(e){}
function api(path,body){
  return fetch(path,{method:body?"POST":"GET",headers:{"Content-Type":"application/json","X-Pin":pin},body:body?JSON.stringify(body):undefined})
    .then(function(r){return r.json().then(function(j){j._status=r.status;return j})});
}
function act(a,tv){a.tv=tv||a.tv||sel;return api("/api/action",a).then(function(j){refresh();if(j.error&&a.tv==sel){$("last").textContent=j.error}return j})}
function mins(s){var m=Math.round(s/60);return m>=60?Math.floor(m/60)+"h "+(m%60)+"m":m+"m"}
function clock(ts){return new Date(ts*1000).toLocaleTimeString([], {hour:"numeric",minute:"2-digit"})}
function el(tag,cls,text){var e=document.createElement(tag);if(cls)e.className=cls;if(text!=null)e.textContent=text;return e}
function pick(ip){sel=ip;try{localStorage.setItem("sttv",ip)}catch(e){}refresh()}

function showGate(isSetup,err){
  setup=isSetup;$("main").classList.add("hide");$("gate").classList.remove("hide");
  $("gateTitle").textContent=isSetup?"Create a parent PIN":"Parent PIN";
  $("gateHelp").textContent=isSetup?"Pick 4-8 digits. You'll need it to change limits, so don't share it with the kids.":"Enter your PIN to manage screen time.";
  $("msg").textContent=err||"";
}
$("pinGo").onclick=function(){
  var v=$("pin").value.trim();
  if(setup){
    fetch("/api/action",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({type:"change_pin","new":v})})
      .then(function(r){return r.json()}).then(function(j){if(j.error){$("msg").textContent=j.error}else{keep(v);refresh()}});
  }else{keep(v);refresh(true)}
};
function keep(v){pin=v;try{localStorage.setItem("stpin",v)}catch(e){}}

function refresh(fromGate){
  api("/api/state").then(function(s){
    if(s.setup)return showGate(true);
    if(s._status==401)return showGate(false,fromGate?"Wrong PIN (5 misses locks it for a minute).":"");
    $("gate").classList.add("hide");$("main").classList.remove("hide");render(s);
  }).catch(function(){$("tvHint").textContent="Can't reach the Pi right now."});
}

function tvStatus(t){
  var L=t.live;
  if(!L.reachable)return "Off or not reachable";
  if(!L.on)return "TV is off";
  return L.app_id?("Now on: "+L.app_name+(L.screensaver?" (screensaver)":"")):"On the Home screen";
}

function render(s){
  var tvs=s.tvs;
  if(!updBusy)$("updMsg").textContent="Version "+s.version;
  if(!tvs.some(function(t){return t.ip==sel}))sel=tvs.length?tvs[0].ip:"";
  var box=$("tvs");box.textContent="";
  tvs.forEach(function(t){
    var row=el("div","row tv"+(t.ip==sel&&tvs.length>1?" sel":"")),info=el("div","app");
    info.appendChild(el("b",null,t.name));
    info.appendChild(el("span","dim",(t.tv_locked?"Locked. ":"")+tvStatus(t)));
    row.appendChild(info);
    var b=el("button","lk "+(t.tv_locked?"pop":"stop"),t.tv_locked?"Unlock":"Lock");
    b.onclick=function(e){e.stopPropagation();act({type:t.tv_locked?"unlock_tv":"lock"},t.ip)};
    row.appendChild(b);
    row.onclick=function(){pick(t.ip)};
    box.appendChild(row);
  });
  $("tvHint").textContent=tvs.length?(tvs.length>1?"Tap a TV to see its limits below.":""):"No TVs yet. Add one to get started.";
  if(!tvs.length)$("addBox").classList.remove("hide");
  cur=tvs.filter(function(t){return t.ip==sel})[0]||null;
  $("detail").classList.toggle("hide",!cur);
  if(!cur)return;
  var t=cur,L=t.live;
  $("dName").textContent=t.name+" - today";
  $("tvWarn").textContent=(L.reachable&&(L.ecp_mode=="limited"||L.ecp_mode=="disabled"))?"This TV is set to block control ("+L.ecp_mode+" mode), so it can be watched but not locked. On the TV: Settings > System > Advanced system settings > Control by mobile apps > Network access > Enabled.":"";
  var left=t.limit_today*60-t.used_seconds;
  $("left").textContent=t.limit_on?(left>0?mins(left):"0m"):mins(t.used_seconds);
  $("leftSub").textContent=t.limit_on?("left of "+mins(t.limit_today*60)+(t.bonus_today?" (incl. +"+t.bonus_today+" bonus)":"")):"watched today (no limit set)";
  var pct=t.limit_on&&t.limit_today?Math.min(100,100*t.used_seconds/(t.limit_today*60)):0;
  $("fill").style.width=pct+"%";$("fill").style.background=pct>=100?"var(--stop)":pct>=80?"var(--warn)":"var(--go)";
  var st=$("status");
  if(t.tv_locked){st.className="pill stop";st.textContent="Locked"}
  else if(t.pause_until){st.className="pill warn";st.textContent="Paused till "+clock(t.pause_until)}
  else if(t.bedtime_now){st.className="pill stop";st.textContent="Bedtime"}
  else if(t.limit_on&&left<=0){st.className="pill stop";st.textContent="Time's up"}
  else{st.className="pill go";st.textContent="Allowed"}
  $("model").textContent=t.model?("Roku calls it: "+t.model):"";
  $("pauseBtn").textContent=t.pause_until?"Resume rules":"Pause rules 1 hr";
  $("watching").textContent=tvStatus(t)+" ("+t.ip+")";
  $("last").textContent=L.last_action?("Last: "+L.last_action):"";
  if(filledFor!=t.ip){
    ["limit_on","bed_on"].forEach(function(k){$(k).checked=t[k]});
    ["limit_weekday","limit_weekend","bed_start","bed_end"].forEach(function(k){$(k).value=t[k]});
    $("label").value=t.label;
    filledFor=t.ip;removeArmed=0;$("removeBtn").textContent="Remove this TV";
  }
  var ab=$("apps");ab.textContent="";
  if(!t.apps.length)ab.appendChild(el("div","dim","Apps show up once the TV is on and allows control."));
  t.apps.forEach(function(a){
    var row=el("div","row"),info=el("div","app");info.appendChild(el("b",null,a.name));
    if(a.blocked){
      info.appendChild(el("span","dim",a.unlock_until?"Allowed till "+clock(a.unlock_until):"Blocked"));
      var b=el("button","sm",a.unlock_until?"Re-lock":"Allow 1 hr");
      b.onclick=function(){act(a.unlock_until?{type:"relock",app:a.id}:{type:"unlock",app:a.id,minutes:60})};
      row.appendChild(info);row.appendChild(b);
    }else row.appendChild(info);
    var sw=el("label","sw"),cb=el("input");cb.type="checkbox";cb.checked=a.blocked;
    cb.onchange=function(){act({type:"block",app:a.id,on:cb.checked})};
    sw.appendChild(cb);sw.appendChild(el("span"));row.appendChild(sw);ab.appendChild(row);
  });
  var u=$("usage");u.textContent=t.usage.length?"":"Nothing yet";
  t.usage.forEach(function(x){var r=el("div","row");r.appendChild(el("span",null,x.name));r.appendChild(el("span","dim",mins(x.seconds)));u.appendChild(r)});
}

document.addEventListener("click",function(e){var a=e.target.getAttribute&&e.target.getAttribute("data-a");if(a)act(JSON.parse(a))});
$("pauseBtn").onclick=function(){act(cur&&cur.pause_until?{type:"resume"}:{type:"pause",minutes:60})};
$("removeBtn").onclick=function(){
  if(Date.now()-removeArmed<4000){removeArmed=0;act({type:"remove_tv"})}
  else{removeArmed=Date.now();this.textContent="Tap again to remove"}
};
["limit_on","bed_on","limit_weekday","limit_weekend","bed_start","bed_end"].forEach(function(k){
  $(k).onchange=function(){var o={type:"settings"};o[k]=this.type=="checkbox"?this.checked:this.type=="number"?parseInt(this.value||"0",10):this.value;act(o)};
});
$("labelGo").onclick=function(){act({type:"rename",label:$("label").value});$("label").blur()};
$("label").onkeydown=function(e){if(e.key=="Enter")$("labelGo").onclick()};
$("updBtn").onclick=function(){
  updBusy=true;$("updMsg").textContent="Checking for an update...";
  api("/api/action",{type:"update"}).then(function(j){
    $("updMsg").textContent=j.error||j.message||"";
    if(j.restarting){setTimeout(function(){location.reload()},7000)}else{setTimeout(function(){updBusy=false},6000)}
  }).catch(function(){$("updMsg").textContent="Couldn't reach the Pi.";updBusy=false});
};
$("addToggle").onclick=function(){$("addBox").classList.toggle("hide")};
function addTv(ip){
  $("addMsg").textContent="Adding...";
  api("/api/action",{type:"add_tv",tv:ip}).then(function(j){
    $("addMsg").textContent=j.error||j.warning||"Added.";
    if(!j.error){$("ip").value="";pick(ip);$("found").textContent=""}
  });
}
$("scan").onclick=function(){
  var f=$("found");f.textContent="Searching...";
  api("/api/action",{type:"discover"}).then(function(j){
    var list=(j.found||[]).filter(function(d){return !d.added});
    f.textContent=list.length?"":((j.found||[]).length?"No new Rokus found. The ones that answered are already added.":"No Roku answered. Make sure the TV is on, or type its IP address.");
    list.forEach(function(d){var r=el("div","row");r.appendChild(el("span",null,d.name+" - "+d.ip));var b=el("button","sm pop","Add");
      b.onclick=function(){addTv(d.ip)};r.appendChild(b);f.appendChild(r)});
  });
};
$("ipGo").onclick=function(){if($("ip").value.trim())addTv($("ip").value.trim())};
refresh();setInterval(refresh,5000);
</script></body></html>
"""


# ---------------------------------------------------------------- main
def install():
    if os.geteuid() != 0:
        sys.exit("Run it like this:  sudo python3 %s --install" % os.path.abspath(__file__))
    user = os.environ.get("SUDO_USER") or "pi"
    unit = """[Unit]
Description=Roku Screen Time
After=network-online.target
Wants=network-online.target

[Service]
User=%s
ExecStart=/usr/bin/python3 %s
Restart=always
RestartSec=5

[Install]
WantedBy=multi-user.target
""" % (user, os.path.abspath(__file__))
    with open("/etc/systemd/system/roku-screentime.service", "w") as f:
        f.write(unit)
    subprocess.run(["systemctl", "daemon-reload"], check=True)
    subprocess.run(["systemctl", "enable", "--now", "roku-screentime"], check=True)
    print("Installed. It now starts on every boot.")
    print("Open  http://%s.local:%d  on your phone." % (socket.gethostname(), PORT))


VERSION = version()  # the copy that is actually running


def main():
    if "--install" in sys.argv:
        return install()
    load()
    sync_watchers()
    threading.Thread(target=housekeeping, daemon=True).start()
    print("Roku Screen Time running: http://%s.local:%d" % (socket.gethostname(), PORT), flush=True)
    try:
        ThreadingHTTPServer(("0.0.0.0", PORT), Handler).serve_forever()
    except KeyboardInterrupt:
        save(force=True)


if __name__ == "__main__":
    main()
