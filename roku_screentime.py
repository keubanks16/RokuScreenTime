#!/usr/bin/env python3
"""
Roku Screen Time
================
Runs on a Raspberry Pi (or any always-on computer) on the same WiFi as a Roku TV.
It watches what the TV is doing and enforces:
  * a daily time limit (separate weekday / weekend minutes)
  * blocked apps (a parent can unlock any of them for a while)
  * a bedtime lockout (TV is switched off during set hours)
The control panel is a web page served by this script: http://<pi-name>.local:8080

No extra packages needed - Python 3 standard library only.

  python3 roku_screentime.py             run it
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
POLL_SECONDS = 5
KEEP_DAYS = 14

DEFAULTS = {
    "pin": None,
    "roku_ip": "",
    "limit_on": True,
    "limit_weekday": 120,
    "limit_weekend": 180,
    "bed_on": True,
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

LOCK = threading.RLock()
S = dict(DEFAULTS)
LIVE = {"reachable": False, "on": False, "app_id": None, "app_name": "", "tv_name": "",
        "is_tv": True, "last_action": "", "screensaver": False}
_dirty = False
_last_save = 0.0
_pin_fails = {"count": 0, "until": 0.0}


# ---------------------------------------------------------------- storage
def load():
    global S
    try:
        with open(DATA) as f:
            saved = json.load(f)
        merged = dict(DEFAULTS)
        merged.update(saved)
        S = merged
    except (OSError, ValueError):
        S = json.loads(json.dumps(DEFAULTS))


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
    }


def active_app(ip):
    root = ET.fromstring(ecp(ip, "query/active-app"))
    app = root.find("app")
    app_id = app.get("id") if app is not None else None
    name = (app.text or "").strip() if app is not None else ""
    return app_id, name, root.find("screensaver") is not None


def installed_apps(ip):
    root = ET.fromstring(ecp(ip, "query/apps"))
    return {a.get("id"): (a.text or "").strip() for a in root.findall("app") if a.get("id")}


def discover(wait=3):
    """Find Rokus on the network with SSDP."""
    msg = ("M-SEARCH * HTTP/1.1\r\nHost: 239.255.255.250:1900\r\n"
           'Man: "ssdp:discover"\r\nST: roku:ecp\r\nMX: 2\r\n\r\n').encode()
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.settimeout(wait)
    found = []
    try:
        sock.sendto(msg, ("239.255.255.250", 1900))
        sock.sendto(msg, ("239.255.255.250", 1900))
        end = time.time() + wait
        while time.time() < end:
            try:
                data, addr = sock.recvfrom(2048)
            except socket.timeout:
                break
            if b"roku" in data.lower() and addr[0] not in found:
                found.append(addr[0])
    except OSError:
        pass
    finally:
        sock.close()
    out = []
    for ip in found:
        try:
            out.append({"ip": ip, "name": device_info(ip)["name"]})
        except Exception:
            out.append({"ip": ip, "name": ip})
    return out


# ---------------------------------------------------------------- rules
def limit_minutes_today():
    weekend = datetime.now().weekday() >= 5
    base = S["limit_weekend"] if weekend else S["limit_weekday"]
    return int(base) + int(S["bonus"].get(today(), 0))


def used_seconds_today():
    return sum(S["usage"].get(today(), {}).values())


def in_bedtime(now=None):
    now = now or datetime.now()
    try:
        sh, sm = [int(x) for x in S["bed_start"].split(":")]
        eh, em = [int(x) for x in S["bed_end"].split(":")]
    except ValueError:
        return False
    cur, start, end = now.hour * 60 + now.minute, sh * 60 + sm, eh * 60 + em
    if start == end:
        return False
    if start < end:
        return start <= cur < end
    return cur >= start or cur < end


def why(e):
    code = getattr(e, "code", None)
    if code in (401, 403):
        return ("the TV refused it (error %d). On the TV set Settings > System > Advanced system "
                "settings > Control by mobile apps > Network access to Permissive" % code)
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


def note(text):
    LIVE["last_action"] = "%s - %s" % (datetime.now().strftime("%-I:%M %p"), text)


def tick(dt):
    global _dirty
    ip = S["roku_ip"]
    if not ip:
        LIVE.update(reachable=False, on=False, app_id=None, app_name="")
        return
    try:
        info = device_info(ip)
        app_id, app_name, saver = active_app(ip)
    except Exception:
        LIVE.update(reachable=False, on=False, app_id=None, app_name="")
        return

    on = info["power"] == "PowerOn"
    with LOCK:
        LIVE.update(reachable=True, on=on, app_id=app_id, app_name=app_name,
                    tv_name=info["name"], is_tv=info["is_tv"], screensaver=saver)
        now = time.time()
        if app_id and app_name and S["apps"].get(app_id) != app_name:
            S["apps"][app_id] = app_name
            _dirty = True

        if on and app_id and not saver:
            day = S["usage"].setdefault(today(), {})
            day[app_id] = day.get(app_id, 0) + dt
            _dirty = True

        if not on:
            return
        if S["tv_locked"]:
            action = ("off", "TV is locked - turned it off")
        elif S["pause_until"] > now:
            return
        elif S["bed_on"] and in_bedtime():
            action = ("off", "Bedtime - turned the TV off")
        elif S["limit_on"] and app_id and used_seconds_today() >= limit_minutes_today() * 60:
            action = ("off", "Daily limit reached - turned the TV off")
        elif app_id in S["blocked"] and S["unlock_until"].get(app_id, 0) < now:
            action = ("home", "Blocked %s - sent the TV to Home" % (app_name or app_id))
        else:
            return

    err = tv_off(ip, info["is_tv"]) if action[0] == "off" else press(ip, "Home")
    note("Tried to enforce a rule but " + err if err else action[1])


def monitor():
    last = time.time()
    last_apps = 0.0
    last_day = today()
    while True:
        now = time.time()
        dt = min(now - last, POLL_SECONDS * 3)
        last = now
        try:
            tick(dt)
            if LIVE["reachable"] and now - last_apps > 300:
                last_apps = now
                try:
                    apps = installed_apps(S["roku_ip"])
                    with LOCK:
                        S["apps"].update(apps)
                    save(force=True)
                except Exception as e:
                    print("app list:", why(e), flush=True)
            if today() != last_day:
                last_day = today()
                cutoff = (datetime.now() - timedelta(days=KEEP_DAYS)).strftime("%Y-%m-%d")
                with LOCK:
                    for key in ("usage", "bonus"):
                        S[key] = {d: v for d, v in S[key].items() if d >= cutoff}
                save(force=True)
            save()
        except Exception as e:  # never let the watcher die
            print("monitor error:", e, flush=True)
        time.sleep(POLL_SECONDS)


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


def state():
    with LOCK:
        now = time.time()
        usage = S["usage"].get(today(), {})
        apps = [{"id": i, "name": n, "blocked": i in S["blocked"],
                 "unlock_until": S["unlock_until"].get(i, 0) if S["unlock_until"].get(i, 0) > now else 0}
                for i, n in S["apps"].items()]
        apps.sort(key=lambda a: (not a["blocked"], a["name"].lower()))
        return {
            "live": dict(LIVE),
            "roku_ip": S["roku_ip"],
            "limit_on": S["limit_on"], "limit_weekday": S["limit_weekday"],
            "limit_weekend": S["limit_weekend"],
            "bed_on": S["bed_on"], "bed_start": S["bed_start"], "bed_end": S["bed_end"],
            "bonus_today": S["bonus"].get(today(), 0),
            "limit_today": limit_minutes_today(),
            "used_seconds": int(used_seconds_today()),
            "bedtime_now": bool(S["bed_on"] and in_bedtime()),
            "pause_until": S["pause_until"] if S["pause_until"] > now else 0,
            "tv_locked": bool(S["tv_locked"]),
            "now": now,
            "apps": apps,
            "usage": sorted(
                [{"name": S["apps"].get(i, i), "seconds": int(s)} for i, s in usage.items()],
                key=lambda u: -u["seconds"]),
        }


def do_action(a):
    global _dirty
    kind = a.get("type")
    with LOCK:
        now = time.time()
        if kind == "settings":
            for k in ("limit_on", "bed_on"):
                if k in a:
                    S[k] = bool(a[k])
            for k in ("limit_weekday", "limit_weekend"):
                if k in a:
                    S[k] = max(0, min(1440, int(a[k])))
            for k in ("bed_start", "bed_end"):
                if k in a and valid_time(a[k]):
                    S[k] = a[k]
        elif kind == "bonus":
            S["bonus"][today()] = max(0, S["bonus"].get(today(), 0) + int(a.get("minutes", 0)))
        elif kind == "pause":
            S["pause_until"] = now + max(1, min(1440, int(a.get("minutes", 60)))) * 60
            note("Rules paused by parent")
        elif kind == "lock":
            S["tv_locked"] = True
            note("TV locked by parent")
        elif kind == "unlock_tv":
            S["tv_locked"] = False
            note("TV unlocked by parent")
        elif kind == "resume":
            S["pause_until"] = 0
            S["unlock_until"] = {}
            note("Rules back on")
        elif kind == "block":
            app = str(a.get("app", ""))
            S["blocked"] = [x for x in S["blocked"] if x != app]
            if a.get("on"):
                S["blocked"].append(app)
            S["unlock_until"].pop(app, None)
        elif kind == "unlock":
            S["unlock_until"][str(a.get("app", ""))] = now + max(1, min(1440, int(a.get("minutes", 30)))) * 60
        elif kind == "relock":
            S["unlock_until"].pop(str(a.get("app", "")), None)
        elif kind == "reset_today":
            S["usage"].pop(today(), None)
            S["bonus"].pop(today(), None)
        elif kind == "set_roku":
            S["roku_ip"] = str(a.get("ip", "")).strip()
            S["apps"] = {}
            LIVE.update(reachable=False, on=False, app_id=None, app_name="", tv_name="")
        elif kind == "change_pin":
            new = str(a.get("new", ""))
            if not (new.isdigit() and 4 <= len(new) <= 8):
                return {"error": "PIN must be 4-8 digits"}
            salt = secrets.token_hex(8)
            S["pin"] = {"salt": salt, "hash": hash_pin(new, salt)}
        elif kind == "tv_off":
            pass
        elif kind == "discover":
            pass
        else:
            return {"error": "unknown action"}
        _dirty = True
    save(force=True)
    if kind in ("lock", "tv_off") and S["roku_ip"]:
        err = tv_off(S["roku_ip"], LIVE.get("is_tv", True))
        if err:
            note("Couldn't turn the TV off: " + err)
            return {"error": "Couldn't turn the TV off: " + err}
        if kind == "tv_off":
            note("Turned off by parent")
    if kind == "discover":
        return {"found": discover()}
    if kind == "set_roku" and S["roku_ip"]:
        try:
            device_info(S["roku_ip"])
        except Exception:
            return {"error": "Saved, but the Pi can't reach a Roku at that address. The TV may be off or on a different network than the Pi."}
        try:
            apps = installed_apps(S["roku_ip"])
            with LOCK:
                S["apps"].update(apps)
            save(force=True)
        except Exception as e:
            return {"error": "Connected, but couldn't load the app list: " + why(e)}
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
.bar{height:10px;background:var(--line);border-radius:6px;overflow:hidden;margin:12px 0 6px}
.bar i{display:block;height:100%;background:var(--go);border-radius:6px;transition:width .4s}
.pill{display:inline-block;padding:3px 10px;border-radius:20px;font-size:13px;font-weight:600;background:var(--line)}
.pill.go{background:#1d3b2c;color:var(--go)}.pill.warn{background:#3d3219;color:var(--warn)}.pill.stop{background:#402024;color:var(--stop)}
button{font:inherit;font-weight:600;color:var(--ink);background:var(--line);border:0;border-radius:11px;padding:10px 14px;cursor:pointer}
button:active{transform:scale(.97)}
button.pop{background:var(--pop);color:#14121f}button.stop{background:#402024;color:var(--stop)}
button.sm{padding:6px 10px;font-size:13px}
.btns{display:flex;flex-wrap:wrap;gap:8px;margin-top:12px}
input[type=number],input[type=time],input[type=text],input[type=password]{font:inherit;color:var(--ink);background:var(--bg);border:1px solid var(--line);border-radius:10px;padding:8px 10px;width:110px;text-align:center}
input.wide{width:100%;text-align:left}
.sw{position:relative;width:50px;height:30px;flex:none}
.sw input{opacity:0;width:100%;height:100%;margin:0;position:absolute;z-index:1;cursor:pointer}
.sw span{position:absolute;inset:0;background:var(--line);border-radius:30px;transition:.2s}
.sw span:before{content:"";position:absolute;width:24px;height:24px;left:3px;top:3px;background:#fff;border-radius:50%;transition:.2s}
.sw input:checked+span{background:var(--pop)}.sw input:checked+span:before{transform:translateX(20px)}
.app{flex:1;min-width:0}.app b{display:block;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;font-weight:600}
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
  <div class="card" id="find">
    <h2>Your Roku TV</h2>
    <div id="tvLine" class="dim"></div>
    <div class="btns"><button id="scan">Find my Roku</button></div>
    <div id="found"></div>
    <div class="row" style="border:0"><input id="ip" class="wide" type="text" placeholder="or type the TV's IP address"><button id="ipGo">Use</button></div>
  </div>

  <div class="card">
    <h2>Today</h2>
    <button id="lockBtn" class="stop" style="width:100%;padding:16px;font-size:18px;margin-bottom:14px">Lock TV</button>
    <div class="row" style="padding-top:0"><div><div class="big" id="left">--</div><div class="dim" id="leftSub"></div></div><span class="pill" id="status"></span></div>
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
    <div class="btns"><button class="sm" data-a='{"type":"reset_today"}'>Reset today</button></div>
  </div>
</div>

<script>
var $=function(i){return document.getElementById(i)},pin="",setup=false,filled=false,timer=null,lastState=null;
try{pin=localStorage.getItem("stpin")||""}catch(e){}
function api(path,body){
  return fetch(path,{method:body?"POST":"GET",headers:{"Content-Type":"application/json","X-Pin":pin},body:body?JSON.stringify(body):undefined})
    .then(function(r){return r.json().then(function(j){j._status=r.status;return j})});
}
function act(a){return api("/api/action",a).then(function(j){refresh();if(j.error&&a.type!="set_roku"){$("last").textContent=j.error}return j})}
function mins(s){var m=Math.round(s/60);return m>=60?Math.floor(m/60)+"h "+(m%60)+"m":m+"m"}
function clock(ts){return new Date(ts*1000).toLocaleTimeString([], {hour:"numeric",minute:"2-digit"})}
function el(tag,cls,text){var e=document.createElement(tag);if(cls)e.className=cls;if(text!=null)e.textContent=text;return e}

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
  }).catch(function(){$("watching").textContent="Can't reach the Pi right now."});
}

function render(s){
  lastState=s;var L=s.live;
  $("tvLine").textContent=s.roku_ip?(L.reachable?(L.tv_name+" ("+s.roku_ip+")"):"Can't reach the TV at "+s.roku_ip+" (it may be fully powered down)"):"No TV picked yet.";
  var left=s.limit_today*60-s.used_seconds;
  $("left").textContent=s.limit_on?(left>0?mins(left):"0m"):mins(s.used_seconds);
  $("leftSub").textContent=s.limit_on?("left of "+mins(s.limit_today*60)+(s.bonus_today?" (incl. +"+s.bonus_today+" bonus)":"")):"watched today (no limit)";
  var pct=s.limit_on&&s.limit_today?Math.min(100,100*s.used_seconds/(s.limit_today*60)):0;
  $("fill").style.width=pct+"%";$("fill").style.background=pct>=100?"var(--stop)":pct>=80?"var(--warn)":"var(--go)";
  var st=$("status");
  var lb=$("lockBtn");lb.textContent=s.tv_locked?"Unlock TV":"Lock TV";lb.className=s.tv_locked?"pop":"stop";
  if(s.tv_locked){st.className="pill stop";st.textContent="Locked"}
  else if(s.pause_until){st.className="pill warn";st.textContent="Paused till "+clock(s.pause_until)}
  else if(s.bedtime_now){st.className="pill stop";st.textContent="Bedtime"}
  else if(s.limit_on&&left<=0){st.className="pill stop";st.textContent="Time's up"}
  else{st.className="pill go";st.textContent="Allowed"}
  $("pauseBtn").textContent=s.pause_until?"Resume rules":"Pause rules 1 hr";
  $("watching").textContent=!s.roku_ip?"":!L.reachable?"TV not reachable":!L.on?"TV is off":L.app_id?("Now on: "+L.app_name+(L.screensaver?" (screensaver)":"")):"On the Home screen";
  $("last").textContent=L.last_action?("Last: "+L.last_action):"";
  if(!filled){
    ["limit_on","bed_on"].forEach(function(k){$(k).checked=s[k]});
    ["limit_weekday","limit_weekend","bed_start","bed_end"].forEach(function(k){$(k).value=s[k]});
    filled=true;
  }
  var box=$("apps");box.textContent="";
  if(!s.apps.length)box.appendChild(el("div","dim",s.roku_ip?"Apps show up once the TV is reachable.":"Pick your TV first."));
  s.apps.forEach(function(a){
    var row=el("div","row"),info=el("div","app");info.appendChild(el("b",null,a.name));
    if(a.blocked){
      info.appendChild(el("span","dim",a.unlock_until?"Allowed till "+clock(a.unlock_until):"Blocked"));
      var b=el("button","sm",a.unlock_until?"Re-lock":"Allow 1 hr");
      b.onclick=function(){act(a.unlock_until?{type:"relock",app:a.id}:{type:"unlock",app:a.id,minutes:60})};
      row.appendChild(info);row.appendChild(b);
    }else row.appendChild(info);
    var sw=el("label","sw"),cb=el("input");cb.type="checkbox";cb.checked=a.blocked;
    cb.onchange=function(){act({type:"block",app:a.id,on:cb.checked})};
    sw.appendChild(cb);sw.appendChild(el("span"));row.appendChild(sw);box.appendChild(row);
  });
  var u=$("usage");u.textContent=s.usage.length?"":"Nothing yet";
  s.usage.forEach(function(x){var r=el("div","row");r.appendChild(el("span",null,x.name));r.appendChild(el("span","dim",mins(x.seconds)));u.appendChild(r)});
}

document.addEventListener("click",function(e){var a=e.target.getAttribute&&e.target.getAttribute("data-a");if(a)act(JSON.parse(a))});
$("lockBtn").onclick=function(){act({type:lastState&&lastState.tv_locked?"unlock_tv":"lock"})};
$("pauseBtn").onclick=function(){act(lastState&&lastState.pause_until?{type:"resume"}:{type:"pause",minutes:60})};
["limit_on","bed_on","limit_weekday","limit_weekend","bed_start","bed_end"].forEach(function(k){
  $(k).onchange=function(){var o={type:"settings"};o[k]=this.type=="checkbox"?this.checked:this.type=="number"?parseInt(this.value||"0",10):this.value;act(o)};
});
$("scan").onclick=function(){
  var f=$("found");f.textContent="Searching...";
  api("/api/action",{type:"discover"}).then(function(j){
    f.textContent=(j.found&&j.found.length)?"":"No Roku answered. Make sure the TV is on, then try again or type its IP.";
    (j.found||[]).forEach(function(d){var r=el("div","row");r.appendChild(el("span",null,d.name+" - "+d.ip));var b=el("button","sm pop","Use");
      b.onclick=function(){pick(d.ip)};r.appendChild(b);f.appendChild(r)});
  });
};
function pick(ip){act({type:"set_roku",ip:ip}).then(function(j){$("found").textContent=j.error||"Saved."})}
$("ipGo").onclick=function(){if($("ip").value.trim())pick($("ip").value.trim())};
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


def main():
    if "--install" in sys.argv:
        return install()
    load()
    threading.Thread(target=monitor, daemon=True).start()
    print("Roku Screen Time running: http://%s.local:%d" % (socket.gethostname(), PORT), flush=True)
    try:
        ThreadingHTTPServer(("0.0.0.0", PORT), Handler).serve_forever()
    except KeyboardInterrupt:
        save(force=True)


if __name__ == "__main__":
    main()
