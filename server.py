#!/usr/bin/env python3
"""Close Call desk: a local-only web UI for the technocore close-1 contest."""
from __future__ import annotations

import base64
import json
import re
import secrets
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timedelta, timezone
from decimal import Decimal
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives.asymmetric.ed25519 import (
    Ed25519PrivateKey,
    Ed25519PublicKey,
)

HERE = Path(__file__).resolve().parent
STATE_FILE = HERE / "state.json"
INDEX_FILE = HERE / "index.html"

CHAT = "https://technocore.chat"
HL_INFO = "https://api.hyperliquid.xyz/info"
COIN = "xyz:NVDA"

SEASON = "close-1"
ROOM_RE = re.compile(r"^[a-z0-9][a-z0-9_-]{0,47}$")
DID_RE = re.compile(r"^did:key:z6Mk[1-9A-HJ-NP-Za-km-z]{44}$")
AMOUNT_RE = re.compile(r"^[0-9]{1,7}(\.[0-9]{1,2})?$")
TRADE_ID_RE = re.compile(r"^[A-Za-z0-9_-]{1,64}$")

OPENING = datetime(2026, 9, 25, 12, 0, tzinfo=timezone.utc)
FIRST_SWEEP = datetime(2026, 9, 25, 12, 5, tzinfo=timezone.utc)
LOCK = datetime(2026, 10, 4, 9, 0, tzinfo=timezone.utc)
FINAL_TIME = datetime(2026, 10, 4, 10, 0, tzinfo=timezone.utc)
SWEEP_SECONDS = 300
LOCK_SWEEP = 2556
MINT = "10000"
MIN_QTY = Decimal("0.1")
LIMIT_WINDOW = Decimal("0.05")
FEE_RATE = Decimal("0.01")

PRICE_ROOM = "d-close1-price"
FLOW_ROOM = "d-close1-flow"
PNL_ROOM = "d-close1-pnl"
POS_ROOM = "d-close1-positions"
STATE_ROOM = "d-close1-state"
DEFAULT_TRADE_ROOM = "close1"

B58_ALPH = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"

_state_lock = threading.Lock()
_hl_lock = threading.Lock()
_hl_cache: dict = {"t": 0.0, "data": None}
_read_counter = 0

_rooms_lock = threading.Lock()
_rooms_cache: dict = {"t": 0.0, "data": None, "rates": {}}
_seq_history: dict[str, tuple[int, float]] = {}
_flow_lock = threading.Lock()
_flow_cache: dict = {"t": 0.0, "settled": set(), "void": set(), "fresh": set(), "unlisted": set()}
_offers_lock = threading.Lock()
_offers_cache: dict[str, dict] = {}

DESK_RE = re.compile(r"(desk|offer|close|c1|nvda|cc[-0-9]|tclk|flop|flip|trade|pit|book)", re.IGNORECASE)


class ApiError(Exception):
    def __init__(self, message: str, code: int = 400):
        super().__init__(message)
        self.code = code


def b58encode(data: bytes) -> str:
    n = int.from_bytes(data, "big")
    out = ""
    while n:
        n, rem = divmod(n, 58)
        out = B58_ALPH[rem] + out
    pad = 0
    for byte in data:
        if byte == 0:
            pad += 1
        else:
            break
    return "1" * pad + out


def b58decode(text: str) -> bytes:
    n = 0
    for char in text:
        idx = B58_ALPH.find(char)
        if idx < 0:
            raise ValueError("bad base58")
        n = n * 58 + idx
    body = n.to_bytes((n.bit_length() + 7) // 8, "big") if n else b""
    pad = 0
    for char in text:
        if char == "1":
            pad += 1
        else:
            break
    return b"\x00" * pad + body


def canon(obj) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def compact(obj) -> str:
    return json.dumps(obj, separators=(",", ":"), ensure_ascii=False)


def sweep_line(text: str) -> str:
    cleaned = []
    for char in text:
        cp = ord(char)
        if cp < 0x20 or 0x7F <= cp <= 0x9F or 0x2028 <= cp <= 0x2029 or 0x200B <= cp <= 0x200F:
            cleaned.append(" ")
        elif 0xD800 <= cp <= 0xDFFF or 0xE000 <= cp <= 0xF8FF:
            cleaned.append(" ")
        else:
            cleaned.append(char)
    return "".join(cleaned).strip()


def load_state() -> dict:
    if STATE_FILE.exists():
        try:
            data = json.loads(STATE_FILE.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                data.setdefault("seed_hex", None)
                data.setdefault("did", None)
                data.setdefault("nonces", {})
                data.setdefault("log", [])
                return data
        except (OSError, ValueError):
            pass
    return {"seed_hex": None, "did": None, "nonces": {}, "log": []}


def save_state(state: dict) -> None:
    STATE_FILE.write_text(json.dumps(state, ensure_ascii=False, indent=1), encoding="utf-8")


def identity(seed_hex: str | None = None) -> tuple[str, str, Ed25519PrivateKey]:
    if seed_hex is None:
        seed = secrets.token_bytes(32)
    else:
        seed_hex = seed_hex.strip().lower()
        if not re.fullmatch(r"[0-9a-f]{64}", seed_hex):
            raise ApiError("seed باید 64 کاراکتر hex باشد")
        seed = bytes.fromhex(seed_hex)
    priv = Ed25519PrivateKey.from_private_bytes(seed)
    pub = priv.public_key().public_bytes_raw()
    did = "did:key:z" + b58encode(b"\xed\x01" + pub)
    if not DID_RE.match(did):
        raise ApiError("ساختار did:key نامعتبر است")
    return did, seed.hex(), priv


def public_key_from_did(did: str) -> Ed25519PublicKey:
    if not DID_RE.match(did):
        raise ApiError("did:key نامعتبر نیست")
    raw = b58decode(did[len("did:key:z"):])
    if len(raw) != 34 or raw[:2] != b"\xed\x01":
        raise ApiError("ساختار کلید نامعتبر است")
    return Ed25519PublicKey.from_public_bytes(raw[2:])


def sign(priv: Ed25519PrivateKey, message: str) -> str:
    sig = priv.sign(message.encode("utf-8"))
    return base64.urlsafe_b64encode(sig).decode("ascii").rstrip("=")


def verify_sig(did: str, sig: str, message: str) -> None:
    if not re.fullmatch(r"[A-Za-z0-9_-]{86}", sig):
        raise ApiError("امضا باید 86 کاراکتر base64url باشد")
    pad = "=" * (-len(sig) % 4)
    try:
        raw = base64.urlsafe_b64decode(sig + pad)
    except Exception as exc:
        raise ApiError(f"امضا قابل decode نیست: {exc}") from exc
    try:
        public_key_from_did(did).verify(raw, message.encode("utf-8"))
    except InvalidSignature as exc:
        raise ApiError("امضا نامعتبر است") from exc


def now_utc() -> datetime:
    return datetime.now(timezone.utc)


def current_sweep(dt: datetime | None = None) -> int:
    dt = dt or now_utc()
    if dt < FIRST_SWEEP:
        return 0
    n = int((dt - FIRST_SWEEP).total_seconds() // SWEEP_SECONDS) + 1
    return min(n, LOCK_SWEEP)


def next_sweep(dt: datetime | None = None) -> datetime:
    dt = dt or now_utc()
    if dt < FIRST_SWEEP:
        return FIRST_SWEEP
    steps = int((dt - FIRST_SWEEP).total_seconds() // SWEEP_SECONDS) + 1
    return FIRST_SWEEP + timedelta(seconds=steps * SWEEP_SECONDS)


def contest_payload(state: dict) -> dict:
    dt = now_utc()
    nxt = next_sweep(dt)
    return {
        "now": dt.isoformat().replace("+00:00", "Z"),
        "opening": OPENING.isoformat().replace("+00:00", "Z"),
        "lock": LOCK.isoformat().replace("+00:00", "Z"),
        "final_time": FINAL_TIME.isoformat().replace("+00:00", "Z"),
        "sweep": current_sweep(dt),
        "next_sweep": nxt.isoformat().replace("+00:00", "Z"),
        "next_sweep_in_s": max(0, int((nxt - dt).total_seconds())),
        "lock_in_s": max(0, int((LOCK - dt).total_seconds())),
        "locked": dt >= LOCK,
        "mint": MINT,
        "min_qty": "0.1",
        "price_step": "0.01",
        "qty_step": "0.01",
        "limit_window": "0.05",
        "fee_rate": "0.01",
        "lock_sweep": LOCK_SWEEP,
        "default_until": min(current_sweep(dt) + 2, LOCK_SWEEP),
        "did": state.get("did"),
        "default_room": DEFAULT_TRADE_ROOM,
    }


def log_event(state: dict, kind: str, detail: dict) -> None:
    state.setdefault("log", []).append({"ts": int(time.time()), "kind": kind, **detail})
    if len(state["log"]) > 500:
        del state["log"][: len(state["log"]) - 500]


def chat_read(room: str, since: int | None = None, limit: int = 50) -> tuple[int, object]:
    if not ROOM_RE.match(room):
        raise ApiError("نام اتاق نامعتبر است")
    global _read_counter
    _read_counter += 1
    params = {"format": "json", "limit": str(max(1, min(200, limit))), "n": str(_read_counter)}
    if since is not None:
        params["since"] = str(int(since))
    url = f"{CHAT}/r/{urllib.parse.quote(room)}?{urllib.parse.urlencode(params)}"
    try:
        with urllib.request.urlopen(url, timeout=20) as resp:
            body = resp.read().decode("utf-8", "replace")
            code = resp.status
    except urllib.error.HTTPError as exc:
        return exc.code, exc.read().decode("utf-8", "replace")
    except (urllib.error.URLError, TimeoutError) as exc:
        raise ApiError(f"اتصال به technocore.chat برقرار نشد: {exc}", 502) from exc
    try:
        return code, json.loads(body)
    except ValueError:
        return code, body


def chat_write(room: str, text: str, state: dict) -> dict:
    if not ROOM_RE.match(room):
        raise ApiError("نام اتاق نامعتبر است")
    text = sweep_line(text)
    if not text:
        raise ApiError("متن پیام خالی است")
    if len(text) > 4096:
        raise ApiError("متن پیام بیش از 4096 کاراکتر است")

    seed_hex = state.get("seed_hex")
    if not seed_hex:
        raise ApiError("اول یک کلید بسازید (تب راه‌اندازی)")
    did, _, priv = identity(seed_hex)

    max_seen = 0
    code_tail, tail = chat_read(room, limit=200)
    if code_tail == 200 and isinstance(tail, dict):
        for msg in tail.get("messages", []):
            if msg.get("from") == did and isinstance(msg.get("nonce"), int):
                max_seen = max(max_seen, msg["nonce"])

    stored = int(state.get("nonces", {}).get(room, 0) or 0)
    nonce = max(int(time.time() * 1000), max_seen + 1, stored + 1)
    if len(str(nonce)) > 19:
        raise ApiError("nonce بیش از 19 رقم است")

    sig = sign(priv, f"{room}|{nonce}|{text}")
    payload = {"did": did, "sig": sig, "nonce": str(nonce), "text": text}
    req = urllib.request.Request(
        f"{CHAT}/r/{urllib.parse.quote(room)}",
        data=json.dumps(payload, ensure_ascii=False).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:
            body = resp.read().decode("utf-8", "replace")
            status = resp.status
    except urllib.error.HTTPError as exc:
        body = exc.read().decode("utf-8", "replace")
        status = exc.code
    except (urllib.error.URLError, TimeoutError) as exc:
        raise ApiError(f"ارسال پیام ممکن نشد: {exc}", 502) from exc

    if 200 <= status < 300:
        state.setdefault("nonces", {})[room] = nonce
    return {"code": status, "body": body, "nonce": nonce, "did": did, "text": text, "sig": sig}


def chat_rooms() -> dict:
    with _rooms_lock:
        if time.time() - _rooms_cache["t"] < 60 and _rooms_cache["data"] is not None:
            return _rooms_cache["data"]
    url = f"{CHAT}/rooms?format=json&limit=200"
    try:
        with urllib.request.urlopen(url, timeout=20) as resp:
            data = json.loads(resp.read().decode("utf-8", "replace"))
    except (urllib.error.URLError, TimeoutError, ValueError) as exc:
        raise ApiError(f"فهرست اتاق‌ها در دسترس نیست: {exc}", 502) from exc
    nowt = time.time()
    rates: dict[str, float] = {}
    seen: set = set()
    for item in data.get("rooms", []) if isinstance(data, dict) else []:
        name = item.get("room") if isinstance(item, dict) else None
        seq = item.get("last_seq") if isinstance(item, dict) else None
        if not isinstance(name, str) or not isinstance(seq, int):
            continue
        seen.add(name)
        prev = _seq_history.get(name)
        if prev and nowt - prev[1] >= 15:
            delta = (seq - prev[0]) / ((nowt - prev[1]) / 60.0)
            if delta >= 0:
                rates[name] = round(min(delta, 10 ** 6), 2)
        _seq_history[name] = (seq, nowt)
    for old in [k for k in _seq_history if k not in seen]:
        _seq_history.pop(old, None)
    with _rooms_lock:
        _rooms_cache["t"] = time.time()
        _rooms_cache["data"] = data
        _rooms_cache["rates"] = rates
    return data


def flow_snapshot(ttl: float = 45.0) -> dict:
    with _flow_lock:
        if time.time() - _flow_cache["t"] < ttl and _flow_cache["t"]:
            return _flow_cache
    settled: set = set()
    void: set = set()
    fresh: set = set()
    unlisted: set = set()
    code, data = chat_read(FLOW_ROOM, limit=10)
    if code == 200 and isinstance(data, dict):
        for msg in data.get("messages", []):
            try:
                obj = json.loads(msg.get("text", ""))
            except (ValueError, TypeError):
                continue
            if obj.get("t") != "flow":
                continue
            settled.update(obj.get("settled") or [])
            fresh.update(obj.get("rooms") or [])
            for pair in obj.get("void") or []:
                if isinstance(pair, list) and pair:
                    void.add(pair[0])
            for name in obj.get("unlisted") or []:
                unlisted.add(name)
    with _flow_lock:
        _flow_cache.update({"t": time.time(), "settled": settled, "void": void,
                            "fresh": fresh, "unlisted": unlisted})
        return dict(_flow_cache)


def room_open_offers(room: str) -> dict:
    if not ROOM_RE.match(room):
        raise ApiError("نام اتاق نامعتبر است")
    with _offers_lock:
        entry = _offers_cache.get(room)
        if entry and time.time() - entry["t"] < 45:
            return entry["data"]
    code, data = chat_read(room, limit=100)
    if code != 200 or not isinstance(data, dict):
        raise ApiError(f"اتاق {room} خوانده نشد (کد {code})", 502)
    flow = flow_snapshot()
    offers = []
    seen_trades = 0
    for msg in data.get("messages", []):
        try:
            obj = json.loads(msg.get("text", ""))
        except (ValueError, TypeError):
            continue
        if obj.get("t") != "trade" or not isinstance(obj.get("terms"), dict):
            continue
        seen_trades += 1
        tid = obj["terms"].get("id")
        if not tid or obj.get("taker_sig"):
            continue
        if tid in flow["settled"] or tid in flow["void"]:
            continue
        offers.append({
            "id": tid,
            "seq": msg.get("seq"),
            "ts": msg.get("ts"),
            "from": msg.get("from"),
            "text": msg.get("text"),
            "terms": obj["terms"],
        })
    offers.sort(key=lambda item: -(item.get("seq") or 0))
    result = {
        "ok": True,
        "room": room,
        "count": len(offers),
        "seen_trades": seen_trades,
        "offers": offers,
        "fetched_at": now_utc().isoformat().replace("+00:00", "Z"),
    }
    with _offers_lock:
        _offers_cache[room] = {"t": time.time(), "data": result}
        if len(_offers_cache) > 40:
            for old in sorted(_offers_cache, key=lambda k: _offers_cache[k]["t"])[:10]:
                _offers_cache.pop(old, None)
    return result


def route_rooms(counts: bool = False) -> dict:
    data = chat_rooms()
    with _rooms_lock:
        rates = dict(_rooms_cache.get("rates") or {})
    flags = flow_snapshot()
    rows = []
    for item in data.get("rooms", []):
        if not isinstance(item, dict):
            continue
        name = item.get("room")
        if not isinstance(name, str):
            continue
        idle = item.get("idle_seconds")
        rows.append({
            "room": name,
            "msgs": item.get("last_seq"),
            "bytes": item.get("bytes"),
            "idle": idle,
            "window": item.get("window"),
            "topic": item.get("topic"),
            "rate": rates.get(name),
            "fresh": name in flags["fresh"],
            "unlisted": name in flags["unlisted"],
            "desk": bool(DESK_RE.search(name)) and not name.startswith("mb-pair") and name != "lobby",
            "offers_n": None,
        })

    def sort_key(r: dict):
        rate = r.get("rate")
        return (
            -(rate if isinstance(rate, (int, float)) else -1),
            r["idle"] if isinstance(r["idle"], int) else 10 ** 9,
            -(r["window"] or 0),
        )

    contest_rows = sorted((r for r in rows if r["desk"]), key=sort_key)
    other_rows = sorted((r for r in rows if not r["desk"]), key=sort_key)
    ordered = contest_rows[:40] + other_rows[:20]
    if counts:
        candidates = [r for r in contest_rows if not isinstance(r["idle"], int) or r["idle"] < 21600]
        if not any(r["room"] == DEFAULT_TRADE_ROOM for r in candidates[:8]):
            main = next((r for r in contest_rows if r["room"] == DEFAULT_TRADE_ROOM), None)
            if main is not None:
                candidates = [main] + [r for r in candidates if r["room"] != DEFAULT_TRADE_ROOM]
        for row in candidates[:8]:
            try:
                row["offers_n"] = room_open_offers(row["room"])["count"]
            except ApiError:
                row["offers_n"] = None
    return {
        "ok": True,
        "rooms": ordered[:60],
        "total": data.get("total"),
        "counts": counts,
        "fetched_at": now_utc().isoformat().replace("+00:00", "Z"),
    }


def hl_last() -> dict:
    with _hl_lock:
        if time.time() - _hl_cache["t"] < 5 and _hl_cache["data"] is not None:
            return _hl_cache["data"]
    start = int((time.time() - 1800) * 1000)
    end = int(time.time() * 1000)
    req_body = {"type": "candleSnapshot", "req": {"coin": COIN, "interval": "1m", "startTime": start, "endTime": end}}
    req = urllib.request.Request(
        HL_INFO,
        data=json.dumps(req_body).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=15) as resp:
            candles = json.loads(resp.read().decode("utf-8"))
    except (urllib.error.URLError, TimeoutError, ValueError) as exc:
        return {"ok": False, "error": str(exc)}
    if not candles:
        return {"ok": False, "error": "کندلی برای NVDA پیدا نشد"}
    last = candles[-1]
    data = {
        "ok": True,
        "px": last.get("c"),
        "open": last.get("o"),
        "high": last.get("h"),
        "low": last.get("l"),
        "volume": last.get("v"),
        "candle_start_ms": last.get("t"),
        "candle_end_ms": last.get("T"),
        "fetched_at": now_utc().isoformat().replace("+00:00", "Z"),
    }
    with _hl_lock:
        _hl_cache["t"] = time.time()
        _hl_cache["data"] = data
    return data


def require_key(state: dict):
    seed_hex = state.get("seed_hex")
    if not seed_hex:
        raise ApiError("اول یک کلید بسازید (تب راه‌اندازی)")
    did, _, priv = identity(seed_hex)
    return did, priv


def validate_amount(field: str, value, allow_zero: bool = False) -> str:
    text = str(value).strip()
    if not AMOUNT_RE.match(text):
        raise ApiError(f"{field} باید عددی با حداکثر دو رقم اعشار باشد")
    dec = Decimal(text)
    if dec <= 0 and not allow_zero:
        raise ApiError(f"{field} باید بزرگ‌تر از صفر باشد")
    return text


def build_terms(body: dict, maker: str) -> dict:
    side = body.get("side")
    if side not in ("buy", "sell"):
        raise ApiError("side باید buy یا sell باشد")
    qty = validate_amount("تعداد (qty)", body.get("qty"))
    if Decimal(qty) < MIN_QTY:
        raise ApiError("حداقل تعداد 0.1 است")
    px = validate_amount("قیمت (px)", body.get("px"))
    taker = body.get("taker") or "any"
    if taker != "any" and not DID_RE.match(str(taker)):
        raise ApiError("taker باید «any» یا یک did:key معتبر باشد")
    until = body.get("until")
    if type(until) is not int or until < 1:
        raise ApiError("until باید شماره sweep (عدد صحیح) باشد")
    return {
        "id": secrets.token_hex(4),
        "maker": maker,
        "px": px,
        "qty": qty,
        "side": side,
        "taker": taker,
        "until": until,
    }


def check_terms(terms) -> dict:
    if not isinstance(terms, dict):
        raise ApiError("terms یک object نیست")
    if not isinstance(terms.get("id"), str) or not TRADE_ID_RE.match(terms["id"]):
        raise ApiError("id نامعتبر است")
    if terms.get("side") not in ("buy", "sell"):
        raise ApiError("side نامعتبر است")
    maker = terms.get("maker")
    if not isinstance(maker, str) or not DID_RE.match(maker):
        raise ApiError("maker نامعتبر است")
    validate_amount("qty", terms.get("qty"))
    if Decimal(str(terms["qty"])) < MIN_QTY:
        raise ApiError("حداقل تعداد 0.1 است")
    validate_amount("px", terms.get("px"))
    taker = terms.get("taker")
    if taker != "any" and not (isinstance(taker, str) and DID_RE.match(taker)):
        raise ApiError("taker نامعتبر است")
    if type(terms.get("until")) is not int:
        raise ApiError("until نامعتبر است")
    return terms


def parse_offer(body: dict) -> tuple[dict, str]:
    terms, msig = body.get("terms"), body.get("maker_sig")
    if not msig and body.get("message"):
        message = body["message"]
        if isinstance(message, str):
            try:
                message = json.loads(message)
            except ValueError as exc:
                raise ApiError("متن پیشنهاد JSON معتبر نیست") from exc
        if not isinstance(message, dict):
            raise ApiError("پیشنهاد یک object نیست")
        terms = terms or message.get("terms")
        msig = msig or message.get("maker_sig")
    if not isinstance(terms, dict) or not isinstance(msig, str):
        raise ApiError("terms یا maker_sig پیدا نشد")
    check_terms(terms)
    verify_sig(terms["maker"], msig, f"{SEASON}|terms|{canon(terms)}")
    return terms, msig


def state_payload() -> dict:
    state = load_state()
    return {
        "ok": True,
        "did": state.get("did"),
        "seed_present": bool(state.get("seed_hex")),
        "nonces": state.get("nonces", {}),
        "log": list(reversed(state.get("log", [])))[:100],
        "contest": contest_payload(state),
    }


class Handler(BaseHTTPRequestHandler):
    server_version = "CloseCallDesk/1.0"

    def log_message(self, fmt, *args):
        print(f"[{datetime.now(timezone.utc).strftime('%H:%M:%S')}] {fmt % args}")

    def _send(self, code: int, body: bytes, ctype: str = "application/json; charset=utf-8") -> None:
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def _json(self, obj, code: int = 200) -> None:
        self._send(code, json.dumps(obj, ensure_ascii=False).encode("utf-8"))

    def _error(self, message: str, code: int = 400) -> None:
        self._json({"ok": False, "error": message}, code)

    def do_OPTIONS(self):
        self.send_response(204)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()

    def do_GET(self):
        split = urllib.parse.urlsplit(self.path)
        path = split.path
        query = urllib.parse.parse_qs(split.query)
        try:
            if path == "/":
                body = INDEX_FILE.read_bytes()
                self._send(200, body, "text/html; charset=utf-8")
            elif path == "/api/state":
                self._json(state_payload())
            elif path == "/api/hl":
                self._json(hl_last())
            elif path == "/api/rooms":
                counts = query.get("counts", ["0"])[0] in ("1", "true", "yes")
                self._json(route_rooms(counts))
            elif path == "/api/offers":
                room = query.get("room", [DEFAULT_TRADE_ROOM])[0] or DEFAULT_TRADE_ROOM
                self._json(room_open_offers(room))
            elif path.startswith("/api/room/"):
                room = urllib.parse.unquote(path[len("/api/room/"):])
                since = query.get("since", [None])[0]
                limit = int(query.get("limit", ["50"])[0] or 50)
                code, data = chat_read(room, int(since) if since not in (None, "") else None, limit)
                self._json({"ok": code == 200, "code": code, "data": data})
            else:
                self._error("پیدا نشد", 404)
        except ApiError as exc:
            self._error(str(exc), exc.code)
        except Exception as exc:  # noqa: BLE001 - local desk, report everything
            self._error(f"خطای داخلی: {exc}", 500)

    def do_POST(self):
        path = urllib.parse.urlsplit(self.path).path
        length = int(self.headers.get("Content-Length") or 0)
        if length > 262144:
            self._error("بدنه بیش از حد بزرگ است", 413)
            return
        raw = self.rfile.read(length) if length else b"{}"
        try:
            body = json.loads(raw.decode("utf-8") or "{}")
            if not isinstance(body, dict):
                raise ValueError("not an object")
        except ValueError as exc:
            self._error(f"بدنه JSON نامعتبر است: {exc}")
            return
        try:
            handler = ROUTES_POST.get(path)
            if handler is None:
                self._error("پیدا نشد", 404)
            else:
                result = handler(body)
                if isinstance(result, dict):
                    self._json(result)
        except ApiError as exc:
            self._error(str(exc), exc.code)
        except Exception as exc:  # noqa: BLE001
            self._error(f"خطای داخلی: {exc}", 500)


def route_key_new(body: dict) -> dict:
    did, seed_hex, _ = identity(None)
    with _state_lock:
        state = load_state()
        state["seed_hex"] = seed_hex
        state["did"] = did
        state["nonces"] = {}
        log_event(state, "key_new", {"did": did})
        save_state(state)
    return {"ok": True, "did": did, "seed_hex": seed_hex}


def route_key_import(body: dict) -> dict:
    did, seed_hex, _ = identity(body.get("seed_hex"))
    with _state_lock:
        state = load_state()
        state["seed_hex"] = seed_hex
        state["did"] = did
        log_event(state, "key_import", {"did": did})
        save_state(state)
    return {"ok": True, "did": did}


def route_key_export(body: dict) -> dict:
    state = load_state()
    if not state.get("seed_hex"):
        raise ApiError("کلیدی ذخیره نشده است")
    return {"ok": True, "did": state["did"], "seed_hex": state["seed_hex"]}


def route_register(body: dict) -> dict:
    room = str(body.get("room") or DEFAULT_TRADE_ROOM)
    with _state_lock:
        state = load_state()
        did, _ = require_key(state)
        text = compact({"t": "owner", "season": SEASON, "key": did})
        result = chat_write(room, text, state)
        log_event(state, "register", {"room": room, "code": result["code"], "did": did})
        save_state(state)
    return {"ok": 200 <= result["code"] < 300, **result}


def route_register_room(body: dict) -> dict:
    room_name = str(body.get("room") or "").strip()
    if not ROOM_RE.match(room_name):
        raise ApiError("نام اتاق نامعتبر است")
    post_room = str(body.get("post_room") or DEFAULT_TRADE_ROOM)
    with _state_lock:
        state = load_state()
        require_key(state)
        text = compact({"t": "room", "season": SEASON, "room": room_name})
        result = chat_write(post_room, text, state)
        log_event(state, "register_room", {"room": room_name, "code": result["code"]})
        save_state(state)
    return {"ok": 200 <= result["code"] < 300, **result}


def route_offer(body: dict) -> dict:
    room = str(body.get("room") or DEFAULT_TRADE_ROOM)
    with _state_lock:
        state = load_state()
        did, priv = require_key(state)
        if contest_payload(state)["locked"]:
            raise ApiError("مسابقه قفل شده (بعد از 4 اکتبر 09:00 UTC)")
        terms = build_terms(body, did)
        msig = sign(priv, f"{SEASON}|terms|{canon(terms)}")
        message = {"t": "trade", "season": SEASON, "terms": terms, "taker": terms["taker"], "maker_sig": msig}
        text = compact(message)
        result = chat_write(room, text, state)
        log_event(state, "offer", {"id": terms["id"], "room": room, "code": result["code"],
                                   "side": terms["side"], "qty": terms["qty"], "px": terms["px"]})
        save_state(state)
    return {"ok": 200 <= result["code"] < 300, "terms": terms, "maker_sig": msig, **result}


def route_inspect(body: dict) -> dict:
    terms, msig = parse_offer(body)
    return {
        "ok": True,
        "terms": terms,
        "maker_sig": msig,
        "summary": {
            "id": terms["id"],
            "side": terms["side"],
            "qty": terms["qty"],
            "px": terms["px"],
            "maker_short": "did:key:z" + terms["maker"][9:15] + "…" + terms["maker"][-4:],
            "taker": terms["taker"],
            "until": terms["until"],
        },
    }


def route_accept(body: dict) -> dict:
    room = str(body.get("room") or DEFAULT_TRADE_ROOM)
    with _state_lock:
        state = load_state()
        if body.get("seed_hex"):
            taker_did, _, taker_priv = identity(str(body["seed_hex"]))
        else:
            taker_did, taker_priv = require_key(state)
        if contest_payload(state)["locked"]:
            raise ApiError("مسابقه قفل شده (بعد از 4 اکتبر 09:00 UTC)")
        terms, msig = parse_offer(body)
        if terms["until"] < current_sweep() + 1:
            raise ApiError(
                f"پیشنهاد منقضی شده است (until={terms['until']}، sweep فعلی {current_sweep()}) — "
                "قبول آن باطل (void) می‌شود"
            )
        named = terms.get("taker")
        if named != "any" and named != taker_did:
            raise ApiError("این پیشنهاد برای کلید دیگری است؛ باید با همان کلید قبول شود")
        tsig = sign(taker_priv, f"{SEASON}|accept|{canon(terms)}|{taker_did}")
        message = {
            "t": "trade",
            "season": SEASON,
            "terms": terms,
            "taker": taker_did,
            "maker_sig": msig,
            "taker_sig": tsig,
        }
        text = compact(message)
        result = chat_write(room, text, state)
        log_event(state, "accept", {"id": terms["id"], "room": room, "code": result["code"],
                                    "side": terms["side"], "qty": terms["qty"], "px": terms["px"]})
        save_state(state)
    return {"ok": 200 <= result["code"] < 300, "terms": terms, "taker_sig": tsig, **result}


def route_post(body: dict) -> dict:
    room = str(body.get("room") or DEFAULT_TRADE_ROOM)
    text = body.get("text")
    if not isinstance(text, str):
        raise ApiError("text لازم است")
    with _state_lock:
        state = load_state()
        require_key(state)
        result = chat_write(room, text, state)
        log_event(state, "post", {"room": room, "code": result["code"]})
        save_state(state)
    return {"ok": 200 <= result["code"] < 300, **result}


ROUTES_POST = {
    "/api/key/new": route_key_new,
    "/api/key/import": route_key_import,
    "/api/key/export": route_key_export,
    "/api/register": route_register,
    "/api/register-room": route_register_room,
    "/api/offer": route_offer,
    "/api/inspect": route_inspect,
    "/api/accept": route_accept,
    "/api/post": route_post,
}


def selftest() -> None:
    did, seed_hex, priv = identity(None)
    assert DID_RE.match(did)
    assert identity(seed_hex)[0] == did
    text = compact({"t": "owner", "season": SEASON, "key": did})
    verify_sig(did, sign(priv, f"close1|1|{text}"), f"close1|1|{text}")
    terms = {"id": "ab12cd34", "maker": did, "px": "100.00", "qty": "1",
             "side": "buy", "taker": "any", "until": 10}
    msig = sign(priv, f"{SEASON}|terms|{canon(terms)}")
    verify_sig(did, msig, f"{SEASON}|terms|{canon(terms)}")
    tsig = sign(priv, f"{SEASON}|accept|{canon(terms)}|{did}")
    verify_sig(did, tsig, f"{SEASON}|accept|{canon(terms)}|{did}")
    print(f"selftest ok  {did}")


def main() -> None:
    import sys

    if "--selftest" in sys.argv:
        selftest()
        return
    url = "http://127.0.0.1:8777/"
    print(f"Close Call desk: {url}")
    if "--open" in sys.argv:
        import threading
        import webbrowser

        threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    ThreadingHTTPServer.allow_reuse_address = True
    server = ThreadingHTTPServer(("127.0.0.1", 8777), Handler)
    server.serve_forever()


if __name__ == "__main__":
    main()
