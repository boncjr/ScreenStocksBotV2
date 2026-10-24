"""
Screen Stocks Trader, Haunted AI edition

* Trades every stock folder it finds under the game's commands folder.
* Tracks realized and open income.
* Auto-adapt: a background "brain" backtests candidate buy / short / sell rules on each stock's
  recorded prices, checks them on data it didn't train on, and only adopts rules that hold up.
Runs on plain Python 3 with Tkinter (nothing extra to install).
"""
import json, math, os, queue, random, threading, time
import tkinter as tk
from collections import deque
from datetime import date, datetime, timezone
from tkinter import font as tkfont, messagebox, simpledialog

try:
    import winsound
except ImportError:          # not on Windows
    winsound = None

APP_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_FILE = os.path.join(APP_DIR, "config.json")
LEDGER_FILE = os.path.join(APP_DIR, "trades.json")
HISTORY_FILE = os.path.join(APP_DIR, "history.json")
BRAIN_FILE = os.path.join(APP_DIR, "brain.json")

# ================= PALETTE =================
HEAD, PANEL_HDR = "#0f0719", "#0c0615"
BG, PANEL, PANEL2, LINE = "#140b22", "#1f1333", "#170e27", "#3a2656"
TEXT, MUTED = "#f1e9d2", "#a898c4"
ORANGE, ORANGE_H = "#ff8a1f", "#ffa24d"
PURPLE_D, PURPLE_H = "#33205f", "#432b7a"
BRAIN, BRAIN_D = "#b48cff", "#3a2a6e"
SLIME, BLOOD = "#9dff5a", "#ff5a74"
ZONE_G, ZONE_R = "#264a2e", "#55233b"
POS_G, POS_R = "#1f4a2a", "#55202f"
FONT = "Segoe UI"
DISPLAY_FONT = "Georgia"


def mix(c1, c2, t):
    t = max(0.0, min(1.0, t))
    a = [int(c1[i:i + 2], 16) for i in (1, 3, 5)]
    b = [int(c2[i:i + 2], 16) for i in (1, 3, 5)]
    return "#%02x%02x%02x" % tuple(int(a[i] + (b[i] - a[i]) * t) for i in range(3))


# ================= CONSTANTS =================
TECH, PLAIN = "$TECH", "$PLAIN"
PRICE_ALIASES = {"$PLAIN": "$BASE"}        # stock folder -> market.json name used for its price
LOOP_DELAY, EXTRA, CLOSE_LOCK = 1.0, 2.0, 3.0
SAMPLE_EVERY, HISTORY_MAX = 10.0, 3000     # one price sample per 10s, about 8 hours kept
DEFAULT_LOCK = {"buymax.json": 105.0, "shortmax.json": 102.0}
COOLDOWN_BARS = 11                         # the buy/short cooldown, in price samples

DEFAULT_SETTINGS = {
    "adapt": False, "sounds": False, "dry_run": False,
    "max_positions": 0.0, "daily_target": None, "daily_loss": None,
    "auto_buy_pct": 20.0, "auto_close_pct": 80.0, "auto_warmup": 60.0, "auto_min_range": 6.0,
    "auto_stop_pct": 8.0, "auto_trail_pct": None, "auto_short": False,
    "brain_min_samples": 240.0, "brain_interval": 20.0, "brain_fee_pct": 0.15,
    "brain_min_conf": 0.25, "brain_standdown": False,
}


def base_stock():
    return {"enabled": True, "auto": True, "brain_lock": False, "buy_at": None, "close_at": None,
            "stop_loss": None, "short_enabled": False, "short_at": None, "cover_at": None,
            "short_stop": None, "crash_enabled": False, "crash_short": None, "crash_buy": None,
            "crash_start": "17:50", "crash_end": "18:10"}


STOCK_KEYS = list(base_stock().keys())
PRESETS = {
    TECH: {"auto": False, "buy_at": 10.0, "close_at": 21.0, "stop_loss": 7.5, "short_enabled": True,
           "short_at": 21.0, "cover_at": 10.0, "short_stop": 26.0},
    PLAIN: {"auto": False, "buy_at": 600.0, "close_at": 900.0, "short_enabled": False,
            "short_stop": 900.0, "crash_enabled": True, "crash_short": 900.0, "crash_buy": 15.0},
}


def rules_for(cfg, stock):
    r = base_stock()
    r.update(PRESETS.get(stock, {}))
    r.update(cfg["stocks"].get(stock, {}))
    return r


def game_base(username):
    return rf"C:\Users\{username}\AppData\LocalLow\Conradical Games\Screen Stocks\mods"


def load_config():
    cfg = {"username": "", "settings": dict(DEFAULT_SETTINGS), "stocks": {}}
    try:
        with open(CONFIG_FILE, "r", encoding="utf-8") as f:
            saved = json.load(f)
        cfg["username"] = saved.get("username", "") or ""
        cfg["settings"].update(saved.get("settings", {}))
        cfg["stocks"] = saved.get("stocks", {})
        old = saved.get("rules")                       # config from the first GUI
        if old and not saved.get("stocks"):
            for key, stock in (("tech", TECH), ("plain", PLAIN)):
                if key in old:
                    cfg["stocks"][stock] = {k: v for k, v in old[key].items() if k in STOCK_KEYS}
    except Exception:
        pass
    return cfg


def save_config(cfg):
    with open(CONFIG_FILE, "w", encoding="utf-8") as f:
        json.dump({"username": cfg["username"], "settings": cfg["settings"], "stocks": cfg["stocks"]}, f, indent=4)


def money(v, sign=True):
    s = f"${abs(v):,.2f}"
    if not sign:
        return s if v >= 0 else "-" + s
    return ("+" if v > 0.004 else "-" if v < -0.004 else "") + s


def money_color(v):
    return SLIME if v > 0.004 else BLOOD if v < -0.004 else MUTED


def play(kind, enabled):
    """Tiny spooky sound effects (Windows only, off by default)."""
    if not enabled or winsound is None:
        return
    seq = {"win": [(880, 70), (1320, 110)], "loss": [(300, 140), (200, 220)],
           "brain": [(660, 60), (880, 60), (1175, 90)]}.get(kind, [])

    def go():
        try:
            for f, d in seq:
                winsound.Beep(f, d)
        except Exception:
            pass
    threading.Thread(target=go, daemon=True).start()


# ================= MARKET HELPERS =================
def collect_prices(data, out=None):
    """One pass over market.json: every dict with a price, keyed by name/stockId/id/symbol/ticker."""
    out = {} if out is None else out
    if isinstance(data, dict):
        if "price" in data:
            try:
                p = float(data["price"])
            except (TypeError, ValueError):
                p = None
            if p is not None:
                for k in ("name", "stockId", "id", "symbol", "ticker"):
                    v = data.get(k)
                    if isinstance(v, str) and v not in out:
                        out[v] = p
        for v in data.values():
            if isinstance(v, (dict, list)):
                collect_prices(v, out)
    elif isinstance(data, list):
        for v in data:
            if isinstance(v, (dict, list)):
                collect_prices(v, out)
    return out


def collect_seed_history(data, out=None):
    """If the game exports a price history next to a stock, use it to jump-start learning."""
    out = {} if out is None else out
    if isinstance(data, dict):
        name = data.get("name") or data.get("stockId")
        if isinstance(name, str):
            for k in ("history", "priceHistory", "prices", "candles"):
                lst = data.get(k)
                if isinstance(lst, list) and len(lst) >= 30:
                    vals = []
                    for x in lst:
                        if isinstance(x, (int, float)):
                            vals.append(float(x))
                        elif isinstance(x, dict):
                            v = x.get("price", x.get("close"))
                            if isinstance(v, (int, float)):
                                vals.append(float(v))
                    if len(vals) >= 30 and name not in out:
                        out[name] = vals[-HISTORY_MAX:]
        for v in data.values():
            if isinstance(v, (dict, list)):
                collect_seed_history(v, out)
    elif isinstance(data, list):
        for v in data:
            if isinstance(v, (dict, list)):
                collect_seed_history(v, out)
    return out


def position_from(p):
    hint = None
    for k in ("averagePrice", "avgPrice", "averageCost", "avgCost", "averageEntryPrice", "entryPrice"):
        try:
            v = float(p[k])
            if v > 0:
                hint = v
                break
        except (KeyError, TypeError, ValueError):
            pass
    return int(p.get("sharesOwned", 0)), int(p.get("sharesShorted", 0)), hint


def discover_stocks(base):
    """{stock folder: set of command files} from the game's commands folder."""
    root, out = os.path.join(base, "commands"), {}
    try:
        for n in sorted(os.listdir(root)):
            p = os.path.join(root, n)
            if os.path.isdir(p):
                out[n] = {f for f in os.listdir(p) if f.endswith(".json")}
    except OSError:
        pass
    return out


def parse_hm(text):
    h, m = str(text).strip().split(":")
    h, m = int(h), int(m)
    if not (0 <= h < 24 and 0 <= m < 60):
        raise ValueError
    return h, m


def quantile(vals, q):
    s = sorted(vals)
    if not s:
        return 0.0
    i = min(max(q, 0.0), 1.0) * (len(s) - 1)
    lo = int(i)
    hi = min(lo + 1, len(s) - 1)
    return s[lo] + (s[hi] - s[lo]) * (i - lo)


# ================= LEDGER (income tracking) =================
class Ledger:
    """Watches position changes and books realized profit, whoever placed the trade."""

    def __init__(self):
        self.d = {"since": time.time(), "run_seconds": 0.0, "positions": {}, "trades": []}
        try:
            with open(LEDGER_FILE, "r", encoding="utf-8") as f:
                self.d.update(json.load(f))
        except Exception:
            pass
        self.by_stock = {}
        for t in self.d["trades"]:
            self.by_stock[t["stock"]] = self.by_stock.get(t["stock"], 0.0) + t["pnl"]
        self._dirty, self._saved = False, 0.0

    def save(self, force=False):
        if not self._dirty or (not force and time.time() - self._saved < 5):
            return
        try:
            tmp = LEDGER_FILE + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(self.d, f)
            os.replace(tmp, LEDGER_FILE)
            self._dirty, self._saved = False, time.time()
        except Exception:
            pass

    def observe(self, stock, price, owned, shorted, hint, reseed):
        pos = self.d["positions"].get(stock)
        if pos is None or reseed:
            new = {"long": [owned, 0.0], "short": [shorted, 0.0]}
            for side, cur in (("long", owned), ("short", shorted)):
                if cur:
                    keep = pos and pos[side][0] == cur and pos[side][1] > 0
                    new[side][1] = pos[side][1] if keep else (hint or price)
            if new != pos:
                self.d["positions"][stock] = new
                self._dirty = True
            return
        for side, cur in (("long", owned), ("short", shorted)):
            prev, avg = pos[side]
            if cur == prev:
                continue
            self._dirty = True
            if cur > prev:
                pos[side][1] = (prev * avg + (cur - prev) * price) / cur
            else:
                d = prev - cur
                pnl = (price - avg) * d if side == "long" else (avg - price) * d
                self.d["trades"].append({"t": time.time(), "stock": stock, "side": side, "shares": d,
                                         "entry": avg, "exit": price, "pnl": pnl})
                self.by_stock[stock] = self.by_stock.get(stock, 0.0) + pnl
                if cur == 0:
                    pos[side][1] = 0.0
            pos[side][0] = cur

    def entry(self, stock, side):
        pos = self.d["positions"].get(stock)
        return pos[side][1] if pos else 0.0

    def open_pnl(self, stock, price):
        pos = self.d["positions"].get(stock)
        if not pos or price is None:
            return 0.0
        total = 0.0
        if pos["long"][0] and pos["long"][1] > 0:
            total += (price - pos["long"][1]) * pos["long"][0]
        if pos["short"][0] and pos["short"][1] > 0:
            total += (pos["short"][1] - price) * pos["short"][0]
        return total

    def today(self):
        d = date.today()
        return sum(t["pnl"] for t in self.d["trades"] if datetime.fromtimestamp(t["t"]).date() == d)

    def equity(self):
        cum, out = 0.0, [0.0]
        for t in self.d["trades"]:
            cum += t["pnl"]
            out.append(cum)
        return out

    def stats(self):
        t = self.d["trades"]
        n = len(t)
        total = sum(x["pnl"] for x in t)
        hours = max(self.d["run_seconds"] / 3600.0, 0.25)
        return {"n": n, "total": total, "today": self.today(),
                "avg_trade": total / n if n else None,
                "avg_hour": total / hours if n else None,
                "win": 100.0 * sum(1 for x in t if x["pnl"] > 0) / n if n else None}


class History:
    def __init__(self):
        self.d, self.last, self._saved = {}, {}, time.time()
        try:
            with open(HISTORY_FILE, "r", encoding="utf-8") as f:
                for k, v in json.load(f).items():
                    self.d[k] = deque(v, maxlen=HISTORY_MAX)
        except Exception:
            pass

    def add(self, stock, price, now):
        if now - self.last.get(stock, 0.0) >= SAMPLE_EVERY:
            self.d.setdefault(stock, deque(maxlen=HISTORY_MAX)).append(round(price, 4))
            self.last[stock] = now

    def seed(self, stock, vals):
        self.d[stock] = deque([round(v, 4) for v in vals], maxlen=HISTORY_MAX)

    def count(self, stock):
        return len(self.d.get(stock, ()))

    def values(self, stock):
        dq = self.d.get(stock)
        for _ in range(3):
            try:
                return list(dq) if dq is not None else []
            except RuntimeError:        # deque changed while copying, retry
                continue
        return []

    def save(self, now, force=False):
        if not force and now - self._saved < 60:
            return
        self._saved = now
        try:
            tmp = HISTORY_FILE + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump({k: self.values(k) for k in list(self.d)}, f)
            os.replace(tmp, HISTORY_FILE)
        except Exception:
            pass


# ================= THE BRAIN =================
AXES = {
    "buy_q": [3, 6, 10, 15, 20, 25, 30, 35, 40],       # buy in the lowest N% of the recent range
    "close_q": [60, 65, 70, 75, 80, 85, 90, 95, 97],   # close / short in the top of the range
    "stop": [None, 2, 4, 6, 9, 13],                    # stop loss %
    "trail": [None, 2, 4, 7],                          # trailing stop %
    "short": [False, True],
    "win": [120, 300, 600, 1200],                      # lookback, in samples
}
QS = sorted(set(AXES["buy_q"] + AXES["close_q"]))


def level_tables(prices, stride=10):
    """For every lookback window and percentile, the level in force at each sample."""
    n = len(prices)
    tables = {}
    for w in AXES["win"]:
        arrs = {q: [0.0] * n for q in QS}
        i = 0
        while i < n:
            win = sorted(prices[max(0, i - w):i])
            if len(win) >= 30:
                m = len(win) - 1
                vals = {q: win[int(q / 100.0 * m)] for q in QS}
                end = min(i + stride, n)
                for q in QS:
                    arr, v = arrs[q], vals[q]
                    for j in range(i, end):
                        arr[j] = v
            i += stride
        tables[w] = arrs
    return tables


def simulate(prices, BL, CL, lo, hi, stop, trail, short, fee, mr, curve=None):
    """Replays the live rules over past prices. Returns (return, max drawdown, trades, wins)."""
    pos, entry, ext = 0, 0.0, 0.0
    eq, top, dd, trades, wins, wait = 1.0, 1.0, 0.0, 0, 0, 0
    for i in range(lo, hi):
        p, b, c = prices[i], BL[i], CL[i]
        if pos == 0:
            if wait > 0:
                wait -= 1
            elif b > 0 and c >= b * (1 + mr):
                if p <= b:
                    pos, entry, ext = 1, p, p
                    eq *= 1 - fee
                elif short and p >= c:
                    pos, entry, ext = -1, p, p
                    eq *= 1 - fee
        elif pos == 1:
            if p > ext:
                ext = p
            if p >= c or (stop and p <= entry * (1 - stop / 100.0)) or (trail and p <= ext * (1 - trail / 100.0)):
                r = (p / entry) * (1 - fee)
                eq *= r
                trades += 1
                wins += r > 1.0
                pos, wait = 0, COOLDOWN_BARS
        else:
            if p < ext:
                ext = p
            if p <= b or (stop and p >= entry * (1 + stop / 100.0)) or (trail and p >= ext * (1 + trail / 100.0)):
                r = (1 + (entry - p) / entry) * (1 - fee)
                eq *= r
                trades += 1
                wins += r > 1.0
                pos, wait = 0, COOLDOWN_BARS
        mtm = eq * (p / entry) if pos == 1 else eq * (1 + (entry - p) / entry) if pos == -1 else eq
        if mtm > top:
            top = mtm
        elif top > 0 and 1 - mtm / top > dd:
            dd = 1 - mtm / top
        if curve is not None:
            curve.append(mtm)
    last = eq
    if pos == 1:
        last = eq * (prices[hi - 1] / entry)
    elif pos == -1:
        last = eq * (1 + (entry - prices[hi - 1]) / entry)
    return last - 1.0, dd, trades, int(wins)


def eval_params(prices, tables, p, start, split, fee, mr):
    T = tables[p["win"]]
    BL, CL = T[p["buy_q"]], T[p["close_q"]]
    tr = simulate(prices, BL, CL, start, split, p["stop"], p["trail"], p["short"], fee, mr)
    te = simulate(prices, BL, CL, split, len(prices), p["stop"], p["trail"], p["short"], fee, mr)
    f_tr, f_te = tr[0] - 0.35 * tr[1], te[0] - 0.35 * te[1]
    valid = tr[2] >= 3 and te[2] >= 1 and te[0] > 0       # must profit on data it never trained on
    return {"total": 0.4 * f_tr + 0.6 * f_te, "tr": list(tr), "te": list(te), "valid": valid}


def random_params(rng):
    return {k: rng.choice(v) for k, v in AXES.items()}


def neighbors(p):
    out = []
    for k, vals in AXES.items():
        i = vals.index(p[k])
        for j in (i - 1, i + 1):
            if 0 <= j < len(vals):
                q = dict(p)
                q[k] = vals[j]
                out.append(q)
    return out


def describe_params(p):
    mins = p["win"] * SAMPLE_EVERY / 60.0
    stop = f"{p['stop']}% stop" if p["stop"] else "no stop"
    trail = f", {p['trail']}% trailing stop" if p["trail"] else ""
    sh = "shorts the highs" if p["short"] else "long only"
    return (f"Buys in the lowest {p['buy_q']}% of the last {mins:.0f} minutes, sells in the top "
            f"{100 - p['close_q']}%, {sh}, {stop}{trail}.")


class Brain(threading.Thread):
    """Walk-forward optimizer: tune on the older 70% of prices, prove it on the newest 30%."""

    def __init__(self, cfg, history, log_q):
        super().__init__(daemon=True)
        self.cfg, self.history, self.log_q = cfg, history, log_q
        self.halt = threading.Event()
        self.state = {"stocks": {}}
        self.rng = random.Random()
        self.last_cycle, self.rr, self.busy, self.last_event = 0.0, 0, None, 0.0
        try:
            with open(BRAIN_FILE, "r", encoding="utf-8") as f:
                self.state = json.load(f)
        except Exception:
            pass

    def log(self, msg, level="brain"):
        self.log_q.put((datetime.now().strftime("%H:%M:%S"), level, msg))

    def save(self):
        try:
            tmp = BRAIN_FILE + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(self.state, f)
            os.replace(tmp, BRAIN_FILE)
        except Exception:
            pass

    def reset(self, stock=None):
        if stock is None:
            self.state = {"stocks": {}}
        else:
            self.state["stocks"].pop(stock, None)
        self.save()

    def info(self, stock):
        return self.state["stocks"].get(stock)

    def live_params(self, stock, st):
        S = self.state["stocks"].get(stock)
        if not S or not S.get("params") or S.get("conf", 0.0) < float(st.get("brain_min_conf") or 0):
            return None
        return S["params"]

    def no_edge(self, stock):
        S = self.state["stocks"].get(stock)
        return bool(S and S.get("rounds", 0) >= 3 and not S.get("params"))

    def eligible(self, stock):
        r = rules_for(self.cfg, stock)
        return r["enabled"] and not r["brain_lock"]

    def run(self):
        while not self.halt.wait(1.0):
            st = self.cfg["settings"]
            if not st.get("adapt"):
                self.busy = None
                continue
            if time.time() - self.last_cycle < float(st.get("brain_interval") or 20):
                continue
            need = int(st.get("brain_min_samples") or 240)
            names = [s for s in sorted(self.history.d) if self.history.count(s) >= need and self.eligible(s)]
            self.last_cycle = time.time()
            if not names:
                continue
            s = names[self.rr % len(names)]
            self.rr += 1
            self.busy = s
            try:
                self.optimize(s)
            except Exception as e:
                self.log(f"{s}: brain hiccup, {e}", "error")
            self.busy = None
            self.save()

    def optimize(self, s):
        st = self.cfg["settings"]
        prices = self.history.values(s)
        n = len(prices)
        fee, mr = float(st["brain_fee_pct"]) / 100.0, float(st["auto_min_range"]) / 100.0
        tables = level_tables(prices)
        start, split = 60, int(n * 0.7)
        S = self.state["stocks"].setdefault(s, {"gen": 0, "params": None, "conf": 0.0, "rounds": 0, "hist": []})

        def ev(p):
            return eval_params(prices, tables, p, start, split, fee, mr)

        cur = S.get("params")
        cur_ev = ev(cur) if cur else None
        cands = (neighbors(cur) if cur else []) + [random_params(self.rng) for _ in range(90)]
        best, best_ev, tried = None, None, 0
        for p in cands:
            e = ev(p)
            tried += 1
            time.sleep(0)                              # let the trader thread breathe
            if e["valid"] and (best_ev is None or e["total"] > best_ev["total"]):
                best, best_ev = p, e
        S["rounds"] = S.get("rounds", 0) + 1
        adopted = bool(best_ev and (cur is None or not cur_ev["valid"] or best_ev["total"] > cur_ev["total"] + 0.002))
        if adopted:
            S["params"], S["ev"] = best, best_ev
            S["gen"] = S.get("gen", 0) + 1
            gain = best_ev["te"][0] * 100
            self.log(f"{s} evolved to generation {S['gen']}: {describe_params(best)} "
                     f"Unseen-data return {gain:+.1f}% after {tried} mutations.", "brain_up")
            self.last_event = time.time()
        elif cur:
            S["ev"] = cur_ev
            self.log(f"{s}: tried {tried} mutations, nothing beat generation {S['gen']}.", "brain")
        else:
            self.log(f"{s}: tried {tried} rule sets, none made money on unseen prices yet.", "brain")
        ev_now = S.get("ev")
        if S.get("params") and ev_now:
            trades = ev_now["tr"][2] + ev_now["te"][2]
            S["conf"] = min(1.0, n / 1500.0) * min(1.0, trades / 10.0) * (1.0 if ev_now["valid"] else 0.3)
            curve = []
            p = S["params"]
            T = tables[p["win"]]
            simulate(prices, T[p["buy_q"]], T[p["close_q"]], start, n, p["stop"], p["trail"], p["short"], fee, mr, curve)
            step = max(1, len(curve) // 160)
            S["curve"] = [round(x, 4) for x in curve[::step]]
            base = prices[start] or 1.0
            S["hold"] = [round(x / base, 4) for x in prices[start::step][:len(S["curve"])]]
        else:
            S["conf"] = 0.0
        S["hist"].append({"t": time.time(), "fit": (ev_now["total"] if ev_now else 0.0), "gen": S.get("gen", 0)})
        S["hist"] = S["hist"][-120:]
        S["samples"] = n


# ================= TRADING ENGINE =================
def mk(kind=None, why="", note="", score=0.0):
    return {"kind": kind, "why": why, "note": note, "score": score}


class Engine(threading.Thread):
    def __init__(self, cfg, ledger, history, brain, log_q, base=None):
        super().__init__(daemon=True)
        self.cfg, self.ledger, self.history, self.brain, self.log_q = cfg, ledger, history, brain, log_q
        self.base = base or game_base(cfg["username"])
        self.halt = threading.Event()
        self.pause_entries, self.close_all = False, False
        self.lock_len, self.unlock_at, self.pending = {}, {}, {}
        self.state, self.seen, self.seeded = {}, set(), set()
        self.stocks, self.cmds, self._stocks_at = [], {}, 0.0
        self.snap = {"link": "idle", "stocks": {}, "halt": None, "open_pnl": 0.0}
        self.halt_msg, self._last_err, self._warned_empty = None, None, False

    # ---------- plumbing ----------
    def log(self, msg, level="info"):
        self.log_q.put((datetime.now().strftime("%H:%M:%S"), level, msg))

    def read_market(self):
        try:
            with open(os.path.join(self.base, "export", "market.json"), encoding="utf-8") as f:
                data = json.load(f)
            self._last_err = None
            return data
        except Exception as e:
            msg = f"Can't read market.json: {e}"
            if msg != self._last_err:
                self.log(msg, "error")
                self._last_err = msg
            return None

    def has_cmd(self, stock, cmd):
        return cmd in self.cmds.get(stock, ())

    def cooldowns(self, stock):
        out = {}
        for cmd in ("buymax.json", "shortmax.json", "closemax.json"):
            key = f"{stock}/{cmd}"
            out[cmd] = (max(0.0, self.unlock_at.get(key, 0.0) - time.time()),
                        self.lock_len.get(key, DEFAULT_LOCK.get(cmd, CLOSE_LOCK) + EXTRA))
        return out

    def update_cooldowns(self, market):
        player = market.get("player", {})
        for cmd, key in (("buymax.json", "buyCooldownSeconds"), ("shortmax.json", "shortCooldownSeconds")):
            try:
                v = float(player[key]) + EXTRA
            except (KeyError, TypeError, ValueError):
                v = DEFAULT_LOCK[cmd] + EXTRA
            for s in self.stocks:
                self.lock_len[f"{s}/{cmd}"] = v
        for s in self.stocks:
            self.lock_len[f"{s}/closemax.json"] = CLOSE_LOCK

    def locked(self, stock, cmd):
        return self.unlock_at.get(f"{stock}/{cmd}", 0.0) > time.time()

    def fire(self, stock, cmd, why=""):
        key = f"{stock}/{cmd}"
        if self.locked(stock, cmd):
            return False
        names = {"buymax.json": "Buy max", "shortmax.json": "Short max", "closemax.json": "Close"}
        label = f"{stock}: {names.get(cmd, cmd)}" + (f" ({why})" if why else "")
        lock = self.lock_len.get(key, CLOSE_LOCK)
        if self.cfg["settings"].get("dry_run"):
            self.unlock_at[key] = time.time() + lock
            self.log("Dry run, would do " + label, "action")
            return True
        path = os.path.join(self.base, "commands", stock, cmd)
        try:
            with open(path, encoding="utf-8") as f:
                data = json.load(f)
            data["execute"] = True
            with open(path, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=4)
            self.unlock_at[key] = time.time() + lock
            self.log(label, "action")
            return True
        except FileNotFoundError:
            self.unlock_at[key] = time.time() + 300
            self.log(f"{stock}: {cmd} doesn't exist, skipping it for 5 minutes", "error")
        except Exception as e:
            self.unlock_at[key] = time.time() + 10
            self.log(f"{label}: {e}", "error")
        return False

    # ---------- main loop ----------
    def run(self):
        self.log("Trader started")
        last = time.time()
        while not self.halt.wait(LOOP_DELAY):
            now = time.time()
            dt, last = now - last, now
            market = self.read_market()
            if market is None:
                self.snap = {**self.snap, "link": "nodata"}
                continue
            try:
                self.tick(market, now, dt)
            except Exception as e:
                self.log(f"Tick failed: {e}", "error")
        self.ledger.save(True)
        self.history.save(time.time(), True)
        self.snap = {"link": "idle", "stocks": {}, "halt": None, "open_pnl": 0.0}
        self.log("Trader stopped")

    def tick(self, market, now, dt):
        if now - self._stocks_at > 10:
            found = discover_stocks(self.base)
            self.stocks, self.cmds, self._stocks_at = list(found), found, now
            if not found and not self._warned_empty:
                self.log("No stock folders found under commands", "error")
                self._warned_empty = True
        if not self.seeded:                                   # jump-start learning if the game shares price history
            self.seeded.add("done")
            for name, vals in collect_seed_history(market).items():
                if self.history.count(name) < 60:
                    self.history.seed(name, vals)
                    self.log(f"Seeded {name} with {len(vals)} past prices from market.json", "brain")
        prices = collect_prices(market)
        self.update_cooldowns(market)
        self.ledger.d["run_seconds"] += min(dt, 5.0)
        st = self.cfg["settings"]
        posmap = {p.get("stockId"): p for p in market.get("player", {}).get("positions", [])}

        today = self.ledger.today()
        halt = None
        if st.get("daily_target") and today >= st["daily_target"]:
            halt = "Daily profit target reached"
        elif st.get("daily_loss") and today <= -st["daily_loss"]:
            halt = "Daily loss limit reached"
        if halt != self.halt_msg:
            if halt:
                self.log(halt + ", no new entries today", "error")
            self.halt_msg = halt

        views, acts = {}, {}
        for s in self.stocks:
            r = rules_for(self.cfg, s)
            price = prices.get(s)
            if price is None and s in PRICE_ALIASES:
                price = prices.get(PRICE_ALIASES[s])
            owned, shorted, hint = position_from(posmap[s]) if s in posmap else (0, 0, None)
            info = self.brain.info(s) if self.brain else None
            view = {"price": price, "owned": owned, "shorted": shorted, "note": "", "levels": None,
                    "auto": r["auto"], "enabled": r["enabled"], "crash": self.crash_levels(r),
                    "spark": [], "realized": self.ledger.by_stock.get(s, 0.0), "open_pnl": 0.0,
                    "brain_gen": info.get("gen", 0) if info else 0, "brain_active": False,
                    "samples": self.history.count(s)}
            views[s] = view
            if price is None:
                view["note"] = "No price in market.json"
                continue
            self.ledger.observe(s, price, owned, shorted, hint, s not in self.seen)
            self.seen.add(s)
            self.history.add(s, price, now)
            view["spark"] = self.history.values(s)[-60:]
            view["open_pnl"] = self.ledger.open_pnl(s, price)
            L, reason = self.levels(s, r, st)
            view["levels"] = L
            view["brain_active"] = bool(L and L.get("brain"))
            if not r["enabled"]:
                view["note"] = "Turned off in rules"
                continue
            a = self.decide(s, r, st, price, owned, shorted, L, reason)
            view["note"] = a["note"]
            acts[s] = a

        if self.close_all:
            left = 0
            for s, v in views.items():
                if v["owned"] or v["shorted"]:
                    left += 1
                    self.fire(s, "closemax.json", "close all")
                    v["note"] = "Closing everything"
            if not left:
                self.close_all = False
                self.log("All positions closed, new entries stay paused", "info")
        else:
            for s, a in acts.items():
                if a["kind"] == "close" and not self.fire(s, "closemax.json", a["why"]) and self.locked(s, "closemax.json"):
                    views[s]["note"] += " (waiting on cooldown)"
            maxpos = int(st.get("max_positions") or 0)
            open_count = sum(1 for s, v in views.items() if v["owned"] or v["shorted"] or self.pending.get(s, 0) > now)
            entries = sorted(((a["score"], s, a) for s, a in acts.items() if a["kind"] in ("buy", "short")), reverse=True)
            for _, s, a in entries:
                cmd = f"{a['kind']}max.json"
                if self.pause_entries:
                    views[s]["note"] = "Signal hit, entries are paused"
                elif self.halt_msg:
                    views[s]["note"] = self.halt_msg
                elif maxpos and open_count >= maxpos and not self.pending.get(s, 0) > now:
                    views[s]["note"] = "Signal hit, position limit reached"
                elif self.locked(s, cmd):
                    views[s]["note"] = "Signal hit, waiting on cooldown"
                elif self.fire(s, cmd, a["why"]):
                    self.pending[s] = now + 10
                    open_count += 1
                    views[s]["note"] = "Placing " + a["kind"] + " order"

        self.snap = {"link": "live", "stocks": views, "halt": self.halt_msg,
                     "open_pnl": sum(v["open_pnl"] for v in views.values())}
        self.ledger.save()
        self.history.save(now)

    # ---------- rules ----------
    def crash_levels(self, r):
        if r["crash_enabled"] and r["crash_buy"] is not None and r["crash_short"] is not None:
            return (r["crash_buy"], r["crash_short"])
        return None

    def crash_window(self, r):
        c = self.crash_levels(r)
        if not c:
            return None
        try:
            now = datetime.now(timezone.utc)
            if parse_hm(r["crash_start"]) <= (now.hour, now.minute) <= parse_hm(r["crash_end"]):
                return c
        except ValueError:
            pass
        return None

    def levels(self, s, r, st):
        mr = st["auto_min_range"] / 100.0
        # 1) the brain's learned rules, when auto-adapt is on and trusted
        if st.get("adapt") and self.brain and not r["brain_lock"]:
            bp = self.brain.live_params(s, st)
            if bp:
                vals = self.history.values(s)[-bp["win"]:]
                if len(vals) < 60:
                    return None, "The brain is gathering prices"
                lo, hi = quantile(vals, bp["buy_q"] / 100.0), quantile(vals, bp["close_q"] / 100.0)
                if lo <= 0 or hi < lo * (1 + mr):
                    return None, "Range is too narrow for the learned rules"
                return {"buy_at": lo, "close_at": hi, "stop_loss": None, "short_enabled": bool(bp["short"]),
                        "short_at": hi, "cover_at": lo, "short_stop": None, "stop_pct": bp["stop"],
                        "trail_pct": bp["trail"], "auto": True, "brain": True}, None
        # 2) auto-calibrated levels
        if r["auto"]:
            vals = self.history.values(s)
            warm = int(st["auto_warmup"] or 60)
            if len(vals) < warm:
                return None, f"Learning the price range ({len(vals)}/{warm})"
            lo, hi = quantile(vals, st["auto_buy_pct"] / 100), quantile(vals, st["auto_close_pct"] / 100)
            if lo <= 0 or hi < lo * (1 + mr):
                return None, "Price range is too narrow to trade"
            return {"buy_at": lo, "close_at": hi, "stop_loss": None, "short_enabled": bool(st["auto_short"]),
                    "short_at": hi, "cover_at": lo, "short_stop": None, "stop_pct": st.get("auto_stop_pct"),
                    "trail_pct": st.get("auto_trail_pct"), "auto": True, "brain": False}, None
        # 3) your manual levels
        if r["buy_at"] is None or r["close_at"] is None:
            return None, "Set buy and close levels in the rules"
        return {"buy_at": r["buy_at"], "close_at": r["close_at"], "stop_loss": r["stop_loss"],
                "short_enabled": bool(r["short_enabled"]),
                "short_at": r["short_at"] if r["short_at"] is not None else r["close_at"],
                "cover_at": r["cover_at"] if r["cover_at"] is not None else r["buy_at"],
                "short_stop": r["short_stop"], "stop_pct": None, "trail_pct": None,
                "auto": False, "brain": False}, None

    def decide(self, s, r, st, price, owned, shorted, L, reason):
        a = self._decide(s, r, st, price, owned, shorted, L, reason)
        if (a["kind"] in ("buy", "short") and st.get("adapt") and st.get("brain_standdown")
                and not r["brain_lock"] and self.brain and self.brain.no_edge(s)):
            return mk(note="The brain found no edge here, standing down")
        return a

    def _decide(self, s, r, st, price, owned, shorted, L, reason):
        S = self.state.setdefault(s, {"stopped": None, "ext": None})
        if owned:
            S["ext"] = price if S["ext"] is None else max(S["ext"], price)
        elif shorted:
            S["ext"] = price if S["ext"] is None else min(S["ext"], price)
        else:
            S["ext"] = None
        if L:
            if S["stopped"] == "long" and price > L["buy_at"]:
                S["stopped"] = None
            if S["stopped"] == "short" and price < L["short_at"]:
                S["stopped"] = None

        crash = self.crash_window(r)
        if crash:
            cb, cs = crash
            if owned:
                return mk(note="Crash window, holding")
            if shorted:
                if price < cb:
                    return mk("close", "crash payoff", "Crash window, closing the short")
                return mk(note="Crash window, short is open")
            if price > cs:
                return mk("short", "crash", "Crash window, short signal", (price - cs) / cs)
            if price < cb:
                return mk("buy", "crash", "Crash window, buy signal", (cb - price) / cb)
            return mk(note="Crash window, waiting")

        if L is None:
            return mk(note=reason)

        def stop(side, why):
            S["stopped"] = side
            return mk("close", why, why.capitalize() + " hit")

        sp, tp = L.get("stop_pct"), L.get("trail_pct")
        if owned:
            if L["stop_loss"] is not None and price <= L["stop_loss"]:
                return stop("long", "stop loss")
            entry = self.ledger.entry(s, "long")
            if sp and entry and price <= entry * (1 - sp / 100.0):
                return stop("long", "stop loss")
            if tp and S["ext"] and price <= S["ext"] * (1 - tp / 100.0):
                return stop("long", "trailing stop")
        if shorted:
            if L["short_stop"] is not None and price >= L["short_stop"]:
                return stop("short", "short stop")
            entry = self.ledger.entry(s, "short")
            if sp and entry and price >= entry * (1 + sp / 100.0):
                return stop("short", "short stop")
            if tp and S["ext"] and price >= S["ext"] * (1 + tp / 100.0):
                return stop("short", "trailing stop")

        short_ok = L["short_enabled"] and self.has_cmd(s, "shortmax.json")
        if price <= L["buy_at"]:
            if shorted:
                return mk("close", "cover short" if short_ok and price <= L["cover_at"] else "closing short before buy",
                          "Covering the short")
            if S["stopped"] == "long":
                return mk(note="Stopped out, waiting for price to recover")
            if owned:
                return mk(note="Already long")
            return mk("buy", "rule hit", "Buy signal", (L["buy_at"] - price) / L["buy_at"])
        if price >= L["close_at"]:
            if owned:
                return mk("close", "take profit", "Closing the long")
            if short_ok and price >= L["short_at"]:
                if S["stopped"] == "short":
                    return mk(note="Stopped out, waiting for price to recover")
                if shorted:
                    return mk(note="Already short")
                return mk("short", "rule hit", "Short signal", (price - L["short_at"]) / L["short_at"])
        return mk(note="Holding between levels" if (owned or shorted) else "Waiting for a signal")


# ================= GUI: WIDGETS =================
def pick_font(candidates, default):
    try:
        fams = set(tkfont.families())
    except Exception:
        return default
    return next((c for c in candidates if c in fams), default)


class Btn(tk.Button):
    def __init__(self, parent, text, command, bg, fg, hover):
        super().__init__(parent, text=text, command=command, bg=bg, fg=fg, activebackground=hover,
                         activeforeground=fg, relief="flat", bd=0, font=(FONT, 10, "bold"), padx=16, pady=7,
                         cursor="hand2", highlightthickness=2, highlightbackground=bg, highlightcolor=ORANGE_H,
                         takefocus=1)

    def restyle(self, text, bg, fg, hover):
        self.config(text=text, bg=bg, fg=fg, activebackground=hover, activeforeground=fg, highlightbackground=bg)


class AnimatedHeader(tk.Canvas):
    H = 150

    def __init__(self, parent):
        super().__init__(parent, bg=HEAD, height=self.H, highlightthickness=0)
        self.t, self.W, self.energy = 0, 0, 0.3
        self.particles, self.toasts, self.flash = [], [], 0
        self.stars, self.bats, self.fog, self.mood = [], [], [], "Asleep in the crypt"
        self.bind("<Configure>", lambda e: self.rebuild())

    # ---------- scene ----------
    def rebuild(self):
        w = max(self.winfo_width(), 760)
        self.W = w
        self.delete("all")
        self.particles, self.toasts, self.stars, self.bats, self.fog = [], [], [], [], []
        rng, H = random.Random(13), self.H
        for _ in range(70):
            x, y, r = rng.randint(0, w), rng.randint(2, H - 12), rng.choice((1, 1, 2))
            self.stars.append((self.create_oval(x, y, x + r, y + r, fill="#4a3a78", outline=""), rng.random() * 6.28))
        web = "#4a3470"
        angs = [math.radians(a) for a in (0, 22, 45, 68, 90)]
        for a in angs:
            self.create_line(0, 0, 100 * math.cos(a), 100 * math.sin(a), fill=web)
        for rad in (26, 50, 76, 100):
            pts = []
            for a in angs:
                pts += [rad * math.cos(a) * 0.92, rad * math.sin(a) * 0.92]
            self.create_line(*pts, fill=web, smooth=True)
        # moon with a breathing halo
        self.mx, self.my = int(w * 0.5), 62
        self.halo = [self.create_oval(self.mx - r, self.my - r, self.mx + r, self.my + r, fill=HEAD, outline="")
                     for r in (58, 46)]
        self.create_oval(self.mx - 32, self.my - 32, self.mx + 32, self.my + 32, fill="#f6e7a8", outline="")
        for dx, dy, r in ((-11, -9, 7), (10, 6, 9), (-5, 15, 5)):
            self.create_oval(self.mx + dx - r, self.my + dy - r, self.mx + dx + r, self.my + dy + r, fill="#e4d08a", outline="")
        # fog banks
        for i in range(3):
            y = H - 18 - i * 6
            self.fog.append([self.create_oval(0, y, 380, y + 36, fill="#2b1d4a", outline="", stipple="gray25"),
                             rng.randint(0, w), 0.25 + i * 0.18, y])
        # bats
        for fx, fy, s, v in ((0.12, 30, 1.0, 1.3), (0.38, 90, 0.7, 0.9), (0.62, 26, 0.8, 1.1), (0.75, 78, 1.0, 1.5), (0.9, 40, 0.6, 1.0)):
            self.bats.append({"it": self.create_polygon(0, 0, 0, 0, 0, 0, fill="#07030d", outline="#3a2560"),
                              "x": w * fx, "y": fy, "s": 6 * s, "v": v, "ph": rng.random() * 6.28})
        # ghost
        self.ghost = self.create_polygon(0, 0, 0, 0, 0, 0, fill="#e9e4ff", outline="#bdb2ee", smooth=True)
        self.gl = [self.create_oval(0, 0, 1, 1, fill="#1b1030", outline="") for _ in range(2)]
        self.gm = self.create_oval(0, 0, 1, 1, fill="#1b1030", outline="")
        # jack-o-lantern, lit from inside
        px, py, r = 74, 84, 40
        self.pglow = self.create_oval(px - r * 1.7, py - r * 1.5, px + r * 1.7, py + r * 1.5, fill="#3b1a00", outline="")
        self.create_oval(px - r * 1.05, py - r * 0.8, px + r * 0.3, py + r * 0.85, fill="#d66200", outline="")
        self.create_oval(px - r * 0.3, py - r * 0.8, px + r * 1.05, py + r * 0.85, fill="#d66200", outline="")
        self.create_oval(px - r * 0.65, py - r * 0.88, px + r * 0.65, py + r * 0.92, fill=ORANGE, outline="")
        self.create_polygon(px - r * 0.12, py - r * 0.8, px + r * 0.12, py - r * 0.8, px + r * 0.24, py - r * 1.15,
                            px - r * 0.04, py - r * 1.1, fill="#5a7d2b", outline="")
        self.pface = []
        for sx in (-1, 1):
            ex = px + sx * r * 0.3
            self.pface.append(self.create_polygon(ex - r * 0.17, py - r * 0.08, ex + r * 0.17, py - r * 0.08, ex, py - r * 0.42,
                                                  fill="#ffe27a", outline=""))
        zig = []
        for i in range(7):
            zig += [px - r * 0.45 + i * r * 0.15, py + r * (0.28 if i % 2 == 0 else 0.5)]
        self.pface.append(self.create_polygon(zig + [px + r * 0.45, py + r * 0.28], fill="#ffe27a", outline=""))
        # title
        self.create_text(152, 56, text="Screen Stocks Trader", anchor="w", font=(DISPLAY_FONT, 36), fill="#6b2fd1")
        self.create_text(149, 53, text="Screen Stocks Trader", anchor="w", font=(DISPLAY_FONT, 36), fill=ORANGE)
        self.mood_item = self.create_text(153, 108, text=self.mood, anchor="w", font=(FONT, 11), fill=MUTED)
        self.flash_item = self.create_rectangle(0, 0, w, H, fill="#d9c8ff", outline="", state="hidden", stipple="gray25")

    # ---------- public effects ----------
    def set_mood(self, text):
        if text != self.mood:
            self.mood = text
            if self.W:
                self.itemconfig(self.mood_item, text=text)

    def burst(self, x, y, color, n=20, speed=3.2, gravity=0.08):
        for _ in range(n):
            if len(self.particles) > 220:
                break
            a, sp, r = random.random() * 6.283, random.random() * speed + 0.6, random.choice((2, 2, 3))
            it = self.create_oval(x - r, y - r, x + r, y + r, fill=color, outline="")
            self.particles.append([it, x, y, math.cos(a) * sp, math.sin(a) * sp - 1.2, r, random.randint(26, 52), color, gravity])

    def toast(self, text, color):
        if not self.W:
            return
        x = random.randint(int(self.W * 0.3), int(self.W * 0.6))
        it = self.create_text(x, 96, text=text, font=(FONT, 15, "bold"), fill=color)
        self.toasts.append([it, x, 96.0, 70, color])

    def celebrate(self, amount, big=False):
        if not self.W:
            return
        x, y = random.randint(int(self.W * 0.3), int(self.W * 0.6)), 70
        self.burst(x, y, SLIME, 26)
        self.burst(x, y, ORANGE, 18, 4.0)
        self.toast(money(amount), SLIME)
        if big:
            self.flash = 7

    def grieve(self, amount):
        if not self.W:
            return
        x, y = random.randint(int(self.W * 0.3), int(self.W * 0.6)), 60
        self.burst(x, y, BLOOD, 22, 2.4, 0.14)
        self.burst(x, y, "#ff9a4d", 10, 2.0, 0.14)
        self.toast(money(amount), BLOOD)

    def brain_spark(self):
        if self.W:
            self.burst(self.mx, self.my, BRAIN, 30, 4.0, 0.02)
            self.toast("The brain evolved", BRAIN)
            self.flash = 4

    # ---------- animation ----------
    def tick(self):
        if not self.W:
            return
        self.t += 1
        t, W, H = self.t, self.W, self.H
        if t % 3 == 0:
            for it, ph in self.stars:
                self.itemconfig(it, fill=mix("#2a1f4d", "#cfc2ff", 0.5 + 0.5 * math.sin(t * 0.05 + ph)))
        pulse = 0.5 + 0.5 * math.sin(t * 0.03)
        self.itemconfig(self.halo[0], fill=mix(HEAD, "#2a1d4a", 0.4 + 0.4 * pulse))
        self.itemconfig(self.halo[1], fill=mix(HEAD, "#4a3a78", 0.4 + 0.4 * pulse))
        for it, x, sp, y in self.fog:
            pass
        for f in self.fog:
            f[1] = (f[1] + f[2] * (1 + self.energy)) % (W + 380)
            y = f[3]
            self.coords(f[0], f[1] - 380, y, f[1], y + 36)
        sp = 1.0 + 3.0 * self.energy
        for b in self.bats:
            b["x"] += b["v"] * sp
            if b["x"] > W + 40:
                b["x"] = -40
            y = b["y"] + 9 * math.sin(t * 0.06 + b["ph"])
            flap = math.sin(t * 0.45 + b["ph"])
            s = b["s"]
            pts = [(-3, -1), (-2, -2), (-1, -1.2), (-0.6, -2), (0, -1), (0.6, -2), (1, -1.2), (2, -2), (3, -1),
                   (2, 0.2), (1, -0.4), (0, 1), (-1, -0.4), (-2, 0.2)]
            flat = []
            for px, py in pts:
                dy = flap * 1.4 * max(0.0, abs(px) - 0.8)
                flat += [b["x"] + px * s, y + (py + dy) * s]
            self.coords(b["it"], *flat)
        # ghost drifting beside the moon
        gx, gy = W * 0.6 + 70 * math.sin(t * 0.011), 72 + 12 * math.sin(t * 0.05)
        w = 2.5 * math.sin(t * 0.2)
        pts = [(-15, 17), (-15, -6), (-9, -17), (0, -21), (9, -17), (15, -6), (15, 17), (10, 12 + w),
               (5, 17), (0, 12 - w), (-5, 17), (-10, 12 + w)]
        self.coords(self.ghost, *[v for x, y in pts for v in (gx + x, gy + y)])
        for k, sx in enumerate((-5, 5)):
            self.coords(self.gl[k], gx + sx - 2.5, gy - 8, gx + sx + 2.5, gy - 1)
        self.coords(self.gm, gx - 2, gy + 2, gx + 2, gy + 7)
        # candlelight flicker
        if t % 4 == 0:
            fl = 0.35 + 0.25 * random.random()
            self.itemconfig(self.pglow, fill=mix(HEAD, "#8a4400", fl))
            for it in self.pface:
                self.itemconfig(it, fill=mix("#ffcf40", "#fff3a0", random.random()))
        # particles
        for p in self.particles[:]:
            p[1] += p[3]
            p[2] += p[4]
            p[4] += p[8]
            p[6] -= 1
            if p[6] <= 0 or p[2] > H + 10:
                self.delete(p[0])
                self.particles.remove(p)
                continue
            r = p[5]
            self.coords(p[0], p[1] - r, p[2] - r, p[1] + r, p[2] + r)
            self.itemconfig(p[0], fill=mix(p[7], HEAD, 1 - min(1.0, p[6] / 30.0)))
        for tt in self.toasts[:]:
            tt[2] -= 0.7
            tt[3] -= 1
            if tt[3] <= 0:
                self.delete(tt[0])
                self.toasts.remove(tt)
                continue
            self.coords(tt[0], tt[1], tt[2])
            self.itemconfig(tt[0], fill=mix(tt[4], HEAD, 1 - min(1.0, tt[3] / 35.0)))
        # lightning
        if self.flash <= 0 and self.energy > 0.5 and random.random() < 0.0012:
            self.flash = 5
        if self.flash > 0:
            self.itemconfig(self.flash_item, state="normal", fill="#e7dcff" if self.flash % 2 else "#a98cff")
            self.tag_raise(self.flash_item)
            self.flash -= 1
        else:
            self.itemconfig(self.flash_item, state="hidden")


class AdaptSwitch(tk.Canvas):
    def __init__(self, parent, command):
        super().__init__(parent, width=236, height=46, bg=PANEL_HDR, highlightthickness=0, cursor="hand2", takefocus=1)
        self.on, self.pos, self.t, self.command, self.busy = False, 0.0, 0, command, False
        self.bind("<Button-1>", self.toggle)
        self.bind("<space>", self.toggle)
        self.bind("<Return>", self.toggle)

    def toggle(self, _e=None):
        self.on = not self.on
        self.command(self.on)

    def set(self, on):
        self.on = on

    def tick(self):
        self.t += 1
        self.pos += ((1.0 if self.on else 0.0) - self.pos) * 0.25
        c = self
        c.delete("all")
        p = self.pos
        track = mix("#2a2040", "#6a45d6", p)
        c.create_oval(4, 9, 36, 37, fill=track, outline="")
        c.create_oval(40, 9, 72, 37, fill=track, outline="")
        c.create_rectangle(20, 9, 56, 37, fill=track, outline="")
        kx = 20 + 36 * p
        if self.on:
            r = 17 + 3 * math.sin(self.t * 0.15) + (4 if self.busy else 0)
            c.create_oval(kx - r, 23 - r, kx + r, 23 + r, outline=mix(PANEL_HDR, BRAIN, 0.6), width=2)
        c.create_oval(kx - 11, 12, kx + 11, 34, fill=mix("#8f84ad", "#ffffff", p), outline="")
        c.create_text(84, 15, text="Auto-adapt", anchor="w", font=(FONT, 11, "bold"), fill=BRAIN if self.on else MUTED)
        sub = ("learning rules now" if self.busy else "brain is on") if self.on else "off, rules stay as set"
        c.create_text(84, 32, text=sub, anchor="w", font=(FONT, 9), fill=MUTED)
        if self.focus_get() is self:
            c.create_rectangle(1, 1, 235, 45, outline=ORANGE_H)


class StatTile(tk.Frame):
    def __init__(self, parent, title, footnote=""):
        super().__init__(parent, bg=PANEL, highlightbackground=LINE, highlightthickness=1)
        tk.Label(self, text=title, font=(FONT, 9), fg=MUTED, bg=PANEL, anchor="w").pack(fill="x", padx=14, pady=(10, 0))
        self.val = tk.Label(self, text="--", font=(FONT, 18, "bold"), fg=TEXT, bg=PANEL, anchor="w")
        self.val.pack(fill="x", padx=14)
        tk.Label(self, text=footnote, font=(FONT, 8), fg=MUTED, bg=PANEL, anchor="w").pack(fill="x", padx=14, pady=(0, 8))
        self.target, self.shown, self.kind, self.last = None, 0.0, "money", None

    def set_target(self, value, kind):
        self.kind = kind
        if value is None:
            self.target = None
        else:
            if self.target is None:
                self.shown = value
            self.target = value

    def tick(self):
        if self.target is None:
            text, color = "--", MUTED
        else:
            diff = self.target - self.shown
            self.shown = self.target if abs(diff) < 0.005 else self.shown + diff * 0.2
            v = self.shown
            if self.kind == "money":
                text, color = money(v), money_color(v)
            elif self.kind == "pct":
                text, color = f"{v:.0f}%", TEXT
            else:
                text, color = f"{v:,.0f}", TEXT
        if (text, color) != self.last:
            self.val.config(text=text, fg=color)
            self.last = (text, color)


class CooldownBar(tk.Frame):
    def __init__(self, parent, name):
        super().__init__(parent, bg=PANEL)
        tk.Label(self, text=name, width=6, anchor="w", font=(FONT, 9), fg=MUTED, bg=PANEL).pack(side="left")
        self.cv = tk.Canvas(self, height=6, bg=PANEL2, highlightthickness=0)
        self.cv.pack(side="left", fill="x", expand=True, padx=8)
        self.val = tk.Label(self, text="", width=6, anchor="e", font=(FONT, 9), fg=MUTED, bg=PANEL)
        self.val.pack(side="left")
        self.cv.bind("<Configure>", lambda e: self._paint())
        self.frac, self.state = 0.0, "idle"

    def set(self, remaining, total):
        if remaining is None:
            self.frac, self.state = 0.0, "idle"
            self.val.config(text="", fg=MUTED)
        elif remaining > 0 and total > 0:
            self.frac, self.state = 1 - remaining / total, "busy"
            self.val.config(text=f"{remaining:.0f}s", fg=ORANGE)
        else:
            self.frac, self.state = 1.0, "ready"
            self.val.config(text="ready", fg=SLIME)
        self._paint()

    def _paint(self):
        c = self.cv
        c.delete("all")
        w = c.winfo_width()
        if self.state == "idle" or w < 4:
            return
        c.create_rectangle(0, 0, w * self.frac, 6, fill=ORANGE if self.state == "busy" else "#3c6b3a", outline="")


class StockCard(tk.Frame):
    def __init__(self, parent):
        super().__init__(parent, bg=PANEL, highlightbackground=LINE, highlightthickness=1)
        top = tk.Frame(self, bg=PANEL)
        top.pack(fill="x", padx=20, pady=(16, 0))
        self.title = tk.Label(top, text="No stock selected", font=(FONT, 15, "bold"), fg=ORANGE, bg=PANEL)
        self.title.pack(side="left")
        self.sub = tk.Label(top, text="", font=(FONT, 9), fg=MUTED, bg=PANEL)
        self.sub.pack(side="left", padx=12, pady=(5, 0))
        self.badge = tk.Label(top, text="No position", font=(FONT, 9, "bold"), padx=12, pady=3, bg=PANEL2, fg=MUTED)
        self.badge.pack(side="right")
        self.price = tk.Label(self, text="--", font=(FONT, 36, "bold"), fg=TEXT, bg=PANEL, anchor="w")
        self.price.pack(fill="x", padx=20, pady=(6, 0))
        self.note = tk.Label(self, text="", font=(FONT, 10), fg=MUTED, bg=PANEL, anchor="w", wraplength=380, justify="left")
        self.note.pack(fill="x", padx=20)
        self.cv = tk.Canvas(self, height=80, bg=PANEL, highlightthickness=0)
        self.cv.pack(fill="x", padx=20, pady=(8, 0))
        self.cv.bind("<Configure>", lambda e: self._draw())
        self.g = None
        bars = tk.Frame(self, bg=PANEL)
        bars.pack(fill="x", padx=20, pady=(6, 16))
        self.bars = {}
        for cmd, name in (("buymax.json", "Buy"), ("shortmax.json", "Short"), ("closemax.json", "Close")):
            b = CooldownBar(bars, name)
            b.pack(fill="x", pady=1)
            self.bars[cmd] = b

    def show(self, stock, view, cooldowns, idle_note):
        self.title.config(text=stock or "No stock selected")
        if not view:
            self.sub.config(text="")
        elif view["brain_active"]:
            self.sub.config(text=f"brain levels, generation {view['brain_gen']}", fg=BRAIN)
        else:
            self.sub.config(text="auto levels" if view["auto"] else "manual levels", fg=MUTED)
        if view and view["price"] is not None:
            self.price.config(text=f"${view['price']:,.2f}", fg=TEXT)
        else:
            self.price.config(text="--", fg=MUTED)
        self.note.config(text=view["note"] if view else idle_note)
        owned, shorted = (view["owned"], view["shorted"]) if view else (0, 0)
        if owned:
            self.badge.config(text=f"Long {owned:,} shares", bg=POS_G, fg=SLIME)
        elif shorted:
            self.badge.config(text=f"Short {shorted:,} shares", bg=POS_R, fg=BLOOD)
        else:
            self.badge.config(text="No position", bg=PANEL2, fg=MUTED)
        for cmd, bar in self.bars.items():
            if cooldowns is None:
                bar.set(None, 0)
            else:
                bar.set(*cooldowns[cmd])
        self.g = stock_gauge(view)
        self._draw()

    def _draw(self):
        c, g = self.cv, self.g
        c.delete("all")
        w = c.winfo_width()
        if not g or w < 80:
            return
        price, lo, hi, zones, marks = g
        x0, x1, ty, th = 14, w - 14, 28, 10
        span = (hi - lo) or 1.0

        def X(v):
            return x0 + (x1 - x0) * min(max((v - lo) / span, 0.0), 1.0)

        c.create_rectangle(x0, ty, x1, ty + th, fill=PANEL2, outline="")
        for a, b, col in zones:
            c.create_rectangle(X(a), ty, X(b), ty + th, fill=col, outline="")
        groups = {}
        for v, col, name in marks:
            groups.setdefault(round(v, 4), [col, []])[1].append(name)
        for v, (col, names) in groups.items():
            x = X(v)
            lx = min(max(x, 34), w - 34)
            c.create_line(x, ty - 3, x, ty + th + 3, fill=col, width=2)
            c.create_text(lx, ty + th + 9, text="/".join(names), fill=MUTED, font=(FONT, 8), anchor="n")
            c.create_text(lx, ty + th + 23, text=f"${v:,.2f}", fill=TEXT, font=(FONT, 9), anchor="n")
        if price is not None:
            xp = X(price)
            c.create_line(xp, ty - 4, xp, ty + th + 3, fill=ORANGE, width=2)
            c.create_polygon(xp - 6, ty - 17, xp + 6, ty - 17, xp, ty - 5, fill=ORANGE, outline="")


def stock_gauge(view):
    if not view:
        return None
    L, price, marks = view["levels"], view["price"], []
    if L:
        marks += [(L["buy_at"], SLIME, "Buy"), (L["close_at"], BLOOD, "Close")]
        if L["stop_loss"] is not None:
            marks.append((L["stop_loss"], BLOOD, "Stop"))
        if L["short_enabled"]:
            marks += [(L["cover_at"], SLIME, "Cover"), (L["short_at"], BLOOD, "Short")]
            if L["short_stop"] is not None:
                marks.append((L["short_stop"], BLOOD, "Short stop"))
    if view.get("crash"):
        marks += [(view["crash"][0], SLIME, "Crash buy"), (view["crash"][1], BLOOD, "Crash short")]
    vals = [v for v, _, _ in marks] + ([price] if price is not None else [])
    if not vals:
        return None
    lo, hi = min(vals), max(vals)
    span = (hi - lo) or hi or 1.0
    lo, hi = max(0.0, lo - span * 0.15), hi + span * 0.15
    zones = [(lo, L["buy_at"], ZONE_G), (L["close_at"], hi, ZONE_R)] if L else []
    return price, lo, hi, zones, marks


def draw_spark(c, vals, w, h, color):
    c.delete("all")
    if len(vals) < 2:
        return
    lo, hi = min(vals), max(vals)
    span = (hi - lo) or 1.0
    pts = []
    for i, v in enumerate(vals):
        pts += [2 + (w - 4) * i / (len(vals) - 1), h - 3 - (h - 6) * (v - lo) / span]
    c.create_line(*pts, fill=color, width=2)
    c.create_oval(pts[-2] - 2.5, pts[-1] - 2.5, pts[-2] + 2.5, pts[-1] + 2.5, fill=ORANGE, outline="")


class StockRow(tk.Frame):
    def __init__(self, parent, stock, on_click):
        super().__init__(parent, bg=PANEL, cursor="hand2")
        self.stock, self.sel, self.hover, self.accent = stock, False, False, PANEL
        self.bar = tk.Frame(self, width=5, bg=PANEL)
        self.bar.pack(side="left", fill="y")
        body = tk.Frame(self, bg=PANEL)
        body.pack(side="left", fill="x", expand=True, padx=(10, 12), pady=8)
        body.columnconfigure(0, weight=1)
        namebox = tk.Frame(body, bg=PANEL)
        self.name = tk.Label(namebox, text=stock, font=(FONT, 12, "bold"), fg=ORANGE, bg=PANEL, anchor="w")
        self.ai = tk.Label(namebox, text="", font=(FONT, 8, "bold"), fg=BRAIN, bg=PANEL)
        self.name.pack(side="left")
        self.ai.pack(side="left", padx=(8, 0))
        self.note = tk.Label(body, text="", font=(FONT, 9), fg=MUTED, bg=PANEL, anchor="w")
        self.spark = tk.Canvas(body, width=92, height=30, bg=PANEL, highlightthickness=0)
        self.price = tk.Label(body, text="--", font=(FONT, 12, "bold"), fg=TEXT, bg=PANEL, anchor="e")
        self.pnl = tk.Label(body, text="", font=(FONT, 9), fg=MUTED, bg=PANEL, anchor="e")
        namebox.grid(row=0, column=0, sticky="w")
        self.note.grid(row=1, column=0, sticky="w")
        self.spark.grid(row=0, column=1, rowspan=2, padx=10)
        self.price.grid(row=0, column=2, sticky="e")
        self.pnl.grid(row=1, column=2, sticky="e")
        self.parts = [self, body, namebox, self.name, self.ai, self.note, self.price, self.pnl, self.spark]
        for w in self.parts + [self.bar]:
            w.bind("<Button-1>", lambda e, s=stock: on_click(s))
            w.bind("<Enter>", lambda e: self._hover(True))
            w.bind("<Leave>", lambda e: self._hover(False))

    def _hover(self, on):
        self.hover = on
        self._paint()

    def _paint(self):
        bg = PURPLE_D if self.sel else "#281a40" if self.hover else PANEL
        for w in self.parts:
            w.config(bg=bg)
        self.bar.config(bg=self.accent)

    def update_view(self, view):
        if view:
            self.price.config(text=f"${view['price']:,.2f}" if view["price"] is not None else "--")
            shown = view["note"]
            self.note.config(text=shown if len(shown) < 34 else shown[:33] + "…")
            self.pnl.config(text=money(view["realized"]), fg=money_color(view["realized"]))
            self.accent = SLIME if view["owned"] else BLOOD if view["shorted"] else PANEL
            self.ai.config(text=f"AI g{view['brain_gen']}" if view["brain_active"] else "")
            draw_spark(self.spark, view["spark"], 92, 30, MUTED)
        else:
            self.price.config(text="--")
            self.note.config(text="")
            self.pnl.config(text="")
            self.ai.config(text="")
            self.accent = PANEL
            self.spark.delete("all")
        self._paint()

    def set_selected(self, sel):
        self.sel = sel
        self._paint()


class StockList(tk.Frame):
    def __init__(self, parent, on_select):
        super().__init__(parent, bg=PANEL, highlightbackground=LINE, highlightthickness=1)
        self.on_select, self.rows, self.selected = on_select, {}, None
        head = tk.Frame(self, bg=PANEL)
        head.pack(fill="x", padx=16, pady=(14, 8))
        tk.Label(head, text="Stocks", font=(FONT, 15, "bold"), fg=ORANGE, bg=PANEL).pack(side="left")
        self.count = tk.Label(head, text="", font=(FONT, 9), fg=MUTED, bg=PANEL)
        self.count.pack(side="left", padx=10, pady=(5, 0))
        self.filter = tk.StringVar()
        self.filter.trace_add("write", lambda *a: self.layout())
        tk.Entry(head, textvariable=self.filter, width=12, font=(FONT, 10), bg=PANEL2, fg=ORANGE,
                 insertbackground=ORANGE, relief="flat", highlightthickness=1, highlightbackground=LINE,
                 highlightcolor=ORANGE).pack(side="right", ipady=3)
        self.cv = tk.Canvas(self, bg=LINE, highlightthickness=0)
        self.cv.pack(fill="both", expand=True)
        self.inner = tk.Frame(self.cv, bg=LINE)
        self.win = self.cv.create_window(0, 0, window=self.inner, anchor="nw")
        self.inner.bind("<Configure>", lambda e: self.cv.configure(scrollregion=self.cv.bbox("all")))
        self.cv.bind("<Configure>", lambda e: self.cv.itemconfig(self.win, width=e.width))
        self.cv.bind("<Enter>", lambda e: self.cv.bind_all("<MouseWheel>", self._wheel))
        self.cv.bind("<Leave>", lambda e: self.cv.unbind_all("<MouseWheel>"))

    def _wheel(self, e):
        self.cv.yview_scroll(int(-e.delta / 120), "units")

    def set_stocks(self, stocks):
        if set(stocks) == set(self.rows):
            return
        for s in list(self.rows):
            if s not in stocks:
                self.rows.pop(s).destroy()
        for s in stocks:
            if s not in self.rows:
                self.rows[s] = StockRow(self.inner, s, self.on_select)
        self.layout()

    def layout(self):
        q = self.filter.get().strip().lower()
        for r in self.rows.values():
            r.pack_forget()
        for s in [s for s in sorted(self.rows) if q in s.lower()]:
            self.rows[s].pack(fill="x", pady=1)
        self.count.config(text=f"{len(self.rows)} found")
        if self.selected in self.rows:
            self.rows[self.selected].set_selected(True)

    def select(self, stock):
        if self.selected in self.rows:
            self.rows[self.selected].set_selected(False)
        self.selected = stock
        if stock in self.rows:
            self.rows[stock].set_selected(True)


class RuleForm(tk.Frame):
    def __init__(self, parent, fields):
        super().__init__(parent, bg=PANEL)
        self.fields, self.vars = fields, {}
        self.columnconfigure(0, weight=1)
        for r, (key, text, kind) in enumerate(fields):
            if kind == "check":
                v = tk.BooleanVar()
                tk.Checkbutton(self, text=text, variable=v, bg=PANEL, fg=TEXT, activebackground=PANEL,
                               activeforeground=TEXT, selectcolor=PANEL2, bd=0, highlightthickness=0,
                               font=(FONT, 10), anchor="w").grid(row=r, column=0, columnspan=2, sticky="w", pady=1)
            else:
                v = tk.StringVar()
                tk.Label(self, text=text, font=(FONT, 10), fg=TEXT, bg=PANEL, anchor="w").grid(row=r, column=0, sticky="w", pady=2)
                tk.Entry(self, textvariable=v, width=9, justify="right", font=(FONT, 10), bg=PANEL2, fg=ORANGE,
                         insertbackground=ORANGE, relief="flat", highlightthickness=1, highlightbackground=LINE,
                         highlightcolor=ORANGE).grid(row=r, column=1, sticky="e", padx=(12, 0), ipady=2)
            self.vars[key] = v

    def load(self, data):
        for key, _, kind in self.fields:
            val = data.get(key)
            if kind == "check":
                self.vars[key].set(bool(val))
            elif val is None:
                self.vars[key].set("")
            else:
                self.vars[key].set(f"{val:g}" if isinstance(val, (int, float)) else str(val))

    def read(self):
        out = {}
        for key, text, kind in self.fields:
            raw = self.vars[key].get()
            if kind == "check":
                out[key] = bool(raw)
            elif kind == "time":
                try:
                    parse_hm(raw)
                except ValueError:
                    raise ValueError(f"{text} needs a time like 17:50")
                out[key] = str(raw).strip()
            else:
                s = str(raw).strip().replace("$", "").replace(",", "")
                if s == "" and kind == "opt":
                    out[key] = None
                    continue
                try:
                    n = float(s)
                except ValueError:
                    raise ValueError(f"{text} needs a number")
                if n < 0:
                    raise ValueError(f"{text} can't be negative")
                out[key] = n
        return out


STOCK_FIELDS = [
    ("enabled", "Trade this stock", "check"),
    ("brain_lock", "Lock rules (the brain hands off)", "check"),
    ("auto", "Auto-calibrate levels from price history", "check"),
    ("buy_at", "Buy at or below", "opt"),
    ("close_at", "Close at or above", "opt"),
    ("stop_loss", "Stop loss (blank is off)", "opt"),
    ("short_enabled", "Allow shorting", "check"),
    ("short_at", "Short at or above", "opt"),
    ("cover_at", "Cover at or below", "opt"),
    ("short_stop", "Short stop (blank is off)", "opt"),
    ("crash_enabled", "Crash window rules", "check"),
    ("crash_short", "Crash short above", "opt"),
    ("crash_buy", "Crash buy below", "opt"),
    ("crash_start", "Window starts (UTC)", "time"),
    ("crash_end", "Window ends (UTC)", "time"),
]
SETTINGS_A = [
    ("dry_run", "Dry run (log signals, send no orders)", "check"),
    ("max_positions", "Max open positions (0 is no limit)", "num"),
    ("daily_target", "Daily profit target (blank is off)", "opt"),
    ("daily_loss", "Daily loss limit (blank is off)", "opt"),
    ("auto_buy_pct", "Auto: buy in the lowest % of range", "num"),
    ("auto_close_pct", "Auto: close in the highest % of range", "num"),
    ("auto_warmup", "Auto: price samples before trading", "num"),
    ("auto_min_range", "Auto: smallest range % worth trading", "num"),
    ("auto_stop_pct", "Auto: stop loss % (blank is off)", "opt"),
    ("auto_trail_pct", "Auto: trailing stop % (blank is off)", "opt"),
    ("auto_short", "Auto: allow shorting", "check"),
]
SETTINGS_B = [
    ("sounds", "Sound effects (Windows)", "check"),
    ("brain_min_samples", "Brain: price samples before learning", "num"),
    ("brain_interval", "Brain: seconds between tuning rounds", "num"),
    ("brain_fee_pct", "Brain: assumed cost per trade, %", "num"),
    ("brain_min_conf", "Brain: min confidence to use (0 to 1)", "num"),
    ("brain_standdown", "Brain: skip stocks where it finds no edge", "check"),
]


# ================= GUI: CHARTS AND BRAIN VISUALS =================
def thin(vals, limit=220):
    if len(vals) <= limit:
        return vals
    step = len(vals) / float(limit)
    return [vals[int(i * step)] for i in range(limit - 1)] + [vals[-1]]


class EquityChart(tk.Canvas):
    def __init__(self, parent):
        super().__init__(parent, bg=PANEL, highlightthickness=0)
        self.vals, self.dot, self.pt, self.t = [0.0], None, None, 0
        self.bind("<Configure>", lambda e: self.draw())

    def set(self, vals):
        if vals != self.vals:
            self.vals = vals
            self.draw()

    def draw(self):
        c = self
        c.delete("all")
        self.dot, self.pt = None, None
        w, h = c.winfo_width(), c.winfo_height()
        if w < 120 or h < 100:
            return
        if len(self.vals) < 3:
            c.create_text(w / 2, h / 2, text="Your income curve appears after the first closed trades",
                          fill=MUTED, font=(FONT, 11))
            return
        vals = thin(self.vals)
        pl, pr, pt, pb = 64, 26, 20, 28
        lo, hi = min(min(vals), 0.0), max(max(vals), 0.0)
        span = (hi - lo) or 1.0
        lo, hi = lo - span * 0.08, hi + span * 0.08
        n = len(vals)

        def X(i):
            return pl + (w - pl - pr) * i / (n - 1)

        def Y(v):
            return pt + (h - pt - pb) * (1 - (v - lo) / (hi - lo))

        for k in range(5):
            v = lo + (hi - lo) * k / 4
            y = Y(v)
            c.create_line(pl, y, w - pr, y, fill=LINE if abs(v) > (hi - lo) * 0.01 else "#5a3d85", dash=(2, 4))
            c.create_text(pl - 8, y, text=money(v, False), anchor="e", fill=MUTED, font=(FONT, 8))
        pts = []
        for i, v in enumerate(vals):
            pts += [X(i), Y(v)]
        c.create_polygon(pts + [X(n - 1), Y(0), X(0), Y(0)], fill=mix(PANEL, ORANGE, 0.16), outline="")
        c.create_line(*pts, fill=mix(PANEL, ORANGE, 0.35), width=8, smooth=True)
        c.create_line(*pts, fill=ORANGE, width=2, smooth=True)
        self.pt = (X(n - 1), Y(vals[-1]))
        last = vals[-1]
        c.create_text(min(self.pt[0], w - 40), max(self.pt[1] - 18, 12), text=money(last), fill=money_color(last),
                      font=(FONT, 11, "bold"), anchor="e" if self.pt[0] > w * 0.7 else "w")

    def tick(self):
        self.t += 1
        if not self.pt:
            return
        r = 5 + 2.5 * math.sin(self.t * 0.18)
        x, y = self.pt
        if self.dot is None:
            self.dot = self.create_oval(x - r, y - r, x + r, y + r, fill=SLIME, outline="")
        else:
            self.coords(self.dot, x - r, y - r, x + r, y + r)


class Leaderboard(tk.Canvas):
    def __init__(self, parent):
        super().__init__(parent, bg=PANEL, highlightthickness=0)
        self.rows = []
        self.bind("<Configure>", lambda e: self.draw())

    def set(self, rows):
        if rows != self.rows:
            self.rows = rows
            self.draw()

    def draw(self):
        c = self
        c.delete("all")
        w, h = c.winfo_width(), c.winfo_height()
        if w < 100:
            return
        if not self.rows:
            c.create_text(w / 2, 40, text="No closed trades yet", fill=MUTED, font=(FONT, 10))
            return
        top = max(abs(v) for _, v in self.rows) or 1.0
        for i, (name, v) in enumerate(self.rows):
            y = 14 + i * 34
            c.create_text(12, y + 9, text=name, anchor="w", fill=TEXT, font=(FONT, 10, "bold"))
            bw = (w - 220) * abs(v) / top
            c.create_rectangle(104, y + 2, 104 + max(bw, 3), y + 16, fill=POS_G if v >= 0 else POS_R, outline="")
            c.create_rectangle(104, y + 2, 108, y + 16, fill=SLIME if v >= 0 else BLOOD, outline="")
            c.create_text(w - 12, y + 9, text=money(v), anchor="e", fill=money_color(v), font=(FONT, 10))


def draw_curves(c, series, labels=()):
    c.delete("all")
    w, h = c.winfo_width(), c.winfo_height()
    if w < 100 or h < 60:
        return
    allv = [v for vals, _, _ in series for v in vals]
    if len(allv) < 4:
        c.create_text(w / 2, h / 2, text="The simulation appears after the brain's first generation",
                      fill=MUTED, font=(FONT, 10))
        return
    lo, hi = min(allv), max(allv)
    span = (hi - lo) or 1.0
    pl, pr, pt, pb = 46, 14, 14, 18
    for k in range(4):
        v = lo + span * k / 3
        y = pt + (h - pt - pb) * (1 - k / 3)
        c.create_line(pl, y, w - pr, y, fill=LINE, dash=(2, 4))
        c.create_text(pl - 6, y, text=f"{(v - 1) * 100:+.0f}%", anchor="e", fill=MUTED, font=(FONT, 8))
    for vals, color, width in series:
        n = len(vals)
        if n < 2:
            continue
        pts = []
        for i, v in enumerate(vals):
            pts += [pl + (w - pl - pr) * i / (n - 1), pt + (h - pt - pb) * (1 - (v - lo) / span)]
        c.create_line(*pts, fill=color, width=width, smooth=True)
    x = w - pr
    for text, color in labels:
        c.create_text(x, h - 4, text=text, anchor="se", fill=color, font=(FONT, 9))
        x -= 150


class NetViz(tk.Canvas):
    LAYERS = (5, 7, 6, 3)
    COLORS = (ORANGE, BRAIN, BRAIN, SLIME)
    TITLES = ("Prices", "Levels", "Rules", "Orders")

    def __init__(self, parent):
        super().__init__(parent, bg=PANEL, highlightthickness=0)
        self.nodes, self.links, self.pulses, self.act, self.mode, self.t = [], [], [], {}, "off", 0
        self.bind("<Configure>", lambda e: self.build())

    def build(self):
        self.delete("all")
        self.nodes, self.links, self.pulses, self.act = [], [], [], {}
        w, h = self.winfo_width(), self.winfo_height()
        if w < 200 or h < 100:
            return
        xs = [w * f for f in (0.12, 0.38, 0.64, 0.88)]
        pos = []
        for li, n in enumerate(self.LAYERS):
            col = []
            for i in range(n):
                col.append((xs[li], 34 + (h - 54) * (i + 0.5) / n))
            pos.append(col)
        self.pos = pos
        for li in range(len(pos) - 1):
            for a in pos[li]:
                for b in pos[li + 1]:
                    self.create_line(a[0], a[1], b[0], b[1], fill="#2a1d46")
        for li, col in enumerate(pos):
            self.create_text(xs[li], 14, text=self.TITLES[li], fill=MUTED, font=(FONT, 9))
            row = []
            for (x, y) in col:
                row.append(self.create_oval(x - 7, y - 7, x + 7, y + 7, fill=PANEL2, outline=self.COLORS[li], width=2))
            self.nodes.append(row)

    def tick(self, mode, conf):
        self.mode, self.t = mode, self.t + 1
        if not self.nodes:
            return
        rate = {"off": 0.0, "on": 0.07, "busy": 0.55}.get(mode, 0.0)
        if random.random() < rate and len(self.pulses) < 40:
            i = random.randrange(self.LAYERS[0])
            self.pulses.append([0, i, random.randrange(self.LAYERS[1]), 0.0, self.create_oval(0, 0, 1, 1, fill=ORANGE, outline="")])
        for p in self.pulses[:]:
            li, i, j, prog, it = p
            p[3] += 0.045
            a, b = self.pos[li][i], self.pos[li + 1][j]
            x, y = a[0] + (b[0] - a[0]) * p[3], a[1] + (b[1] - a[1]) * p[3]
            self.coords(it, x - 3, y - 3, x + 3, y + 3)
            self.itemconfig(it, fill=self.COLORS[li + 1])
            if p[3] >= 1.0:
                self.act[(li + 1, j)] = 1.0
                self.delete(it)
                self.pulses.remove(p)
                if li + 2 < len(self.LAYERS) and random.random() < 0.85:
                    self.pulses.append([li + 1, j, random.randrange(self.LAYERS[li + 2]), 0.0,
                                        self.create_oval(0, 0, 1, 1, fill=self.COLORS[li + 1], outline="")])
        for (li, i), v in list(self.act.items()):
            self.itemconfig(self.nodes[li][i], fill=mix(PANEL2, self.COLORS[li], v))
            self.act[(li, i)] = v - 0.06
            if self.act[(li, i)] <= 0:
                del self.act[(li, i)]
                self.itemconfig(self.nodes[li][i], fill=PANEL2)
        if mode != "off" and self.nodes:
            glow = 0.35 + 0.35 * conf + 0.2 * math.sin(self.t * 0.12)
            for it in self.nodes[-1]:
                self.itemconfig(it, outline=mix(SLIME, "#ffffff", max(0.0, glow - 0.5)))


class BrainPanel(tk.Frame):
    def __init__(self, parent, on_reset_stock, on_reset_all):
        super().__init__(parent, bg=BG)
        self.columnconfigure(0, weight=3)
        self.columnconfigure(1, weight=2, minsize=340)
        self.rowconfigure(0, weight=1)
        left = tk.Frame(self, bg=BG)
        left.grid(row=0, column=0, sticky="nsew", padx=(0, 14))
        left.rowconfigure(0, weight=3)
        left.rowconfigure(1, weight=2)
        left.columnconfigure(0, weight=1)
        netcard = tk.Frame(left, bg=PANEL, highlightbackground=LINE, highlightthickness=1)
        netcard.grid(row=0, column=0, sticky="nsew", pady=(0, 14))
        tk.Label(netcard, text="The brain", font=(FONT, 13, "bold"), fg=BRAIN, bg=PANEL).pack(anchor="w", padx=18, pady=(12, 0))
        self.net = NetViz(netcard)
        self.net.pack(fill="both", expand=True, padx=10, pady=(0, 8))
        simcard = tk.Frame(left, bg=PANEL, highlightbackground=LINE, highlightthickness=1)
        simcard.grid(row=1, column=0, sticky="nsew")
        tk.Label(simcard, text="Replay: learned rules versus just holding", font=(FONT, 11, "bold"), fg=BRAIN,
                 bg=PANEL).pack(anchor="w", padx=18, pady=(12, 0))
        self.sim = tk.Canvas(simcard, bg=PANEL, highlightthickness=0)
        self.sim.pack(fill="both", expand=True, padx=10, pady=(0, 8))
        self.sim.bind("<Configure>", lambda e: self._redraw_sim())
        self._sim_data = None

        right = tk.Frame(self, bg=PANEL, highlightbackground=LINE, highlightthickness=1)
        right.grid(row=0, column=1, sticky="nsew")
        self.title = tk.Label(right, text="No stock selected", font=(FONT, 14, "bold"), fg=ORANGE, bg=PANEL)
        self.title.pack(anchor="w", padx=18, pady=(14, 4))
        ringrow = tk.Frame(right, bg=PANEL)
        ringrow.pack(fill="x", padx=18)
        self.ring = tk.Canvas(ringrow, width=96, height=96, bg=PANEL, highlightthickness=0)
        self.ring.pack(side="left")
        facts = tk.Frame(ringrow, bg=PANEL)
        facts.pack(side="left", padx=14, fill="x", expand=True)
        self.facts = []
        for _ in range(4):
            lb = tk.Label(facts, text="", font=(FONT, 10), fg=TEXT, bg=PANEL, anchor="w")
            lb.pack(fill="x")
            self.facts.append(lb)
        self.status = tk.Label(right, text="", font=(FONT, 10), fg=MUTED, bg=PANEL, wraplength=300, justify="left", anchor="w")
        self.status.pack(fill="x", padx=18, pady=(10, 4))
        self.rules = tk.Label(right, text="", font=(FONT, 10), fg=BRAIN, bg=PANEL, wraplength=300, justify="left", anchor="w")
        self.rules.pack(fill="x", padx=18, pady=(0, 8))
        tk.Label(right, text="Evolution feed", font=(FONT, 11, "bold"), fg=BRAIN, bg=PANEL).pack(anchor="w", padx=18)
        self.feed = tk.Text(right, bg=PANEL2, fg=MUTED, relief="flat", bd=0, wrap="word", font=(FONT, 9), padx=10, pady=8,
                            state="disabled", height=8, highlightthickness=0)
        self.feed.pack(fill="both", expand=True, padx=18, pady=(4, 8))
        self.feed.tag_config("brain", foreground=MUTED)
        self.feed.tag_config("brain_up", foreground=BRAIN)
        btns = tk.Frame(right, bg=PANEL)
        btns.pack(fill="x", padx=18, pady=(0, 16))
        Btn(btns, "Reset this stock", on_reset_stock, PURPLE_D, ORANGE, PURPLE_H).pack(side="left", padx=(0, 8))
        Btn(btns, "Reset all", on_reset_all, POS_R, BLOOD, "#6b2838").pack(side="left")
        self.conf = 0.0

    def add_feed(self, ts, level, msg):
        w = self.feed
        w.config(state="normal")
        w.insert("end", f"{ts}  {msg}\n\n", level)
        if int(float(w.index("end-1c"))) > 160:
            w.delete("1.0", "20.0")
        w.see("end")
        w.config(state="disabled")

    def _redraw_sim(self):
        if self._sim_data is None:
            draw_curves(self.sim, [])
        else:
            curve, hold = self._sim_data
            draw_curves(self.sim, [(hold, MUTED, 2), (curve, BRAIN, 3)], [("Learned rules", BRAIN), ("Buy and hold", MUTED)])

    def update_info(self, stock, S, st, samples, locked, adapt, busy):
        self.title.config(text=stock or "No stock selected")
        need = int(st.get("brain_min_samples") or 240)
        for lb in self.facts:
            lb.config(text="")
        self.conf = S.get("conf", 0.0) if S else 0.0
        data = None
        if not stock:
            msg, rules = "Pick a stock in the list.", ""
        elif locked:
            msg, rules = "Rules are locked for this stock, so the brain hands off.", ""
        elif not adapt:
            msg, rules = "Auto-adapt is off. Flip the switch in the header to let the brain tune this stock.", ""
        elif samples < need:
            msg, rules = f"Collecting prices, {samples} of {need}. Learning starts at {need} samples (one every 10 seconds).", ""
        elif not S or not S.get("params"):
            msg = "No rule set has made money on unseen prices yet. The brain keeps mutating and trying new ones."
            rules = ""
        else:
            ev = S["ev"]
            trusted = self.conf >= float(st.get("brain_min_conf") or 0)
            msg = (f"Generation {S['gen']} after {S.get('rounds', 0)} rounds. "
                   + ("Trading with the learned rules." if trusted else "Not trusted yet, trading with your base rules."))
            rules = describe_params(S["params"])
            self.facts[0].config(text=f"Generation {S['gen']}", fg=BRAIN)
            self.facts[1].config(text=f"Training return {ev['tr'][0] * 100:+.1f}%", fg=money_color(ev['tr'][0]))
            self.facts[2].config(text=f"Unseen-data return {ev['te'][0] * 100:+.1f}%", fg=money_color(ev['te'][0]))
            self.facts[3].config(text=f"Replay trades {ev['tr'][2] + ev['te'][2]}", fg=MUTED)
            if S.get("curve") and S.get("hold"):
                data = (S["curve"], S["hold"])
        self.status.config(text=msg)
        self.rules.config(text=rules)
        if data != self._sim_data:
            self._sim_data = data
            self._redraw_sim()
        self.mode = "busy" if busy else ("on" if adapt else "off")

    mode = "off"

    def tick(self, t):
        self.net.tick(self.mode, self.conf)
        c = self.ring
        c.delete("all")
        c.create_oval(10, 10, 86, 86, outline=PANEL2, width=9)
        if self.conf > 0:
            c.create_arc(10, 10, 86, 86, start=90, extent=-359.9 * self.conf, style="arc", outline=BRAIN, width=9)
        c.create_text(48, 44, text=f"{self.conf * 100:.0f}%", fill=TEXT, font=(FONT, 15, "bold"))
        c.create_text(48, 63, text="confidence", fill=MUTED, font=(FONT, 8))


# ================= APP =================
class App(tk.Tk):
    TABS = ("Overview", "Stock", "Brain", "Settings", "Trades", "Activity")

    def __init__(self):
        super().__init__()
        self.withdraw()
        global DISPLAY_FONT
        DISPLAY_FONT = pick_font(["Chiller", "Jokerman", "Gabriola", "Segoe Script"], "Georgia")
        self.title("Screen Stocks Trader, Haunted AI edition")
        self.configure(bg=BG)
        self.geometry("1380x940")
        self.minsize(1200, 800)

        self.cfg = load_config()
        if not self.cfg["username"]:
            name = simpledialog.askstring("Screen Stocks Trader", "Enter your Windows username:",
                                          initialvalue=os.environ.get("USERNAME", ""), parent=self)
            if not name or not name.strip():
                self.destroy()
                raise SystemExit
            self.cfg["username"] = name.strip()
            save_config(self.cfg)
        self.base = game_base(self.cfg["username"])
        self.ledger, self.history = Ledger(), History()
        self.log_q = queue.Queue()
        self.brain = Brain(self.cfg, self.history, self.log_q)
        self.brain.start()
        self.engine = None
        self.selected, self._found_at, self._trades_n, self._seen_trades = None, 0.0, -1, None
        self.cur_tab = "Overview"

        self._build()
        self.protocol("WM_DELETE_WINDOW", self._close)
        self.refresh_stocks(True)
        self.settings_a.load(self.cfg["settings"])
        self.settings_b.load(self.cfg["settings"])
        self.switch.set(bool(self.cfg["settings"].get("adapt")))
        self.deiconify()
        self.poll()
        self.anim()

    # ---------- layout ----------
    def _build(self):
        self.header = AnimatedHeader(self)
        self.header.pack(fill="x")
        panel = tk.Frame(self.header, bg=PANEL_HDR, highlightbackground=LINE, highlightthickness=1)
        panel.place(relx=1.0, x=-20, rely=0.5, anchor="e")
        row1 = tk.Frame(panel, bg=PANEL_HDR)
        row1.pack(fill="x", padx=14, pady=(12, 6))
        self.switch = AdaptSwitch(row1, self.set_adapt)
        self.switch.pack(side="left")
        self.status = tk.Label(row1, text="Stopped", font=(FONT, 10, "bold"), width=22, pady=6, bg=PURPLE_D, fg=MUTED)
        self.status.pack(side="left", padx=(14, 0))
        row2 = tk.Frame(panel, bg=PANEL_HDR)
        row2.pack(fill="x", padx=14, pady=(0, 12))
        self.toggle = Btn(row2, "Start trading", self.toggle_engine, ORANGE, HEAD, ORANGE_H)
        self.toggle.pack(side="right")
        Btn(row2, "Close all", self.close_all, POS_R, BLOOD, "#6b2838").pack(side="right", padx=(0, 8))
        self.pause_btn = Btn(row2, "Pause entries", self.toggle_pause, PURPLE_D, ORANGE, PURPLE_H)
        self.pause_btn.pack(side="right", padx=(0, 8))

        strip = tk.Frame(self, bg=BG)
        strip.pack(fill="x", padx=20, pady=(16, 0))
        self.tiles = {}
        for i, (key, title, foot) in enumerate([
                ("today", "Today", "resets at midnight"), ("total", "Total realized", "since tracking began"),
                ("open", "Open P&L", "estimated, live"), ("avg_trade", "Avg per trade", ""),
                ("avg_hour", "Avg per hour", "of running time"), ("win", "Win rate", ""), ("n", "Closed trades", "")]):
            strip.columnconfigure(i, weight=1, uniform="t")
            t = StatTile(strip, title, foot)
            t.grid(row=0, column=i, sticky="ew", padx=(0 if i == 0 else 8, 0))
            self.tiles[key] = t

        body = tk.Frame(self, bg=BG)
        body.pack(fill="both", expand=True, padx=20, pady=16)
        body.columnconfigure(1, weight=1)
        body.rowconfigure(0, weight=1)
        self.stock_list = StockList(body, self.select)
        self.stock_list.grid(row=0, column=0, sticky="ns", padx=(0, 16))
        self.stock_list.config(width=400)
        self.stock_list.pack_propagate(False)

        right = tk.Frame(body, bg=BG)
        right.grid(row=0, column=1, sticky="nsew")
        right.rowconfigure(1, weight=1)
        right.columnconfigure(0, weight=1)
        tabs = tk.Frame(right, bg=BG)
        tabs.grid(row=0, column=0, sticky="w", pady=(0, 10))
        self.tab_btns, self.tab_frames = {}, {}
        for name in self.TABS:
            b = Btn(tabs, name, lambda n=name: self.show_tab(n), PANEL, MUTED, PURPLE_D)
            b.pack(side="left", padx=(0, 6))
            self.tab_btns[name] = b
            f = tk.Frame(right, bg=BG)
            f.grid(row=1, column=0, sticky="nsew")
            self.tab_frames[name] = f

        # Overview
        ov = self.tab_frames["Overview"]
        ov.columnconfigure(0, weight=3)
        ov.columnconfigure(1, weight=2, minsize=320)
        ov.rowconfigure(0, weight=1)
        eqc = tk.Frame(ov, bg=PANEL, highlightbackground=LINE, highlightthickness=1)
        eqc.grid(row=0, column=0, sticky="nsew", padx=(0, 14))
        tk.Label(eqc, text="Income curve", font=(FONT, 13, "bold"), fg=ORANGE, bg=PANEL).pack(anchor="w", padx=18, pady=(12, 0))
        tk.Label(eqc, text="Running total of realized profit, one point per closed trade", font=(FONT, 9), fg=MUTED,
                 bg=PANEL).pack(anchor="w", padx=18)
        self.equity = EquityChart(eqc)
        self.equity.pack(fill="both", expand=True, padx=8, pady=(4, 8))
        side = tk.Frame(ov, bg=BG)
        side.grid(row=0, column=1, sticky="nsew")
        side.rowconfigure(0, weight=1)
        side.rowconfigure(1, weight=1)
        side.columnconfigure(0, weight=1)
        lbc = tk.Frame(side, bg=PANEL, highlightbackground=LINE, highlightthickness=1)
        lbc.grid(row=0, column=0, sticky="nsew", pady=(0, 14))
        tk.Label(lbc, text="Top earners", font=(FONT, 13, "bold"), fg=ORANGE, bg=PANEL).pack(anchor="w", padx=18, pady=(12, 0))
        self.board = Leaderboard(lbc)
        self.board.pack(fill="both", expand=True, padx=6, pady=(4, 8))
        opc = tk.Frame(side, bg=PANEL, highlightbackground=LINE, highlightthickness=1)
        opc.grid(row=1, column=0, sticky="nsew")
        tk.Label(opc, text="Open positions", font=(FONT, 13, "bold"), fg=ORANGE, bg=PANEL).pack(anchor="w", padx=18, pady=(12, 0))
        self.open_w = self._text(opc, mono=True, border=False)

        # Stock tab
        sf = self.tab_frames["Stock"]
        sf.columnconfigure(0, weight=1)
        sf.columnconfigure(1, minsize=340)
        sf.rowconfigure(0, weight=1)
        self.card = StockCard(sf)
        self.card.grid(row=0, column=0, sticky="new", padx=(0, 16))
        rf = tk.Frame(sf, bg=PANEL, highlightbackground=LINE, highlightthickness=1)
        rf.grid(row=0, column=1, sticky="new")
        tk.Label(rf, text="Rules for this stock", font=(FONT, 13, "bold"), fg=ORANGE, bg=PANEL).pack(anchor="w", padx=20, pady=(14, 6))
        self.stock_form = RuleForm(rf, STOCK_FIELDS)
        self.stock_form.pack(fill="x", padx=20)
        self.stock_err = tk.Label(rf, text="", font=(FONT, 9), fg=BLOOD, bg=PANEL, wraplength=300, justify="left", anchor="w")
        self.stock_err.pack(fill="x", padx=20, pady=(8, 0))
        Btn(rf, "Save rules", self.save_stock, PURPLE_D, ORANGE, PURPLE_H).pack(fill="x", padx=20, pady=(6, 16))

        # Brain tab
        self.brain_panel = BrainPanel(self.tab_frames["Brain"], self.reset_brain_stock, self.reset_brain_all)
        self.brain_panel.pack(fill="both", expand=True)

        # Settings tab
        gf = self.tab_frames["Settings"]
        gf.columnconfigure(0, weight=1)
        gf.columnconfigure(1, weight=1)
        box = tk.Frame(gf, bg=PANEL, highlightbackground=LINE, highlightthickness=1)
        box.grid(row=0, column=0, sticky="new", padx=(0, 14))
        tk.Label(box, text="Risk and auto levels", font=(FONT, 13, "bold"), fg=ORANGE, bg=PANEL).pack(anchor="w", padx=20, pady=(14, 2))
        tk.Label(box, text="Auto stocks learn levels from the prices seen while the trader runs (one sample every 10 seconds). "
                           "Stocks with manual levels ignore the auto settings.", font=(FONT, 9), fg=MUTED, bg=PANEL,
                 wraplength=420, justify="left", anchor="w").pack(fill="x", padx=20, pady=(0, 10))
        self.settings_a = RuleForm(box, SETTINGS_A)
        self.settings_a.pack(fill="x", padx=20, pady=(0, 16))
        box2 = tk.Frame(gf, bg=PANEL, highlightbackground=LINE, highlightthickness=1)
        box2.grid(row=0, column=1, sticky="new")
        tk.Label(box2, text="Brain and extras", font=(FONT, 13, "bold"), fg=BRAIN, bg=PANEL).pack(anchor="w", padx=20, pady=(14, 2))
        tk.Label(box2, text="The brain tests candidate rules on older prices and only keeps the ones that also profit on "
                            "newer prices it never trained on. The switch in the header turns it on.", font=(FONT, 9),
                 fg=MUTED, bg=PANEL, wraplength=420, justify="left", anchor="w").pack(fill="x", padx=20, pady=(0, 10))
        self.settings_b = RuleForm(box2, SETTINGS_B)
        self.settings_b.pack(fill="x", padx=20)
        self.settings_err = tk.Label(box2, text="", font=(FONT, 9), fg=BLOOD, bg=PANEL, anchor="w", wraplength=420, justify="left")
        self.settings_err.pack(fill="x", padx=20, pady=(8, 0))
        Btn(box2, "Save settings", self.save_settings, PURPLE_D, ORANGE, PURPLE_H).pack(anchor="w", padx=20, pady=(6, 16))

        self.trades_w = self._text(self.tab_frames["Trades"])
        self.logw = self._text(self.tab_frames["Activity"])
        self.show_tab("Overview")

    def _text(self, parent, mono=True, border=True):
        w = tk.Text(parent, bg=PANEL, fg=MUTED, relief="flat", bd=0, wrap="none", font=("Consolas", 10),
                    padx=16, pady=12, state="disabled", highlightbackground=LINE, highlightthickness=1 if border else 0)
        w.pack(fill="both", expand=True)
        for tag, col in (("action", ORANGE), ("error", BLOOD), ("info", MUTED), ("win", SLIME), ("loss", BLOOD),
                         ("head", TEXT), ("brain", BRAIN), ("brain_up", BRAIN)):
            w.tag_config(tag, foreground=col)
        return w

    def show_tab(self, name):
        self.cur_tab = name
        self.tab_frames[name].tkraise()
        for n in self.TABS:
            self.tab_btns[n].restyle(n, PURPLE_D if n == name else PANEL, ORANGE if n == name else MUTED, PURPLE_H)

    # ---------- actions ----------
    def alive(self):
        return self.engine is not None and self.engine.is_alive()

    def toggle_engine(self):
        if self.alive():
            self.engine.halt.set()
        else:
            self.engine = Engine(self.cfg, self.ledger, self.history, self.brain, self.log_q)
            self.engine.start()

    def set_adapt(self, on):
        self.cfg["settings"]["adapt"] = bool(on)
        try:
            save_config(self.cfg)
        except Exception:
            pass
        self.log_q.put((datetime.now().strftime("%H:%M:%S"), "brain",
                        "Auto-adapt is on, the brain will start tuning rules" if on else "Auto-adapt is off, rules are back to what you set"))
        if on:
            self.header.brain_spark()

    def toggle_pause(self):
        if self.alive():
            self.engine.pause_entries = not self.engine.pause_entries
            self.log_q.put((datetime.now().strftime("%H:%M:%S"), "info",
                            "New entries paused" if self.engine.pause_entries else "New entries resumed"))

    def close_all(self):
        if not self.alive():
            messagebox.showinfo("Close all", "Start the trader first, it sends the close orders.")
            return
        if messagebox.askyesno("Close all positions", "Close every open position and pause new entries?"):
            self.engine.pause_entries = True
            self.engine.close_all = True

    def reset_brain_stock(self):
        if self.selected and messagebox.askyesno("Reset brain", f"Forget everything the brain learned about {self.selected}?"):
            self.brain.reset(self.selected)

    def reset_brain_all(self):
        if messagebox.askyesno("Reset brain", "Forget everything the brain learned about every stock?"):
            self.brain.reset(None)

    def select(self, stock):
        self.selected = stock
        self.stock_list.select(stock)
        self.stock_form.load(rules_for(self.cfg, stock))
        self.stock_err.config(text="")
        if self.cur_tab in ("Overview", "Trades", "Activity"):
            self.show_tab("Stock")

    def save_stock(self):
        if not self.selected:
            return
        try:
            r = self.stock_form.read()
            if not r["auto"]:
                if r["buy_at"] is None or r["close_at"] is None:
                    raise ValueError("Enter a buy and a close level, or turn on auto-calibrate")
                if r["buy_at"] >= r["close_at"]:
                    raise ValueError("The buy level must be below the close level")
                if r["stop_loss"] is not None and r["stop_loss"] >= r["buy_at"]:
                    raise ValueError("The stop loss must be below the buy level")
                if r["short_enabled"]:
                    sa = r["short_at"] if r["short_at"] is not None else r["close_at"]
                    if r["short_stop"] is not None and r["short_stop"] <= sa:
                        raise ValueError("The short stop must be above the short level")
            if r["crash_enabled"] and (r["crash_buy"] is None or r["crash_short"] is None):
                raise ValueError("Crash window rules need a crash buy and a crash short level")
        except ValueError as e:
            self.stock_err.config(text=str(e))
            return
        self.stock_err.config(text="")
        self.cfg["stocks"][self.selected] = r
        self._save("Rules saved for " + self.selected, self.stock_err)

    def save_settings(self):
        try:
            a, b = self.settings_a.read(), self.settings_b.read()
            if not (0 < a["auto_buy_pct"] < a["auto_close_pct"] < 100):
                raise ValueError("Auto percentiles need 0 < buy % < close % < 100")
            if a["auto_warmup"] < 10:
                raise ValueError("Auto needs at least 10 price samples")
            if b["brain_min_samples"] < 120:
                raise ValueError("The brain needs at least 120 price samples to learn from")
            if b["brain_interval"] < 5:
                raise ValueError("Brain rounds need to be at least 5 seconds apart")
            if not (0 <= b["brain_min_conf"] <= 1):
                raise ValueError("Brain confidence is a number from 0 to 1")
        except ValueError as e:
            self.settings_err.config(text=str(e))
            return
        self.settings_err.config(text="")
        self.cfg["settings"].update(a)
        self.cfg["settings"].update(b)
        self._save("Settings saved", self.settings_err)

    def _save(self, msg, err_label):
        try:
            save_config(self.cfg)
            self.log_q.put((datetime.now().strftime("%H:%M:%S"), "info", msg))
        except Exception as e:
            err_label.config(text=f"Couldn't write config.json: {e}")

    def _close(self):
        if self.engine:
            self.engine.halt.set()
        self.brain.halt.set()
        self.brain.save()
        self.ledger.save(True)
        self.history.save(time.time(), True)
        self.destroy()

    # ---------- refresh ----------
    def refresh_stocks(self, force=False):
        now = time.time()
        if not force and now - self._found_at < 5:
            return
        self._found_at = now
        found = sorted(discover_stocks(self.base))
        self.stock_list.set_stocks(found)
        if found and (self.selected not in found):
            self.select(found[0])
            self.show_tab("Overview")

    def write_log(self, ts, level, msg):
        sounds = self.cfg["settings"].get("sounds")
        if level in ("brain", "brain_up"):
            self.brain_panel.add_feed(ts, level, msg)
            if level == "brain_up":
                self.header.brain_spark()
                play("brain", sounds)
        w = self.logw
        w.config(state="normal")
        w.insert("end", f"{ts}  {msg}\n", level)
        if int(float(w.index("end-1c"))) > 500:
            w.delete("1.0", "60.0")
        w.see("end")
        w.config(state="disabled")

    def refresh_trades(self):
        trades = self.ledger.d["trades"]
        if len(trades) == self._trades_n:
            return
        self._trades_n = len(trades)
        w = self.trades_w
        w.config(state="normal")
        w.delete("1.0", "end")
        w.insert("end", f"{'Closed':<10}{'Stock':<10}{'Side':<7}{'Shares':>8}{'Entry':>12}{'Exit':>12}{'Result':>14}\n", "head")
        for t in reversed(trades[-300:]):
            when = datetime.fromtimestamp(t["t"]).strftime("%m/%d %H:%M")
            line = (f"{when:<10}{t['stock']:<10}{t['side']:<7}{t['shares']:>8,}"
                    f"{t['entry']:>12,.2f}{t['exit']:>12,.2f}{money(t['pnl']):>14}\n")
            w.insert("end", line, "win" if t["pnl"] > 0 else "loss" if t["pnl"] < 0 else "info")
        if not trades:
            w.insert("end", "\nNo closed trades yet. Income is booked when a position shrinks or closes.\n", "info")
        w.config(state="disabled")

    def refresh_overview(self, views):
        self.equity.set(self.ledger.equity())
        ranked = sorted(self.ledger.by_stock.items(), key=lambda kv: abs(kv[1]), reverse=True)[:6]
        self.board.set([(k, v) for k, v in ranked])
        w = self.open_w
        w.config(state="normal")
        w.delete("1.0", "end")
        held = [(s, v) for s, v in views.items() if v["owned"] or v["shorted"]]
        if not held:
            w.insert("end", "Nothing open right now.\n", "info")
        for s, v in held:
            side, n = ("long", v["owned"]) if v["owned"] else ("short", v["shorted"])
            w.insert("end", f"{s:<9}{side:<6}{n:>6,} sh  {money(v['open_pnl']):>12}\n",
                     "win" if v["open_pnl"] > 0.004 else "loss" if v["open_pnl"] < -0.004 else "info")
        w.config(state="disabled")

    def celebrate_new_trades(self):
        trades = self.ledger.d["trades"]
        if self._seen_trades is None:
            self._seen_trades = len(trades)
            return
        new, self._seen_trades = trades[self._seen_trades:], len(trades)
        if not new:
            return
        wins = [t["pnl"] for t in trades if t["pnl"] > 0]
        avg = sum(wins) / len(wins) if wins else 0.0
        sounds = self.cfg["settings"].get("sounds")
        for t in new[-3:]:
            if t["pnl"] > 0:
                self.header.celebrate(t["pnl"], big=len(wins) >= 3 and t["pnl"] > 2 * avg)
                play("win", sounds)
            elif t["pnl"] < 0:
                self.header.grieve(t["pnl"])
                play("loss", sounds)

    def poll(self):
        while True:
            try:
                self.write_log(*self.log_q.get_nowait())
            except queue.Empty:
                break
        self.refresh_stocks()
        eng = self.engine if self.alive() else None
        snap = eng.snap if eng else None
        adapt = bool(self.cfg["settings"].get("adapt"))
        busy = bool(adapt and self.brain.busy)
        self.switch.busy = busy
        views = snap["stocks"] if snap else {}

        if not eng:
            self.status.config(text="Stopped", bg=PURPLE_D, fg=MUTED)
            self.toggle.restyle("Start trading", ORANGE, HEAD, ORANGE_H)
            self.pause_btn.restyle("Pause entries", PURPLE_D, ORANGE, PURPLE_H)
            mood, energy = "Asleep in the crypt. Press Start trading to wake it.", 0.25
        else:
            held = sum(1 for v in views.values() if v["owned"] or v["shorted"])
            if snap["halt"]:
                self.status.config(text=snap["halt"], bg=POS_R, fg=BLOOD)
                mood, energy = snap["halt"] + ", the bot is only managing open positions", 0.5
            elif eng.pause_entries:
                self.status.config(text="Entries paused", bg="#4a3a14", fg=ORANGE)
                mood, energy = "Entries paused, watching the market without opening anything new", 0.4
            elif snap["link"] == "live":
                self.status.config(text="Running", bg=POS_G, fg=SLIME)
                mood = f"Haunting {len(views)} stocks" + (f", holding {held}" if held else ", hunting for signals")
                energy = 0.7
            else:
                self.status.config(text="Waiting for market.json", bg="#4a3a14", fg=ORANGE)
                mood, energy = "Waiting for the game to write market.json", 0.4
            self.toggle.restyle("Stop trading", POS_R, BLOOD, "#6b2838")
            self.pause_btn.restyle("Resume entries" if eng.pause_entries else "Pause entries", PURPLE_D, ORANGE, PURPLE_H)
        if adapt:
            mood += ". " + ("The brain is tuning " + self.brain.busy if busy else "The brain is on")
            energy = max(energy, 0.9 if busy else energy)
        self.header.set_mood(mood)
        self.header.energy = energy

        st = self.ledger.stats()
        self.tiles["today"].set_target(st["today"], "money")
        self.tiles["total"].set_target(st["total"], "money")
        self.tiles["open"].set_target(snap["open_pnl"] if snap else None, "money")
        self.tiles["avg_trade"].set_target(st["avg_trade"], "money")
        self.tiles["avg_hour"].set_target(st["avg_hour"], "money")
        self.tiles["win"].set_target(st["win"], "pct")
        self.tiles["n"].set_target(float(st["n"]), "int")

        for s, row in self.stock_list.rows.items():
            row.update_view(views.get(s))
        view = views.get(self.selected)
        idle = "Trader is stopped, press Start trading" if not eng else "Waiting for data"
        self.card.show(self.selected, view, eng.cooldowns(self.selected) if (eng and self.selected) else None, idle)
        S = self.brain.info(self.selected) if self.selected else None
        locked = bool(self.selected and rules_for(self.cfg, self.selected)["brain_lock"])
        self.brain_panel.update_info(self.selected, S, self.cfg["settings"], self.history.count(self.selected) if self.selected else 0,
                                     locked, adapt, busy)
        self.refresh_trades()
        self.refresh_overview(views)
        self.celebrate_new_trades()
        self.after(400, self.poll)

    def anim(self):
        self.header.tick()
        self.switch.tick()
        for t in self.tiles.values():
            t.tick()
        if self.cur_tab == "Brain":
            self.brain_panel.tick(self.header.t)
        elif self.cur_tab == "Overview":
            self.equity.tick()
        self.after(40, self.anim)


def main():
    try:
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(1)    # crisp text on Windows
    except Exception:
        pass
    App().mainloop()


if __name__ == "__main__":
    main()
