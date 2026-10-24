# This is the main code for the bot
"""
Screen Stocks Trader, Haunted edition
Trades every stock folder it finds under the game's commands folder, tracks income,
and runs on plain Python 3 with Tkinter (nothing extra to install).
"""
import json, math, os, queue, random, threading, time
import tkinter as tk
from collections import deque
from datetime import date, datetime, timezone
from tkinter import font as tkfont, messagebox, simpledialog

APP_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_FILE = os.path.join(APP_DIR, "config.json")
LEDGER_FILE = os.path.join(APP_DIR, "trades.json")
HISTORY_FILE = os.path.join(APP_DIR, "history.json")

# ================= PALETTE (Halloween) =================
HEAD, BG, PANEL, PANEL2, LINE = "#0f0719", "#140b22", "#1f1333", "#170e27", "#3a2656"
TEXT, MUTED = "#f1e9d2", "#a898c4"
ORANGE, ORANGE_H = "#ff8a1f", "#ffa24d"
PURPLE_D, PURPLE_H = "#33205f", "#432b7a"
SLIME, BLOOD = "#9dff5a", "#ff5a74"
ZONE_G, ZONE_R = "#264a2e", "#55233b"
POS_G, POS_R = "#1f4a2a", "#55202f"
FONT = "Segoe UI"
DISPLAY_FONT = "Georgia"

# ================= CONSTANTS =================
TECH, PLAIN = "$TECH", "$PLAIN"
PRICE_ALIASES = {"$PLAIN": "$BASE"}        # stock folder -> market.json name used for its price
LOOP_DELAY, EXTRA, CLOSE_LOCK = 1.0, 2.0, 3.0
SAMPLE_EVERY, HISTORY_MAX = 10.0, 3000     # price sample every 10s, ~8 hours kept
DEFAULT_LOCK = {"buymax.json": 105.0, "shortmax.json": 102.0}

DEFAULT_SETTINGS = {
    "dry_run": False, "max_positions": 0.0, "daily_target": None, "daily_loss": None,
    "auto_buy_pct": 20.0, "auto_close_pct": 80.0, "auto_warmup": 60.0, "auto_min_range": 6.0,
    "auto_stop_pct": 8.0, "auto_trail_pct": None, "auto_short": False,
}


def base_stock():
    return {"enabled": True, "auto": True, "buy_at": None, "close_at": None, "stop_loss": None,
            "short_enabled": False, "short_at": None, "cover_at": None, "short_stop": None,
            "crash_enabled": False, "crash_short": None, "crash_buy": None,
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
        old = saved.get("rules")                       # config from the earlier GUI
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

    def values(self, stock):
        return list(self.d.get(stock, ()))

    def save(self, now, force=False):
        if not force and now - self._saved < 60:
            return
        self._saved = now
        try:
            tmp = HISTORY_FILE + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump({k: list(v) for k, v in self.d.items()}, f)
            os.replace(tmp, HISTORY_FILE)
        except Exception:
            pass


# ================= TRADING ENGINE =================
def mk(kind=None, why="", note="", score=0.0):
    return {"kind": kind, "why": why, "note": note, "score": score}


class Engine(threading.Thread):
    def __init__(self, cfg, ledger, history, log_q, base=None):
        super().__init__(daemon=True)
        self.cfg, self.ledger, self.history, self.log_q = cfg, ledger, history, log_q
        self.base = base or game_base(cfg["username"])
        self.halt = threading.Event()
        self.pause_entries, self.close_all = False, False
        self.lock_len, self.unlock_at, self.pending = {}, {}, {}
        self.state, self.seen = {}, set()
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
        prices = collect_prices(market)
        self.update_cooldowns(market)
        self.ledger.d["run_seconds"] += min(dt, 5.0)
        st = self.cfg["settings"]
        posmap = {p.get("stockId"): p for p in market.get("player", {}).get("positions", [])}

        # daily kill switch
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
            view = {"price": price, "owned": owned, "shorted": shorted, "note": "", "levels": None,
                    "auto": r["auto"], "enabled": r["enabled"], "crash": self.crash_levels(r),
                    "spark": [], "realized": self.ledger.by_stock.get(s, 0.0), "open_pnl": 0.0}
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
            if not r["enabled"]:
                view["note"] = "Turned off in rules"
                continue
            a = self.decide(s, r, st, price, owned, shorted, L, reason)
            view["note"] = a["note"]
            acts[s] = a

        # closing always goes through; panic button closes everything
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

            # entries: best signal first, within the position limit
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
        if r["auto"]:
            vals = self.history.values(s)
            warm = int(st["auto_warmup"] or 60)
            if len(vals) < warm:
                return None, f"Learning the price range ({len(vals)}/{warm})"
            lo, hi = quantile(vals, st["auto_buy_pct"] / 100), quantile(vals, st["auto_close_pct"] / 100)
            if lo <= 0 or hi < lo * (1 + st["auto_min_range"] / 100):
                return None, "Price range is too narrow to trade"
            return {"buy_at": lo, "close_at": hi, "stop_loss": None, "short_enabled": bool(st["auto_short"]),
                    "short_at": hi, "cover_at": lo, "short_stop": None, "auto": True}, None
        if r["buy_at"] is None or r["close_at"] is None:
            return None, "Set buy and close levels in the rules"
        return {"buy_at": r["buy_at"], "close_at": r["close_at"], "stop_loss": r["stop_loss"],
                "short_enabled": bool(r["short_enabled"]),
                "short_at": r["short_at"] if r["short_at"] is not None else r["close_at"],
                "cover_at": r["cover_at"] if r["cover_at"] is not None else r["buy_at"],
                "short_stop": r["short_stop"], "auto": False}, None

    def decide(self, s, r, st, price, owned, shorted, L, reason):
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

        if owned:
            if L["stop_loss"] is not None and price <= L["stop_loss"]:
                return stop("long", "stop loss")
            if L["auto"]:
                entry = self.ledger.entry(s, "long")
                if st.get("auto_stop_pct") and entry and price <= entry * (1 - st["auto_stop_pct"] / 100):
                    return stop("long", "stop loss")
                if st.get("auto_trail_pct") and S["ext"] and price <= S["ext"] * (1 - st["auto_trail_pct"] / 100):
                    return stop("long", "trailing stop")
        if shorted:
            if L["short_stop"] is not None and price >= L["short_stop"]:
                return stop("short", "short stop")
            if L["auto"]:
                entry = self.ledger.entry(s, "short")
                if st.get("auto_stop_pct") and entry and price >= entry * (1 + st["auto_stop_pct"] / 100):
                    return stop("short", "short stop")
                if st.get("auto_trail_pct") and S["ext"] and price >= S["ext"] * (1 + st["auto_trail_pct"] / 100):
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


# ================= GUI WIDGETS =================
def pick_font(candidates, default):
    try:
        fams = set(tkfont.families())
    except Exception:
        return default
    return next((c for c in candidates if c in fams), default)


class Btn(tk.Button):
    def __init__(self, parent, text, command, bg, fg, hover):
        super().__init__(parent, text=text, command=command, bg=bg, fg=fg, activebackground=hover,
                         activeforeground=fg, relief="flat", bd=0, font=(FONT, 10, "bold"), padx=18, pady=8,
                         cursor="hand2", highlightthickness=2, highlightbackground=bg, highlightcolor=ORANGE_H,
                         takefocus=1)

    def restyle(self, text, bg, fg, hover):
        self.config(text=text, bg=bg, fg=fg, activebackground=hover, activeforeground=fg, highlightbackground=bg)


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
        self.sub.config(text="" if not view else ("auto levels" if view["auto"] else "manual levels"))
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
            bar.set(None, 0) if cooldowns is None else bar.set(*cooldowns[cmd])
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
        self.stock, self.sel = stock, False
        self.bar = tk.Frame(self, width=5, bg=PANEL)
        self.bar.pack(side="left", fill="y")
        body = tk.Frame(self, bg=PANEL)
        body.pack(side="left", fill="x", expand=True, padx=(10, 12), pady=8)
        body.columnconfigure(0, weight=1)
        self.name = tk.Label(body, text=stock, font=(FONT, 12, "bold"), fg=ORANGE, bg=PANEL, anchor="w")
        self.note = tk.Label(body, text="", font=(FONT, 9), fg=MUTED, bg=PANEL, anchor="w")
        self.spark = tk.Canvas(body, width=92, height=30, bg=PANEL, highlightthickness=0)
        self.price = tk.Label(body, text="--", font=(FONT, 12, "bold"), fg=TEXT, bg=PANEL, anchor="e")
        self.pnl = tk.Label(body, text="", font=(FONT, 9), fg=MUTED, bg=PANEL, anchor="e")
        self.name.grid(row=0, column=0, sticky="w")
        self.note.grid(row=1, column=0, sticky="w")
        self.spark.grid(row=0, column=1, rowspan=2, padx=10)
        self.price.grid(row=0, column=2, sticky="e")
        self.pnl.grid(row=1, column=2, sticky="e")
        self.parts = [self, body, self.name, self.note, self.price, self.pnl, self.spark]
        for w in self.parts + [self.bar]:
            w.bind("<Button-1>", lambda e, s=stock: on_click(s))
        self.accent = PANEL

    def _paint(self):
        bg = PURPLE_D if self.sel else PANEL
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
            draw_spark(self.spark, view["spark"], 92, 30, MUTED)
        else:
            self.price.config(text="--")
            self.note.config(text="")
            self.pnl.config(text="")
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
        shown = [s for s in sorted(self.rows) if q in s.lower()]
        for s in shown:
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


class StatTile(tk.Frame):
    def __init__(self, parent, title, footnote=""):
        super().__init__(parent, bg=PANEL, highlightbackground=LINE, highlightthickness=1)
        tk.Label(self, text=title, font=(FONT, 9), fg=MUTED, bg=PANEL, anchor="w").pack(fill="x", padx=14, pady=(10, 0))
        self.val = tk.Label(self, text="--", font=(FONT, 18, "bold"), fg=TEXT, bg=PANEL, anchor="w")
        self.val.pack(fill="x", padx=14)
        tk.Label(self, text=footnote, font=(FONT, 8), fg=MUTED, bg=PANEL, anchor="w").pack(fill="x", padx=14, pady=(0, 8))

    def set(self, text, color=TEXT):
        self.val.config(text=text, fg=color)


class RuleForm(tk.Frame):
    def __init__(self, parent, fields, label_width=None):
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
SETTINGS_FIELDS = [
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


# ================= APP =================
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.withdraw()
        global DISPLAY_FONT
        DISPLAY_FONT = pick_font(["Chiller", "Jokerman", "Gabriola", "Segoe Script"], "Georgia")
        self.title("Screen Stocks Trader, Haunted edition")
        self.configure(bg=BG)
        self.geometry("1340x880")
        self.minsize(1180, 760)

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
        self.engine, self.log_q = None, queue.Queue()
        self.selected, self._found_at, self._trades_n = None, 0.0, -1

        self._build()
        self.protocol("WM_DELETE_WINDOW", self._close)
        self.refresh_stocks(True)
        self.settings_form.load(self.cfg["settings"])
        self.deiconify()
        self.poll()

    # ---------- layout ----------
    def _build(self):
        head = tk.Frame(self, bg=HEAD, height=112)
        head.pack(fill="x")
        head.pack_propagate(False)
        self.hc = tk.Canvas(head, bg=HEAD, highlightthickness=0)
        self.hc.place(x=0, y=0, relwidth=1, relheight=1)
        self.hc.bind("<Configure>", lambda e: self.draw_header())
        btns = tk.Frame(head, bg=HEAD)
        btns.place(relx=1.0, x=-24, rely=0.5, anchor="e")
        self.status = tk.Label(btns, text="Stopped", font=(FONT, 10, "bold"), padx=14, pady=6, bg=PURPLE_D, fg=MUTED)
        self.status.pack(side="left", padx=(0, 12))
        self.pause_btn = Btn(btns, "Pause entries", self.toggle_pause, PURPLE_D, ORANGE, PURPLE_H)
        self.pause_btn.pack(side="left", padx=(0, 8))
        Btn(btns, "Close all", self.close_all, POS_R, BLOOD, "#6b2838").pack(side="left", padx=(0, 8))
        self.toggle = Btn(btns, "Start trading", self.toggle_engine, ORANGE, HEAD, ORANGE_H)
        self.toggle.pack(side="left")

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
        self.stock_list.grid_propagate(False)

        right = tk.Frame(body, bg=BG)
        right.grid(row=0, column=1, sticky="nsew")
        right.rowconfigure(1, weight=1)
        right.columnconfigure(0, weight=1)
        tabs = tk.Frame(right, bg=BG)
        tabs.grid(row=0, column=0, sticky="w", pady=(0, 10))
        self.tab_btns, self.tab_frames = {}, {}
        for name in ("Stock", "Settings", "Trades", "Activity"):
            b = Btn(tabs, name, lambda n=name: self.show_tab(n), PANEL, MUTED, PURPLE_D)
            b.pack(side="left", padx=(0, 6))
            self.tab_btns[name] = b
            f = tk.Frame(right, bg=BG)
            f.grid(row=1, column=0, sticky="nsew")
            self.tab_frames[name] = f

        # Stock tab
        sf = self.tab_frames["Stock"]
        sf.columnconfigure(0, weight=1)
        sf.columnconfigure(1, minsize=330)
        sf.rowconfigure(0, weight=1)
        self.card = StockCard(sf)
        self.card.grid(row=0, column=0, sticky="new", padx=(0, 16))
        rf = tk.Frame(sf, bg=PANEL, highlightbackground=LINE, highlightthickness=1)
        rf.grid(row=0, column=1, sticky="new")
        tk.Label(rf, text="Rules for this stock", font=(FONT, 13, "bold"), fg=ORANGE, bg=PANEL).pack(anchor="w", padx=20, pady=(14, 6))
        self.stock_form = RuleForm(rf, STOCK_FIELDS)
        self.stock_form.pack(fill="x", padx=20)
        self.stock_err = tk.Label(rf, text="", font=(FONT, 9), fg=BLOOD, bg=PANEL, wraplength=290, justify="left", anchor="w")
        self.stock_err.pack(fill="x", padx=20, pady=(8, 0))
        Btn(rf, "Save rules", self.save_stock, PURPLE_D, ORANGE, PURPLE_H).pack(fill="x", padx=20, pady=(6, 16))

        # Settings tab
        gf = self.tab_frames["Settings"]
        box = tk.Frame(gf, bg=PANEL, highlightbackground=LINE, highlightthickness=1)
        box.pack(anchor="nw", fill="x")
        tk.Label(box, text="Settings for every stock", font=(FONT, 13, "bold"), fg=ORANGE, bg=PANEL).pack(anchor="w", padx=20, pady=(14, 2))
        tk.Label(box, text="Auto stocks learn their own buy and close levels from the prices seen while the trader runs "
                           "(one sample every 10 seconds, kept between sessions). Stocks with manual levels ignore the auto settings.",
                 font=(FONT, 9), fg=MUTED, bg=PANEL, wraplength=640, justify="left", anchor="w").pack(fill="x", padx=20, pady=(0, 10))
        self.settings_form = RuleForm(box, SETTINGS_FIELDS)
        self.settings_form.pack(fill="x", padx=20)
        self.settings_err = tk.Label(box, text="", font=(FONT, 9), fg=BLOOD, bg=PANEL, anchor="w")
        self.settings_err.pack(fill="x", padx=20, pady=(8, 0))
        Btn(box, "Save settings", self.save_settings, PURPLE_D, ORANGE, PURPLE_H).pack(anchor="w", padx=20, pady=(6, 16))

        # Trades tab
        tf = self.tab_frames["Trades"]
        self.trades_w = self._text(tf)
        # Activity tab
        af = self.tab_frames["Activity"]
        self.logw = self._text(af)
        self.show_tab("Stock")

    def _text(self, parent):
        w = tk.Text(parent, bg=PANEL, fg=MUTED, relief="flat", bd=0, wrap="none", font=("Consolas", 10),
                    padx=16, pady=12, state="disabled", highlightbackground=LINE, highlightthickness=1)
        w.pack(fill="both", expand=True)
        for tag, col in (("action", ORANGE), ("error", BLOOD), ("info", MUTED), ("win", SLIME), ("loss", BLOOD), ("head", TEXT)):
            w.tag_config(tag, foreground=col)
        return w

    def show_tab(self, name):
        for n, f in self.tab_frames.items():
            if n == name:
                f.tkraise()
            self.tab_btns[n].restyle(n, PURPLE_D if n == name else PANEL, ORANGE if n == name else MUTED, PURPLE_H)

    # ---------- Halloween header ----------
    def draw_header(self):
        c = self.hc
        c.delete("all")
        w, h = max(c.winfo_width(), 600), 112
        rng = random.Random(13)
        for _ in range(46):
            x, y, r = rng.randint(0, w), rng.randint(2, h - 8), rng.choice((1, 1, 2))
            c.create_oval(x, y, x + r, y + r, fill=rng.choice(("#5c4a86", "#7d6aa8", "#3f2f66")), outline="")
        # cobweb in the corner
        web = "#4a3470"
        angles = [math.radians(a) for a in (0, 22, 45, 68, 90)]
        for a in angles:
            c.create_line(0, 0, 96 * math.cos(a), 96 * math.sin(a), fill=web)
        for rad in (26, 50, 74, 96):
            pts = []
            for a in angles:
                pts += [rad * math.cos(a) * 0.92, rad * math.sin(a) * 0.92]
            c.create_line(*pts, fill=web, smooth=True)
        # moon
        mx, my = int(w * 0.52), 46
        c.create_oval(mx - 34, my - 34, mx + 34, my + 34, fill="#2a1a45", outline="")
        c.create_oval(mx - 26, my - 26, mx + 26, my + 26, fill="#f6e7a8", outline="")
        for dx, dy, r in ((-9, -8, 6), (8, 5, 8), (-4, 12, 4)):
            c.create_oval(mx + dx - r, my + dy - r, mx + dx + r, my + dy + r, fill="#e4d08a", outline="")
        # bats
        for fx, fy, s in ((0.40, 30, 1.0), (0.46, 78, 0.7), (0.60, 24, 0.8), (0.66, 70, 1.1), (0.34, 84, 0.6)):
            self._bat(c, w * fx, fy, 6 * s)
        # pumpkin + title
        self._pumpkin(c, 66, 66, 34)
        c.create_text(122, 46, text="Screen Stocks Trader", anchor="w", font=(DISPLAY_FONT, 30), fill="#6b2fd1")
        c.create_text(120, 44, text="Screen Stocks Trader", anchor="w", font=(DISPLAY_FONT, 30), fill=ORANGE)
        c.create_text(124, 86, text="Haunted edition, trading every stock it finds", anchor="w", font=(FONT, 10), fill=MUTED)

    @staticmethod
    def _bat(c, cx, cy, s):
        pts = [(-3, -1), (-2, -2), (-1, -1.2), (-0.6, -2), (0, -1), (0.6, -2), (1, -1.2), (2, -2), (3, -1),
               (2, 0.2), (1, -0.4), (0, 1), (-1, -0.4), (-2, 0.2)]
        c.create_polygon([v for x, y in pts for v in (cx + x * s, cy + y * s)], fill="#07030d", outline="#2b1a47")

    @staticmethod
    def _pumpkin(c, cx, cy, r):
        c.create_oval(cx - r * 1.05, cy - r * 0.8, cx + r * 0.3, cy + r * 0.85, fill="#d66200", outline="")
        c.create_oval(cx - r * 0.3, cy - r * 0.8, cx + r * 1.05, cy + r * 0.85, fill="#d66200", outline="")
        c.create_oval(cx - r * 0.65, cy - r * 0.88, cx + r * 0.65, cy + r * 0.92, fill=ORANGE, outline="")
        c.create_polygon(cx - r * 0.12, cy - r * 0.8, cx + r * 0.12, cy - r * 0.8, cx + r * 0.24, cy - r * 1.15,
                         cx - r * 0.04, cy - r * 1.1, fill="#5a7d2b", outline="")
        dark = "#2a0f3a"
        for sx in (-1, 1):
            ex = cx + sx * r * 0.3
            c.create_polygon(ex - r * 0.17, cy - r * 0.08, ex + r * 0.17, cy - r * 0.08, ex, cy - r * 0.42, fill=dark, outline="")
        zig = []
        for i in range(7):
            zig += [cx - r * 0.45 + i * r * 0.15, cy + r * (0.28 if i % 2 == 0 else 0.5)]
        c.create_polygon(zig + [cx + r * 0.45, cy + r * 0.28], fill=dark, outline="")

    # ---------- actions ----------
    def alive(self):
        return self.engine is not None and self.engine.is_alive()

    def toggle_engine(self):
        if self.alive():
            self.engine.halt.set()
        else:
            self.engine = Engine(self.cfg, self.ledger, self.history, self.log_q)
            self.engine.start()

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

    def select(self, stock):
        self.selected = stock
        self.stock_list.select(stock)
        self.stock_form.load(rules_for(self.cfg, stock))
        self.stock_err.config(text="")
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
            s = self.settings_form.read()
            if not (0 < s["auto_buy_pct"] < s["auto_close_pct"] < 100):
                raise ValueError("Auto percentiles need 0 < buy % < close % < 100")
            if s["auto_warmup"] < 10:
                raise ValueError("Auto needs at least 10 price samples")
        except ValueError as e:
            self.settings_err.config(text=str(e))
            return
        self.settings_err.config(text="")
        self.cfg["settings"].update(s)
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
            self.show_tab("Stock")

    def write_log(self, ts, level, msg):
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

    def poll(self):
        while True:
            try:
                self.write_log(*self.log_q.get_nowait())
            except queue.Empty:
                break
        self.refresh_stocks()
        eng = self.engine if self.alive() else None
        snap = eng.snap if eng else None

        if not eng:
            self.status.config(text="Stopped", bg=PURPLE_D, fg=MUTED)
            self.toggle.restyle("Start trading", ORANGE, HEAD, ORANGE_H)
            self.pause_btn.restyle("Pause entries", PURPLE_D, ORANGE, PURPLE_H)
        else:
            if snap["halt"]:
                self.status.config(text=snap["halt"], bg=POS_R, fg=BLOOD)
            elif eng.pause_entries:
                self.status.config(text="Entries paused", bg="#4a3a14", fg=ORANGE)
            elif snap["link"] == "live":
                self.status.config(text="Running", bg=POS_G, fg=SLIME)
            else:
                self.status.config(text="Waiting for market.json", bg="#4a3a14", fg=ORANGE)
            self.toggle.restyle("Stop trading", POS_R, BLOOD, "#6b2838")
            self.pause_btn.restyle("Resume entries" if eng.pause_entries else "Pause entries", PURPLE_D, ORANGE, PURPLE_H)

        st = self.ledger.stats()
        self.tiles["today"].set(money(st["today"]), money_color(st["today"]))
        self.tiles["total"].set(money(st["total"]), money_color(st["total"]))
        op = snap["open_pnl"] if snap else None
        self.tiles["open"].set("--" if op is None else money(op), MUTED if op is None else money_color(op))
        for key in ("avg_trade", "avg_hour"):
            v = st[key]
            self.tiles[key].set("--" if v is None else money(v), MUTED if v is None else money_color(v))
        self.tiles["win"].set("--" if st["win"] is None else f"{st['win']:.0f}%", TEXT if st["win"] is not None else MUTED)
        self.tiles["n"].set(f"{st['n']:,}")

        views = snap["stocks"] if snap else {}
        for s, row in self.stock_list.rows.items():
            row.update_view(views.get(s))
        view = views.get(self.selected)
        idle = "Trader is stopped, press Start trading" if not eng else "Waiting for data"
        self.card.show(self.selected, view, eng.cooldowns(self.selected) if (eng and self.selected) else None, idle)
        self.refresh_trades()
        self.after(400, self.poll)


def main():
    try:
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(1)    # crisp text on Windows
    except Exception:
        pass
    App().mainloop()


if __name__ == "__main__":
    main()
