# ==============================================================================
# DevicePilot Android Automation Controller — v1.0
# Place alongside android_automation_engine.py and run directly.
# ==============================================================================
from __future__ import annotations

import importlib.util
import json
import logging
import os
import re
import subprocess
import sys
import threading
import time
import traceback
from datetime import datetime
from pathlib import Path
from queue import Empty, Queue
import tkinter as tk
from tkinter import filedialog, messagebox, scrolledtext, ttk

# Optional drag-and-drop support for the Data Extractor tab.  When tkinterdnd2
# is installed the controller root is made DnD-capable; otherwise it falls back
# to a plain tk.Tk root (drag-drop simply unavailable, never a hard dependency).
try:
    from tkinterdnd2 import TkinterDnD, DND_FILES
    _DND_AVAILABLE = True
    _ControllerBase = TkinterDnD.Tk
except Exception:
    TkinterDnD = None
    DND_FILES = None
    _DND_AVAILABLE = False
    _ControllerBase = tk.Tk

import multiprocessing
from concurrent.futures import ThreadPoolExecutor, as_completed

try:
    from PIL import Image, ImageTk, ImageDraw
    _PIL_OK = True
except ImportError:
    _PIL_OK = False

try:
    import winsound
    def _beep():
        winsound.Beep(880, 350)
        time.sleep(0.12)
        winsound.Beep(1100, 250)
except ImportError:
    def _beep():
        try:
            subprocess.Popen(["paplay", "/usr/share/sounds/freedesktop/stereo/complete.oga"],
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        except Exception:
            try:
                print("\a", end="", flush=True)
            except Exception:
                pass


# ── paths ──────────────────────────────────────────────────────────────────────
SCRIPT_BASENAME = "android_automation_engine.py"
ETA_FILE        = "controller_eta.json"
STATE_FILE      = "controller_state.json"
STATUS_CACHE_FILE  = "controller_status_cache.json"   # persists latest completed task statuses
NAMED_STATES_FILE  = "controller_states.json"          # named UI state snapshots
TASK_SETS_FILE  = "task_sets.json"
LOG_DIR         = "."
INTERNET_DOWN_TIMEOUT = 40.0   # seconds before global internet-down emergency fires

# ── task definitions ───────────────────────────────────────────────────────────
# ── task catalogue ────────────────────────────────────────────────────────────
# The old 39-task catalogue was removed; tasks are being rebuilt one at a time.
# TASK_DEFS is UI/status METADATA ONLY — it never holds Python callables. The
# single mapping from task key to function lives in the bot (TASK_FUNCTIONS /
# get_task_callable) so Test mode and Run mode cannot drift apart.
SUBTASK_ORDER = ["vip_collect", "tutorial"]

TASK_DEFS: dict[str, dict] = {
    "vip_collect": {
        "label":       "VIP Collect",
        "header":      "VipCollect",
        "status_attr": "_vip_collect_status",
        "sub_attr":    None,
    },
    "tutorial": {
        "label":       "Tutorial",
        # No sheet column yet — set to a header string (e.g. "Tutorial") once
        # one exists in the Google Sheet, and update_status() will start
        # writing to it automatically.
        "header":      None,
        "status_attr": "_tutorial_status",
        "sub_attr":    None,
    },
}

SHORT_LABELS = {
    "vip_collect": "VIP",
    "tutorial":    "TUT",
}

# Raw sheet headers for tasks whose header is None and which write values via
# update_status(device, "<Header>", value). Empty in this build; kept so a
# future task can register one without new plumbing.
RAW_STATUS_HEADER_TO_TASK: dict[str, str] = {}
RAW_STATUS_HEADER_TO_ROW_FIELD: dict[str, str] = {}

# Sheet headers owned by the deleted tasks. A status cache written by the old
# 39-task build can still hold pending writes for these; flushing one would make
# _find_or_create_status_col() recreate the obsolete column. Membership is an
# explicit DENY list rather than "anything not in TASK_DEFS", so operational
# headers (Issues, LastUpdate, DeviceStartup, TargetApp …) and any future non-task
# header are preserved automatically.
DELETED_TASK_HEADERS: frozenset = frozenset({
    "Tutorial", "crisis1", "crisis2", "BreakShield", "DailyReward", "MegaSlots",
    "OpenResource", "Building5", "Tekkman", "FreeRelease", "JoinGuild",
    "TimeSpace", "GoldChest", "ChangeName", "StorylineCollect",
    "NewServerReward", "SupplySupport", "MailCollect", "Interstellar",
    "Patricks", "Redeem", "AppSupply", "Handbook", "GuildWarming",
    "MapLocation", "FailExplore", "Monster2", "Easter", "WheelOfCollapse",
    "DwarfStar", "EnergyLode", "GoldUse", "TravelShop", "AppLevel",
    "TenthSignup", "ThirteenthAnniv", "DwarfStarNew", "DwarfStar1723",
})


def sanitize_task_keys(keys, where: str = "", allow_sets: bool = False,
                       _warned: set = set()):
    """
    Keep only task keys this build still knows about.

    Saved state outlives the code: controller_state.json, controller_states.json,
    task_sets.json and per-DeviceType task_config all happily contain keys for
    tasks that no longer exist. Passing one to a worker would reach
    get_task_callable() and be reported as an unknown task, so they are dropped
    here instead — once, with a warning, rather than on every read.

    `allow_sets` separates the two stages, which is not cosmetic:

      True   BEFORE expansion — a saved UI selection may legitimately name a
             task SET, which TaskSetsManager resolves later.
      False  AFTER expansion, and for the CONTENTS of a set — the result must be
             concrete TASK_DEFS keys only.

    Keeping "set:" unconditionally was a real leak. A set containing another
    set (Outer -> ["set:Inner", ...]) expanded to ["set:Inner", ...], and
    "set:Inner" then survived the final worker-argument filter all the way to
    bot.get_task_callable("set:Inner"). Nested sets are not a supported feature,
    so they are dropped rather than resolved recursively.
    """
    out, dropped = [], []
    for k in (keys or []):
        if not isinstance(k, str):
            dropped.append(k)
        elif k in TASK_DEFS:
            out.append(k)
        elif allow_sets and k.startswith("set:"):
            out.append(k)
        else:
            dropped.append(k)
    if dropped:
        # NEVER set(dropped): a hand-edited or corrupt JSON file can legally
        # contain {}, [] or {"task": "..."} , and set() on those raises
        # TypeError: unhashable type — turning a bad config into a crash on
        # load. Deduplicate on a string LABEL instead. The original objects stay
        # in the caller's `invalid` list so provenance is unaltered.
        dropped_labels = sorted({f"{type(v).__name__}:{v!r}" for v in dropped})
        sig = (where, tuple(dropped_labels))
        if sig not in _warned:
            _warned.add(sig)
            _multi_log.warning(
                f"[TASKS] discarded {len(dropped_labels)} stale task key(s) from "
                f"{where or 'saved state'}: {dropped_labels} "
                f"— not in TASK_DEFS for this build"
            )
    return out


def _sanitize_saved_state(state, where: str):
    """
    Validate the SHAPE of a loaded UI state snapshot. Nothing more.

    This function used to run sanitize_task_keys over task_config and
    multi_tasks, which destroyed the very evidence the caller needs:

        ["daily_reward"] -> []   then validate_selection([]) -> had_input=False

    An invalid stored selection therefore became indistinguishable from a
    deliberately empty one, and Run mode happily started a setup-only run for a
    device whose configured work no longer exists.

    So list CONTENTS are passed through untouched and
    TaskSetsManager.validate_selection makes the authoritative
    valid / invalid / had_input decision. Only malformed sections — a
    non-dict field, or a value that is not a list — are dropped here, since
    those cannot be classified at all.
    """
    if not isinstance(state, dict):
        return {}
    # All four task-bearing fields, and the OUTER shape as well as the inner
    # one. Previously a non-dict section (task_config=[], multi_tasks="bad")
    # survived untouched and blew up later on .items(); the provenance fields
    # were not checked at all.
    for field in ("task_config", "multi_tasks",
                  "invalid_task_config", "invalid_multi_tasks"):
        if field not in state:
            continue                      # absent -> normal default behaviour
        section = state.get(field)
        if not isinstance(section, dict):
            _multi_log.warning(
                f"[TASKS] {where}:{field} is {type(section).__name__}, expected "
                f"a dict — ignoring it")
            state[field] = {}
            continue
        kept = {k: list(v) for k, v in section.items() if isinstance(v, list)}
        dropped = [k for k, v in section.items() if not isinstance(v, list)]
        if dropped:
            _multi_log.warning(
                f"[TASKS] {where}:{field} — dropped malformed (non-list) "
                f"entr(ies) for {dropped}")
        state[field] = kept

    # run_checks is dict[adb_id, bool] rather than dict[str, list], so it needs
    # its own rule — but the same guarantee: no JSON-compatible value may make
    # .items() fail downstream.
    if "run_checks" in state:
        rc = state.get("run_checks")
        if not isinstance(rc, dict):
            _multi_log.warning(
                f"[STATE] {where}:run_checks is {type(rc).__name__}, expected "
                f"a dict — ignoring it")
            state["run_checks"] = {}
        else:
            clean, bad = {}, []
            for k, v in rc.items():
                if not isinstance(k, str):
                    bad.append(k)
                elif isinstance(v, bool):
                    clean[k] = v
                elif isinstance(v, int) and v in (0, 1):
                    clean[k] = bool(v)      # JSON round-trips can yield 0/1
                else:
                    bad.append(k)
            if bad:
                _multi_log.warning(
                    f"[STATE] {where}:run_checks — dropped {len(bad)} malformed "
                    f"entr(ies): {sorted(map(str, bad))}")
            state["run_checks"] = clean
    return state


def _tasks_short_label(keys: list[str], max_chars: int = 38) -> str:
    """Turn a list of task keys into a compact short-label string for display."""
    if not keys:
        return "no tasks"
    def _label(k):
        if k.startswith("set:"):
            return f"📦{k[4:]}"
        return SHORT_LABELS.get(k, k[:4])
    parts = [_label(k) for k in keys]
    joined = " · ".join(parts)
    if len(joined) <= max_chars:
        return joined
    # truncate with count suffix
    shown = []
    used = 0
    for p in parts:
        if used + len(p) + 3 > max_chars - 6:
            break
        shown.append(p)
        used += len(p) + 3
    return " · ".join(shown) + f"  +{len(parts)-len(shown)}"

# ── colour palette ─────────────────────────────────────────────────────────────
BG_BASE  = "#0E0E1A"
BG_MID   = "#141420"
BG_PANEL = "#1A1A2C"
BG_CELL  = "#23233A"

PRI      = "#F47840"
PRI_DRK  = "#C45E28"
ACC_BLUE = "#1A78D0"
ACC_GRN  = "#2E7D32"
ACC_YEL  = "#C07800"

FG_MAIN  = "#E0E0EE"
FG_DIM   = "#5A5A7A"
FG_ERR   = "#E05A40"

BADGE_DONE    = ("#1A5C22", "#5CDD5C")
BADGE_RUNNING = ("#6A3800", "#FFA040")
BADGE_IDLE    = ("#1E1E32", "#6060A0")
BADGE_FAILED  = ("#5A1010", "#FF6060")
BADGE_STOPPED = ("#222238", "#7070A0")
BADGE_STOPPING= ("#222238", "#7070A0")
BADGE_QUEUED  = ("#1A1A3A", "#8080C0")
BADGE_RETRY   = ("#3A2000", "#FFA040")   # orange — ADB connect retry

CLR_DONE    = "#2E7D32"
CLR_DONE_FG = "#FFFFFF"
CLR_RUN     = "#C07000"
CLR_RUN_FG  = "#FFFFFF"
CLR_EMPTY   = "#8B1A1A"
CLR_EMPTY_FG= "#FFFFFF"
CLR_FAIL    = "#6A1515"
CLR_ERR     = "#5A5A5A"

F   = "Segoe UI"
FM  = "Consolas"
FB  = (F, 13, "bold"); FH = (F, 10, "bold"); FN = (F, 9); FS = (F, 8)
FNB = (F, 9, "bold");  FSB = (F, 8, "bold"); FMN = (FM, 9); FMS = (FM, 8)


# ── file loggers ───────────────────────────────────────────────────────────────
def _make_logger(name: str, fname: str) -> logging.Logger:
    lg = logging.getLogger(name)
    lg.setLevel(logging.DEBUG); lg.propagate = False
    if not lg.handlers:
        # FIX 5: Use delayed-open handler — no persistent file lock
        fh = logging.handlers.RotatingFileHandler(fname, mode="a", encoding="utf-8",
                                                   maxBytes=0, backupCount=0)              if False else None  # placeholder — real handler below
        class _DFH(logging.Handler):
            def __init__(self, fn):
                super().__init__()
                self.fn = fn
                self.setFormatter(logging.Formatter(
                    "%(asctime)s  %(levelname)-8s  %(message)s", "%Y-%m-%d %H:%M:%S"))
            def emit(self, record):
                try:
                    with open(self.fn, "a", encoding="utf-8") as _f:
                        _f.write(self.format(record) + "\n")
                except Exception:
                    self.handleError(record)
        lg.addHandler(_DFH(fname))
    return lg

_ui_log    = _make_logger("devicepilot.ui",    "controller_ui.log")
_multi_log = _make_logger("devicepilot.multi", "controller_multi.log")
_TAG_LVL   = {"ok": logging.INFO, "info": logging.INFO,
              "warn": logging.WARNING, "err": logging.ERROR, "dim": logging.DEBUG}


# ==============================================================================
# ETA TRACKER
# ==============================================================================
class EtaTracker:
    MAX_SAMPLES = 10

    def __init__(self, path: str = ETA_FILE):
        self.path    = path
        self._data   = {}
        self._starts: dict[tuple, float] = {}
        self._lock   = threading.Lock()
        self._load()

    def _load(self):
        try:
            if os.path.exists(self.path):
                with open(self.path, "r", encoding="utf-8") as f:
                    self._data = json.load(f)
        except Exception:
            self._data = {}

    def _save(self):
        try:
            with open(self.path, "w", encoding="utf-8") as f:
                json.dump(self._data, f, indent=2)
        except Exception:
            pass

    def start(self, device_id: str, task_key: str):
        with self._lock:
            self._starts[(device_id, task_key)] = time.time()

    def finish(self, device_id: str, task_key: str):
        with self._lock:
            t0 = self._starts.pop((device_id, task_key), None)
            if t0 is None:
                return
            elapsed = time.time() - t0
            dev_data = self._data.setdefault(device_id, {})
            samples  = dev_data.setdefault(task_key, [])
            samples.append(round(elapsed, 1))
            if len(samples) > self.MAX_SAMPLES:
                samples.pop(0)
        self._save()

    def avg(self, device_id: str, task_key: str) -> float | None:
        samples = self._data.get(device_id, {}).get(task_key, [])
        return (sum(samples) / len(samples)) if samples else None


_eta = EtaTracker()


# ==============================================================================
# INSTANT STOP — thread-local monkey-patch
# ==============================================================================
class StopTaskNow(Exception):
    pass

_thread_local = threading.local()


def _install_guard(bot):
    if getattr(bot, "_stop_guard_installed", False):
        return
    orig_click = bot.click_in_bounding_box
    orig_adb   = bot._adb_shell

    def _g_click(*a, **kw):
        ev = getattr(_thread_local, "stop_event", None)
        if ev and ev.is_set():
            raise StopTaskNow()
        return orig_click(*a, **kw)

    def _g_adb(*a, **kw):
        ev = getattr(_thread_local, "stop_event", None)
        if ev and ev.is_set():
            raise StopTaskNow()
        return orig_adb(*a, **kw)

    bot.click_in_bounding_box   = _g_click
    bot._adb_shell               = _g_adb
    bot._stop_guard_installed    = True
    bot._orig_click              = orig_click
    bot._orig_adb                = orig_adb


def _remove_guard(bot):
    if getattr(bot, "_stop_guard_installed", False):
        bot.click_in_bounding_box = bot._orig_click
        bot._adb_shell             = bot._orig_adb
        bot._stop_guard_installed  = False


# ==============================================================================
# MODULE-LEVEL ADB HELPERS (no bot module required)
# ==============================================================================
def _adb_vpn_check(adb_id: str, timeout: int = 2) -> bool:
    """Check tun0 on device via raw ADB — no bot module needed, safe from any thread."""
    try:
        r = subprocess.run(
            ["adb", "-s", adb_id, "shell", "ip", "link", "show", "tun0"],
            capture_output=True, text=True, timeout=timeout,
        )
        return r.returncode == 0 and "tun0" in r.stdout
    except Exception:
        return False


def _adb_connect_quiet(adb_id: str, timeout: int = 6) -> None:
    """Fire-and-forget adb connect. Errors silently ignored."""
    try:
        subprocess.run(["adb", "connect", adb_id],
                       capture_output=True, text=True, timeout=timeout)
    except Exception:
        pass


# ==============================================================================
# ── Host/global internet check ────────────────────────────────────────────────
# Used by _handle_internet_down_emergency and internet_restored_restart.
# Checks PC/host network, NOT emulator VPN route.
def _host_internet_ok() -> bool:
    """
    Check host-machine (PC) internet, not emulator VPN route.
    Tries Windows ping to 8.8.8.8, then ping to 1.1.1.1, then HTTPS fallback.
    Returns True if host internet appears functional.
    """
    try:
        r = subprocess.run(
            ["ping", "-n", "1", "-w", "2000", "8.8.8.8"],
            capture_output=True, text=True, timeout=5
        )
        if "TTL=" in (r.stdout or "") or "bytes from" in (r.stdout or ""):
            return True
    except Exception:
        pass
    try:
        r = subprocess.run(
            ["ping", "-n", "1", "-w", "2000", "1.1.1.1"],
            capture_output=True, text=True, timeout=5
        )
        if "TTL=" in (r.stdout or "") or "bytes from" in (r.stdout or ""):
            return True
    except Exception:
        pass
    try:
        import urllib.request
        resp = urllib.request.urlopen("https://www.google.com/generate_204", timeout=4)
        if resp.status == 204:
            return True
    except Exception:
        pass
    return False


# MULTIPROCESSING ENTRY POINT — must be top-level to be picklable on Windows
# ==============================================================================
def _mp_worker_entry(dev_id, task_keys, task_defs,
                     cfg_data, skip_before, status_q, stop_flag,
                     pause_flag=None):
    """
    `pause_flag` is a separate multiprocessing.Event from `stop_flag`.

    stop_flag  = "shut down, the run is over"
    pause_flag = "hold still, the host lost internet — you are still alive"

    They must never be conflated: setting stop_flag for a network outage would
    tear down a healthy run that only needed to wait.

    Defaulted to None so an older controller build can still spawn this worker.
    """
    import sys, importlib.util
    from pathlib import Path
    bot_path = cfg_data.get("_bot_path", "")
    p    = Path(bot_path)
    name = f"devicepilot_engine_{abs(hash(str(p.resolve())))}"
    spec = importlib.util.spec_from_file_location(name, str(p))
    mod  = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    mod.device_worker(
        dev_id, task_keys, task_defs,
        cfg_data, skip_before, status_q, stop_flag, pause_flag,
    )


# ==============================================================================
# BOT BRIDGE
# ==============================================================================

# ==============================================================================
# STATE MANAGER  — saves / restores UI session state to disk
# ==============================================================================
class StateManager:
    """Persists controller UI selections to controller_state.json."""

    def __init__(self, path: str = STATE_FILE):
        self.path = path

    def save(self, state: dict):
        try:
            with open(self.path, "w", encoding="utf-8") as f:
                json.dump(state, f, indent=2)
        except Exception as ex:
            print(f"[StateManager] save failed: {ex}")

    def load(self) -> dict:
        try:
            if os.path.exists(self.path):
                with open(self.path, "r", encoding="utf-8") as f:
                    return _sanitize_saved_state(json.load(f), "controller_state.json")
        except Exception as ex:
            print(f"[StateManager] load failed: {ex}")
        return {}


# ==============================================================================
# NAMED STATE MANAGER — multiple named UI snapshots in controller_states.json
# ==============================================================================

class NamedStateManager:
    """
    Stores named UI state snapshots alongside the default autosave.
    File format: { "<name>": { ...state dict... }, ... }
    """

    def __init__(self, path: str = NAMED_STATES_FILE):
        self.path   = path
        self._states: dict[str, dict] = {}
        self._load()

    def _load(self):
        try:
            if os.path.exists(self.path):
                with open(self.path, "r", encoding="utf-8") as f:
                    data = json.load(f)
                    self._states = data if isinstance(data, dict) else {}
        except Exception as ex:
            print(f"[NamedStateManager] load failed: {ex}")
            self._states = {}

    def _save(self):
        try:
            with open(self.path, "w", encoding="utf-8") as f:
                json.dump(self._states, f, indent=2)
        except Exception as ex:
            print(f"[NamedStateManager] save failed: {ex}")

    def save(self, name: str, state: dict):
        name = name.strip()
        if not name:
            return
        self._states[name] = state
        self._save()

    def load(self, name: str) -> dict:
        return _sanitize_saved_state(
            dict(self._states.get(name.strip(), {})),
            f"controller_states.json[{name.strip()}]")

    def delete(self, name: str):
        self._states.pop(name.strip(), None)
        self._save()

    def list_names(self) -> list[str]:
        return sorted(self._states.keys())


# ==============================================================================
# TASK SETS MANAGER  — named groups of tasks saved to task_sets.json
# ==============================================================================
class TaskSetsManager:
    """
    Manages named task sets — user-defined collections of individual tasks.

    A task set is stored as:
        { "name": "Dailies", "tasks": ["vip_collect", ...] }

    The set name is prefixed with "set:" when used as a task key so it can
    co-exist with individual task keys without collision.
    """

    SET_PREFIX = "set:"

    def __init__(self, path: str = TASK_SETS_FILE):
        self.path = path
        self._sets: list[dict] = []   # [{name, tasks}, ...]
        self._load()

    # ── persistence ──────────────────────────────────────────────────────────
    def _load(self):
        try:
            if os.path.exists(self.path):
                with open(self.path, "r", encoding="utf-8") as f:
                    data = json.load(f)
                    raw = data if isinstance(data, list) else []
                    # Sets saved by an older build can name tasks this one no
                    # longer has. Filter on load so nothing downstream — the
                    # editor, the expansion, or a worker — ever sees them.
                    #
                    # allow_sets=False: a set's CONTENTS must be concrete tasks.
                    # A nested "set:Other" is dropped here rather than expanded.
                    self._sets = [
                        {"name": s.get("name", ""),
                         "tasks": sanitize_task_keys(
                             s.get("tasks", []),
                             where=f"task set {s.get('name', '')!r}",
                             allow_sets=False)}
                        for s in raw if isinstance(s, dict) and s.get("name")
                    ]
        except Exception:
            self._sets = []

    def _save(self):
        try:
            with open(self.path, "w", encoding="utf-8") as f:
                json.dump(self._sets, f, indent=2)
        except Exception as ex:
            print(f"[TaskSetsManager] save failed: {ex}")

    # ── CRUD ─────────────────────────────────────────────────────────────────
    def all_sets(self) -> list[dict]:
        return list(self._sets)

    def get_set(self, name: str) -> dict | None:
        for s in self._sets:
            if s["name"] == name:
                return s
        return None

    def add_or_update(self, name: str, tasks: list[str]):
        """
        Create or replace a task set by name.

        Contents are sanitized on the way IN as well as on load, so a nested
        set reference or a stale key can never be persisted in the first place.
        """
        name = name.strip()
        if not name:
            return
        clean = sanitize_task_keys(tasks, where=f"task set {name!r}",
                                   allow_sets=False)
        for s in self._sets:
            if s["name"] == name:
                s["tasks"] = clean
                self._save()
                return
        self._sets.append({"name": name, "tasks": clean})
        self._save()

    def delete(self, name: str):
        self._sets = [s for s in self._sets if s["name"] != name]
        self._save()

    # ── key helpers ───────────────────────────────────────────────────────────
    def set_key(self, name: str) -> str:
        return f"{self.SET_PREFIX}{name}"

    def is_set_key(self, key: str) -> bool:
        return key.startswith(self.SET_PREFIX)

    def name_from_key(self, key: str) -> str:
        return key[len(self.SET_PREFIX):]

    def expand_keys(self, keys: list[str]) -> list[str]:
        """
        Expand any set: keys → individual task keys. Deduplicate preserving order.

        The result is sanitized with allow_sets=False, so the output is CONCRETE
        task keys only. Expansion is the last point at which a stale key — or a
        nested "set:" reference from an old file — could turn into something a
        worker would try to run.
        """
        out, seen, missing = [], set(), []
        for k in keys:
            if self.is_set_key(k):
                name = self.name_from_key(k)
                s = self.get_set(name)
                if s is None:
                    # Silently expanding to [] turned "run the Dailies set" into
                    # a setup-only run with no indication anything was wrong.
                    missing.append(name)
                    continue
                expanded = s["tasks"]
            else:
                expanded = [k]
            for t in expanded:
                if t not in seen:
                    seen.add(t)
                    out.append(t)
        if missing:
            _multi_log.warning(
                f"[TASKS] task set(s) referenced but not found: {missing} — "
                f"expanded to nothing")
        return sanitize_task_keys(out, where="expanded task keys",
                                  allow_sets=False)

    def validate_selection(self, keys, where: str = "") -> dict:
        """
        Pre-expansion classification of a stored selection.

        Returns {"valid": [...], "invalid": [...], "had_input": bool}.

        A structured return, not a filtered list plus a `last_validation`
        attribute: the side channel was one stray call away from a caller
        reading another selection's verdict, and it made the "was there input?"
        question invisible at the call site.

        sanitize_task_keys(allow_sets=True) cannot do this alone — it has no view
        of the manager — so a reference to a set the user has since deleted
        survives it and only disappears at expansion, by which point the caller
        has already decided there is work to do.
        """
        raw = list(keys or [])
        kept, gone = [], []
        allowed = sanitize_task_keys(raw, where=where, allow_sets=True)
        for k in allowed:
            if self.is_set_key(k) and self.get_set(self.name_from_key(k)) is None:
                gone.append(k)
            else:
                kept.append(k)
        # Anything sanitize_task_keys itself rejected counts as discarded too —
        # a deleted task key, or a non-string that was never a key at all.
        gone += [k for k in raw if k not in allowed]
        if gone:
            _multi_log.warning(
                f"[TASKS] dropped reference(s) to missing/invalid task(s) from "
                f"{where or 'selection'}: {gone}")
        return {"valid": kept, "invalid": gone, "had_input": bool(raw)}

    def all_keys(self) -> list[str]:
        """Return set: keys for all sets, for use in task selectors."""
        return [self.set_key(s["name"]) for s in self._sets]

    def label_for_key(self, key: str) -> str:
        if self.is_set_key(key):
            return f"📦 {self.name_from_key(key)}"
        return TASK_DEFS.get(key, {}).get("label", key)


class BotBridge:
    def __init__(self, bot_path: str):
        self.bot_path            = str(bot_path)
        self.bot                 = None
        self.rows_by_device:     dict[str, dict] = {}
        self._last_refresh_time: float = 0.0
        self._refresh_cooldown:  float = 60.0

    def set_path(self, path: str):
        _remove_guard(self.bot) if self.bot else None
        self.bot = None
        self.rows_by_device = {}
        self.bot_path = str(path)

    # ── module loading ─────────────────────────────────────────────────────────
    def load_bot(self):
        if self.bot is not None:
            return self.bot
        p = Path(self.bot_path)
        if not p.exists():
            raise FileNotFoundError(f"Bot file not found: {p}")
        name = f"devicepilot_engine_{abs(hash(str(p.resolve())))}"
        spec = importlib.util.spec_from_file_location(name, str(p))
        mod  = importlib.util.module_from_spec(spec)
        sys.modules[name] = mod
        spec.loader.exec_module(mod)
        self.bot = mod
        _install_guard(mod)
        return mod

    def reload_code(self):
        if self.bot:
            _remove_guard(self.bot)
            name = self.bot.__name__
            sys.modules.pop(name, None)
        self.bot = None
        self.rows_by_device = {}
        return self.load_bot()

    def reload_pages(self):
        bot = self.load_bot()
        bot._PAGES_CACHE = None
        return bot.load_pages_config(force_reload=True)

    def run_daily_reset(self) -> bool:
        bot = self.load_bot()
        ws, all_vals = bot._load_control_sheet(refresh_values=True)
        did_reset = bot.maybe_refresh_daily_statuses(ws, all_vals)
        if did_reset:
            # Discard stale pre-reset snapshot and re-read sheet fresh after
            # maybe_refresh_daily_statuses() cleared the status cells.
            if hasattr(bot, "_CONTROL_VALUES"):
                bot._CONTROL_VALUES = None
            ws, all_vals = bot._load_control_sheet(refresh_values=True)
        # Always build full cache from current (post-reset or unchanged) values.
        cfg = bot.read_control_config(ws, all_vals)
        self.rows_by_device     = {r["device_id"]: r for r in cfg.get("rows", [])}
        self._last_cfg          = cfg
        self._raw_vals          = all_vals
        self._last_refresh_time = time.time()
        self._seed_globals()
        return bool(did_reset)

    # ── sheet ──────────────────────────────────────────────────────────────────
    def refresh_sheet(self, force: bool = False):
        import time as _time
        now = _time.time()
        if not force and (now - self._last_refresh_time) < self._refresh_cooldown:
            print(f"[refresh_sheet] skipped — data is {now - self._last_refresh_time:.0f}s old")
            return getattr(self, "_last_cfg", {})
        self._last_refresh_time = now
        bot = self.load_bot()
        if hasattr(bot, "_reset_gs_client"):
            bot._reset_gs_client()
        t0 = _time.time()
        ws, vals = bot._load_control_sheet(refresh_values=True)
        print(f"[refresh_sheet] loaded in {_time.time()-t0:.1f}s — {len(vals)} rows")
        cfg = bot.read_control_config(ws, vals)
        self.rows_by_device = {r["device_id"]: r for r in cfg.get("rows", [])}
        self._last_cfg = cfg
        self._raw_vals = vals  # keep for Sheet tab
        self._seed_globals()
        return cfg

    def _lookup_row(self, adb_id: str) -> dict:
        if adb_id in self.rows_by_device:
            return self.rows_by_device[adb_id]
        port = adb_id.split(":")[-1] if ":" in adb_id else adb_id
        for candidate in (f"localhost:{port}", f"127.0.0.1:{port}", port):
            if candidate in self.rows_by_device:
                return self.rows_by_device[candidate]
        return {}

    def _seed_globals(self):
        bot  = self.load_bot()
        rows = list(self.rows_by_device.values())
        cfg  = getattr(self, "_last_cfg", None) or {}
        bot._vip_collect_status       = {r["device_id"]: r.get("vip_collect_status",       "") for r in rows}
        bot._device_type_map          = {r["device_id"]: r.get("device_type", "").strip().lower() for r in rows}
        bot._available_version        = cfg.get("available_version", "")
        bot._DEVICE_ROW_CACHE.update(cfg.get("device_row_cache", {}))


    def _build_cfg_data(self) -> dict:
        bot = self.load_bot()
        cfg = getattr(self, "_last_cfg", None) or {}
        return {
            "_bot_path":                self.bot_path,
            "vip_collect_status":       dict(getattr(bot, "_vip_collect_status",        {})),
            "device_type_map":          dict(getattr(bot, "_device_type_map",           {})),
            "available_version":         getattr(bot, "_available_version",              ""),
            "device_row_cache":          dict(getattr(bot, "_DEVICE_ROW_CACHE",           {})),
            # Delivered through cfg_data rather than as another Process argument.
            "record_video":            bool(getattr(self, "_record_video_flag", False)),
        }

    def status_snapshot(self, dev_id: str) -> dict[str, str]:
        r = self._lookup_row(dev_id)
        return {
            "vip_collect":   r.get("vip_collect_status",   ""),
        }

    # ── device conf ───────────────────────────────────────────────────────────
    def list_conf_devices(self) -> list[dict]:
        bot = self.load_bot()
        raw = bot.parse_bluestacks_conf(bot.BLUESTACKS_CONF)
        out = []
        for d in raw:
            adb_id = f"localhost:{d['port']}"
            if adb_id == "localhost:5555":
                continue
            sheet_row = self._lookup_row(adb_id)
            out.append({
                "adb_id":      adb_id,
                "name":        d.get("name", adb_id),
                "instance":    d.get("instance", ""),
                "device_type": sheet_row.get("device_type", ""),
                "statuses":    self.status_snapshot(adb_id),
            })
        return out

    def connect_selected(self, adb_ids: list[str], log_fn=None) -> list[dict]:
        bot = self.load_bot()
        self.refresh_sheet()
        alive = []
        for adb_id in adb_ids:
            if log_fn:
                log_fn(f"  Connecting {adb_id} …", "dim")
            try:
                bot.connect_to_devices(adb_id)
            except Exception as e:
                if log_fn:
                    log_fn(f"  connect error {adb_id}: {e}", "err")
            ok = bot._adb_ping(adb_id)
            if ok:
                sheet_row = self._lookup_row(adb_id)
                alive.append({
                    "adb_id":      adb_id,
                    "name":        sheet_row.get("friendly", adb_id),
                    "device_type": sheet_row.get("device_type", ""),
                    "statuses":    self.status_snapshot(adb_id),
                })
                if log_fn:
                    log_fn(f"  ✓ online  {adb_id}", "ok")
            else:
                if log_fn:
                    log_fn(f"  ✗ offline {adb_id}", "warn")
        return alive

    # ── sync devices ─────────────────────────────────────────────────────────
    def sync_devices(self) -> dict:
        """
        Smart-sync bluestacks.conf → control sheet.
        Adds missing devices; updates changed names only.
        Removes rows whose adb_id is no longer in BlueStacks conf.
        Returns summary dict: {added, name_updated, unchanged, removed, total}.
        """
        bot = self.load_bot()
        ws, all_vals = bot._load_control_sheet(refresh_values=True)
        result = bot.maybe_refresh_devices_from_conf(ws, all_vals, uncheck_trigger=False)

        # ── Remove rows not in conf ───────────────────────────────────────────
        # Build set of adb_ids currently in BlueStacks conf
        conf_raw  = bot.parse_bluestacks_conf(bot.BLUESTACKS_CONF)
        conf_ids  = {f"localhost:{d['port']}" for d in conf_raw
                     if str(d.get("port", "")) != "5555"}

        # Re-read sheet after add/update
        ws2, vals2 = bot._load_control_sheet(refresh_values=True)
        data_start = bot.DATA_START_ROW - 1   # 0-based
        stale_rows: list[tuple[int, str, str]] = []   # (row_num_1based, adb_id, name)

        for offset, r in enumerate(vals2[data_start:]):
            row_num   = bot.DATA_START_ROW + offset
            name_cell = r[0].strip() if len(r) > 0 else ""
            adb_cell  = r[1].strip() if len(r) > 1 else ""
            if not name_cell and not adb_cell:
                continue
            adb_id = adb_cell or (name_cell if ":" in name_cell else "")
            if not adb_id:
                continue
            if adb_id not in conf_ids:
                stale_rows.append((row_num, adb_id, name_cell))

        # Delete stale rows in reverse order so row numbers stay valid
        removed = []
        for row_num, adb_id, name in sorted(stale_rows, reverse=True):
            try:
                bot._sheets_call(ws2.delete_rows, row_num)
                removed.append({"adb_id": adb_id, "name": name})
                print(f"[sync_devices] removed stale row {row_num}: {adb_id} ({name})")
            except Exception as ex:
                print(f"[sync_devices] failed to remove row {row_num}: {ex}")

        result["removed"] = removed

        # Re-read sheet one final time for accurate total
        _, vals3 = bot._load_control_sheet(refresh_values=True)
        cfg = bot.read_control_config(ws2, vals3)
        self.rows_by_device   = {r["device_id"]: r for r in cfg.get("rows", [])}
        self._last_cfg        = cfg
        self._raw_vals        = vals3
        self._last_refresh_time = time.time()
        self._seed_globals()
        result["total"] = len(self.rows_by_device)
        return result

    def get_conf_devices_raw(self) -> list[dict]:
        """Parse bluestacks.conf — returns raw list of {name, port, instance}."""
        bot = self.load_bot()
        return bot.parse_bluestacks_conf(bot.BLUESTACKS_CONF)

    # ── toggle status ─────────────────────────────────────────────────────────
    def toggle_status(self, dev_id: str, task_key: str) -> str:
        header = TASK_DEFS[task_key]["header"]
        # L: block toggle for tasks whose status is a raw value, not "done/undone"
        if header is None:
            raise ValueError(
                f"Task '{task_key}' has no sheet header (header=None) — "
                f"it stores a raw value or uses custom status logic and cannot "
                f"be toggled as done/undone manually."
            )
        bot    = self.load_bot()
        current   = (self.status_snapshot(dev_id).get(task_key, "") or "").strip().lower()
        new_value = "" if current == "done" else "done"
        bot._PENDING_STATUS.setdefault(dev_id, {}).pop(header, None)
        bot.update_status(dev_id, header, new_value)
        bot.flush_status(dev_id)
        self.refresh_sheet(force=True)
        return new_value

    # ── task runner (threading — Test mode) ──────────────────────────────────
    def run_tasks(self, dev_id: str, task_keys: list[str],
                  skip_before: bool, stop: threading.Event,
                  log_fn=None) -> tuple[bool, str]:
        bot = self.load_bot()
        # TWO thread-locals, both required, both set on THIS worker thread.
        #
        #   controller's — stops the monkey-patched click_in_bounding_box and
        #                  _adb_shell wrappers installed below
        #   bot's        — stops guarded_sleep, stop_aware_sleep, the pause
        #                  waits and every internal bot loop
        #
        # Only the first was being set, so bot._stop_requested() stayed False
        # for the whole of Test mode and the bot's own waits ignored Stop.
        _thread_local.stop_event = stop
        try:
            bot._thread_local.stop_event = stop
        except Exception as exc:      # a bot build without _thread_local
            _multi_log.warning(f"[TEST-STOP] could not set bot stop event: {exc!r}")
        self._reset_state(dev_id)

        def _log(msg: str, tag: str = "dim"):
            if log_fn:
                log_fn(msg, tag)

        dlog = bot._get_device_logger(dev_id)
        _t_run_start = time.time()
        _multi_log.info(
            f"[DIAG] run_tasks ── {dev_id} START  tasks={task_keys}  "
            f"skip_before={skip_before}  t={_t_run_start:.3f}"
        )

        try:
            # Bail immediately if stop was already requested before we even started
            if stop.is_set():
                return False, "stopped"

            # Retry connect up to 3 times — device may not be ready immediately
            connected = False
            for _attempt in range(3):
                _t_conn = time.time()
                _multi_log.info(
                    f"[DIAG] run_tasks ── {dev_id} connect attempt {_attempt+1}/3 "
                    f"at t={_t_conn:.3f}"
                )
                try:
                    bot.connect_to_devices(dev_id)
                except Exception as _ce:
                    _log(f"  connect attempt {_attempt + 1} error: {_ce}", "warn")
                    _multi_log.warning(
                        f"[DIAG] run_tasks ── {dev_id} connect_to_devices exception "
                        f"attempt {_attempt+1}: {_ce}"
                    )
                _t_wait = time.time()
                ok_wait = bot._adb_wait_for_device(dev_id, timeout=15, interval=2)
                _multi_log.info(
                    f"[DIAG] run_tasks ── {dev_id} _adb_wait_for_device → {ok_wait} "
                    f"in {time.time()-_t_wait:.3f}s (attempt {_attempt+1})"
                )
                if ok_wait:
                    connected = True
                    break
                _log(f"  Device not responding — retrying ({_attempt + 1}/3)…", "warn")
                time.sleep(5)

            if not connected:
                _multi_log.error(
                    f"[DIAG] run_tasks ── {dev_id} NOT CONNECTED after 3 attempts — aborting"
                )
                return False, "Device not connected after 3 attempts"

            _multi_log.info(
                f"[DIAG] run_tasks ── {dev_id} connected in "
                f"{time.time()-_t_run_start:.3f}s total"
            )

            try:
                if hasattr(bot, "_verify_touch_device"):
                    bot._verify_touch_device(dev_id, dlog)
            except Exception:
                pass
            # Refresh sheet before seeding globals so "done" statuses are current
            try:
                self.refresh_sheet(force=True)
            except Exception as _rsex:
                _multi_log.warning(f"[DIAG] run_tasks ── pre-run sheet refresh failed: {_rsex}")
            self._seed_globals()

            # Check stop again before running prepare_target_app
            if stop.is_set():
                return False, "stopped"

            _t_prep = time.time()
            ok, msg = self._prepare(dev_id, dlog, skip_before, _log)
            _multi_log.info(
                f"[DIAG] run_tasks ── {dev_id} _prepare → ok={ok} msg={msg!r} "
                f"in {time.time()-_t_prep:.3f}s"
            )
            if not ok:
                return False, msg
            _log(f"Prep: {msg}", "dim")
            guard = bot._target_app_guards.get(dev_id)
            last  = "done"
            for task_key in task_keys:
                if stop.is_set():
                    return False, "stopped"
                # Refresh before EVERY task. _run_one replaces its own local
                # guard after full_restart or vpn_down, but that never
                # propagated back here — so with more than one task the next one
                # would be handed the stopped TargetAppGuard from before the recovery.
                # Only VIP exists today; this is the bug that would appear the
                # moment a second task is added.
                guard = bot._target_app_guards.get(dev_id) or guard
                _eta.start(dev_id, task_key)
                _log(f"▶  starting {TASK_DEFS[task_key]['label']}", "info")
                _t_task = time.time()
                _multi_log.info(
                    f"[DIAG] run_tasks ── {dev_id} task START {task_key!r} "
                    f"t={_t_task:.3f}"
                )
                try:
                    result = self._run_one(dev_id, task_key, dlog, guard, stop, _log)
                except StopTaskNow:
                    _log("■  stopped by user", "warn")
                    return False, "stopped"
                # ...and again afterwards, so the value carried into the next
                # iteration reflects any recovery _run_one performed.
                guard = bot._target_app_guards.get(dev_id) or guard
                _eta.finish(dev_id, task_key)
                _multi_log.info(
                    f"[DIAG] run_tasks ── {dev_id} task END {task_key!r} → {result!r} "
                    f"in {time.time()-_t_task:.3f}s"
                )
                last = result
                if result not in ("done", "skipped"):
                    _log(f"✗  {task_key} failed: {result}", "err")
                    return False, result
                _log(f"✓  {TASK_DEFS[task_key]['label']} complete", "ok")

            _multi_log.info(
                f"[DIAG] run_tasks ── {dev_id} ALL DONE  "
                f"total={time.time()-_t_run_start:.3f}s"
            )
            return True, last
        except StopTaskNow:
            return False, "stopped"
        except Exception as exc:
            tb = traceback.format_exc()
            dlog.error(tb)
            _log(f"Exception: {type(exc).__name__}: {exc}", "err")
            _multi_log.error(
                f"[DIAG] run_tasks ── {dev_id} EXCEPTION after "
                f"{time.time()-_t_run_start:.3f}s: {exc}"
            )
            return False, f"{type(exc).__name__}: {exc}"
        finally:
            _thread_local.stop_event = None
            try:
                bot._thread_local.stop_event = None
            except Exception:
                pass
            _multi_log.info(f"[DIAG] run_tasks ── {dev_id} finally block: flushing status to sheets")
            try:
                pending = getattr(bot, "_PENDING_STATUS", {})
                pending_keys = list(pending.get(dev_id, {}).keys())
                _multi_log.info(
                    f"[DIAG] run_tasks ── {dev_id} pending status fields before flush: {pending_keys}"
                )
                bot.flush_status(dev_id)
                _multi_log.info(f"[DIAG] run_tasks ── {dev_id} flush_status completed ✓")
            except Exception as _fe:
                _multi_log.error(f"[DIAG] run_tasks ── {dev_id} flush_status FAILED: {_fe}")
            try:
                g = bot._target_app_guards.pop(dev_id, None)
                if g:
                    g.stop()
                    _multi_log.info(f"[DIAG] run_tasks ── {dev_id} TargetAppGuard stopped")
            except Exception:
                pass
            # Full per-device counter reset on completion (runs regardless of success/fail)
            try:
                self._reset_state(dev_id)
                _multi_log.info(f"[DIAG] run_tasks ── {dev_id} _reset_state() completed in finally ✓")
            except Exception as _re:
                _multi_log.warning(f"[DIAG] run_tasks ── {dev_id} _reset_state in finally failed: {_re}")

    def _prepare(self, dev_id, dlog, skip_before, log_fn):
        bot = self.load_bot()
        _t_prep_start = time.time()
        try:
            activity = bot._get_current_activity(dev_id) or ""
        except Exception:
            activity = ""
        try:
            vpn_up = bool(bot.vpn_activity(dev_id))
        except Exception:
            vpn_up = False
        target_app_open = bot.TARGET_APP_PACKAGE in activity
        _multi_log.info(
            f"[DIAG] _prepare ── {dev_id} ENTRY  "
            f"skip_before={skip_before}  vpn_up={vpn_up}  "
            f"target_app_open={target_app_open}  activity={activity.strip()!r}"
        )
        if skip_before and target_app_open and vpn_up:
            guard = bot.TargetAppGuard(dev_id, dlog)
            guard.start(); guard.set_stage(3)
            guard.set_target_app_opened(); guard.set_main_page_seen()
            bot._target_app_guards[dev_id] = guard
            _multi_log.info(
                f"[DIAG] _prepare ── {dev_id} skip_before path taken — "
                f"attached to existing TargetApp session in {time.time()-_t_prep_start:.3f}s"
            )
            return True, "attached to existing TargetApp session"
        else:
            if skip_before and not (target_app_open and vpn_up):
                _multi_log.warning(
                    f"[DIAG] _prepare ── {dev_id} skip_before=True but conditions NOT met "
                    f"(target_app_open={target_app_open}, vpn_up={vpn_up}) — running prepare_target_app anyway"
                )
            # Retry prepare_target_app up to 3 times — device may need a moment to become ready
            MAX_PREPARE_ATTEMPTS = 3
            for attempt in range(MAX_PREPARE_ATTEMPTS):
                log_fn(f"  prepare_target_app attempt {attempt + 1}/{MAX_PREPARE_ATTEMPTS} …", "dim")
                _t_ba = time.time()
                _multi_log.info(
                    f"[DIAG] _prepare ── {dev_id} prepare_target_app attempt {attempt+1}/"
                    f"{MAX_PREPARE_ATTEMPTS} start t={_t_ba:.3f}"
                )
                try:
                    _multi_log.info(f"[FORCE-STOP] controller startover path: prepare_target_app(force_stop_first=True) — _prepare()")
                    ok = bot.prepare_target_app(dev_id, force_stop_first=True)
                except Exception as exc:
                    log_fn(f"  prepare_target_app exception: {exc}", "warn")
                    _multi_log.error(
                        f"[DIAG] _prepare ── {dev_id} prepare_target_app attempt {attempt+1} "
                        f"EXCEPTION after {time.time()-_t_ba:.3f}s: {exc}"
                    )
                    ok = False
                _multi_log.info(
                    f"[DIAG] _prepare ── {dev_id} prepare_target_app attempt {attempt+1} → "
                    f"ok={ok} in {time.time()-_t_ba:.3f}s"
                )
                if ok:
                    _multi_log.info(
                        f"[DIAG] _prepare ── {dev_id} SUCCESS total prep "
                        f"{time.time()-_t_prep_start:.3f}s"
                    )
                    return True, f"prepare_target_app completed (attempt {attempt + 1})"
                if attempt < MAX_PREPARE_ATTEMPTS - 1:
                    try:
                        act_retry = bot._get_current_activity(dev_id) or ""
                        vpn_retry = bool(bot.vpn_activity(dev_id))
                    except Exception:
                        act_retry = "unknown"
                        vpn_retry = False
                    _multi_log.warning(
                        f"[DIAG] _prepare ── {dev_id} prepare_target_app FAILED attempt {attempt+1} — "
                        f"state: vpn={vpn_retry}  activity={act_retry.strip()!r} — retrying in 8s"
                    )
                    log_fn(f"  prepare_target_app failed — retrying in 8 s …", "warn")
                    time.sleep(8)
            _multi_log.error(
                f"[DIAG] _prepare ── {dev_id} FAILED all {MAX_PREPARE_ATTEMPTS} attempts "
                f"total={time.time()-_t_prep_start:.3f}s"
            )
            return False, f"prepare_target_app failed after {MAX_PREPARE_ATTEMPTS} attempts"

    def _reset_state(self, dev_id):
        """Full per-device counter reset. Uses bot.reset_device_finished_state() when available."""
        bot = self.load_bot()
        if hasattr(bot, "reset_device_finished_state"):
            try:
                bot.reset_device_finished_state(dev_id)
                _multi_log.info(f"[RESET] _reset_state: reset_device_finished_state({dev_id}) ✓")
                return
            except Exception as _rse:
                _multi_log.warning(f"[RESET] _reset_state: reset_device_finished_state failed: {_rse}")
        # Fallback: clear the five old dicts that existed before the guard refactor
        for attr in ("vpn_stage", "stage_tries", "install_attempts",
                     "target_app_stage", "target_app_install_attempts"):
            m = getattr(bot, attr, None)
            if isinstance(m, dict):
                m.pop(dev_id, None)

    def _run_one(self, dev_id, task_key, dlog, guard, stop, log_fn) -> str:
        bot = self.load_bot()
        td  = TASK_DEFS.get(task_key)
        if td is None:
            log_fn(f"✗  unknown task: {task_key}", "err")
            _multi_log.error(f"[DIAG] _run_one ── {dev_id} unknown task {task_key!r}")
            return f"unknown task: {task_key}"

        status_dict = getattr(bot, td["status_attr"], {})
        sub_attr    = td.get("sub_attr")
        sub_dict    = getattr(bot, sub_attr, None) if sub_attr else None
        if (status_dict.get(dev_id, "") or "").strip().lower() == "done":
            _multi_log.info(
                f"[DIAG] _run_one ── {dev_id} {task_key!r} SKIPPED (already done in sheet)"
            )
            log_fn(f"✓  {task_key} skipped (already done)", "ok")
            print(f"[{dev_id.split(':')[-1]}] {task_key}: skipped (already done)")
            return "skipped"
        substatus = sub_dict.setdefault(dev_id, {}) if sub_dict is not None else None

        # Same registry the Run-mode worker uses, so Test mode can never execute
        # a different function — or a task the worker does not have.
        func = bot.get_task_callable(task_key)
        if func is None:
            log_fn(f"✗  no function for task: {task_key}", "err")
            _multi_log.error(
                f"[DIAG] _run_one ── {dev_id} {task_key!r} has no callable in "
                f"bot.TASK_FUNCTIONS"
            )
            return f"no function for task: {task_key}"
        # Max 5 total attempts before giving up on this task
        MAX_ATTEMPTS  = 5
        attempt       = 0
        restart_count = 0
        while not stop.is_set():
            # Check cap BEFORE running — ensures exactly MAX_ATTEMPTS total runs
            if attempt >= MAX_ATTEMPTS:
                log_fn(f"  {task_key} reached max attempts ({MAX_ATTEMPTS}) — aborting task", "err")
                _multi_log.error(
                    f"[DIAG] _run_one ── {dev_id} {task_key!r} CAP REACHED: "
                    f"attempt={attempt} >= MAX_ATTEMPTS={MAX_ATTEMPTS} "
                    f"restarts={restart_count} — ABORTING"
                )
                print(
                    f"[{dev_id.split(':')[-1]}] {task_key}: ABORTED after "
                    f"{attempt} attempts (max={MAX_ATTEMPTS})"
                )
                return f"max_attempts: {task_key}"
            attempt += 1
            _t_attempt = time.time()
            log_fn(f"  {task_key} attempt #{attempt}/{MAX_ATTEMPTS}", "dim")
            _multi_log.info(
                f"[DIAG] _run_one ── {dev_id} {task_key!r} attempt #{attempt}/{MAX_ATTEMPTS} "
                f"restarts={restart_count}  t={_t_attempt:.3f}"
            )
            try:
                result = func(dev_id, dlog, guard, substatus if substatus is not None else {})
            except StopTaskNow:
                # Always propagate the stop signal — do NOT let it fall into the ADB recovery path
                raise
            except bot.GuardRecoveryFailed as _grf:
                dlog.error(f"── controller ── GuardRecoveryFailed in {task_key}: {_grf}")
                log_fn(f"  GuardRecoveryFailed — device unrecoverable (will wait + prepare_target_app)…", "warn")
                _multi_log.error(
                    f"[DIAG] _run_one ── {dev_id} {task_key!r} "
                    f"GuardRecoveryFailed attempt #{attempt}: {_grf}"
                )
                # One shared ladder. The old 90s ADB pre-wait could never be
                # satisfied by a closed emulator, and prepare_target_app -> setup_device
                # is what relaunches one.
                _rec = self._recover_prepare_target_app(
                    dev_id, log_fn, stop,
                    reason=f"GuardRecoveryFailed: {_grf}")
                if _rec == "stopped":
                    return "stopped"
                if _rec != "recovered":
                    return "prepare_target_app_failed"
                guard = bot._target_app_guards.get(dev_id)
                self._seed_globals()
                log_fn(f"  Recovery complete — retrying {task_key}", "info")
                restart_count += 1
                continue
            except Exception as exc:
                _is_logic_err = isinstance(exc, (RuntimeError, KeyError,
                                                  ValueError, AttributeError,
                                                  TypeError, IndexError))
                if _is_logic_err:
                    dlog.error(f"── controller ── Logic error in {task_key}: {exc}")
                    log_fn(f"  Logic error in task — restarting without device recovery", "warn")
                    _multi_log.error(
                        f"[DIAG] _run_one ── {dev_id} {task_key!r} LOGIC ERROR "
                        f"attempt #{attempt} after {time.time()-_t_attempt:.3f}s: {exc}"
                    )
                    restart_count += 1
                    continue  # cap enforced at top of loop
                # ── ADB / device-offline recovery ─────────────────────────────
                dlog.error(f"── controller ── ADB exception in {task_key}: {exc}")
                log_fn(f"  ADB exception — waiting for device to come back…", "warn")
                _multi_log.error(
                    f"[DIAG] _run_one ── {dev_id} {task_key!r} ADB EXCEPTION "
                    f"attempt #{attempt} after {time.time()-_t_attempt:.3f}s: {exc}"
                )
                # Same shared ladder — a closed emulator must reach prepare_target_app.
                _rec = self._recover_prepare_target_app(
                    dev_id, log_fn, stop, reason=f"ADB exception: {exc}")
                if _rec == "stopped":
                    return "stopped"
                if _rec != "recovered":
                    return "prepare_target_app_failed"
                guard = bot._target_app_guards.get(dev_id)
                self._seed_globals()
                log_fn(f"  Recovery complete — retrying {task_key}", "info")
                restart_count += 1
                continue  # cap enforced at top of loop

            _multi_log.info(
                f"[DIAG] _run_one ── {dev_id} {task_key!r} attempt #{attempt} → "
                f"{result!r} in {time.time()-_t_attempt:.3f}s"
            )
            # ── Task result contract ─────────────────────────────────────
            # done | restart | full_restart | vpn_down | stopped | SIG_MANUAL_STOP
            # Anything else is a genuine bug and is reported as one, never
            # reinterpreted as a recovery signal.

            # 4A. Stop wins over everything, and is checked BEFORE any status
            #     write. Without this a Stop landing between the task returning
            #     and the commit below still wrote VipCollect=done.
            _manual = getattr(bot, "SIG_MANUAL_STOP", "manual_stop")
            if stop.is_set():
                _multi_log.info(
                    f"[DIAG] _run_one ── {dev_id} {task_key!r} stop set after "
                    f"the task returned {result!r} — no status commit")
                return "stopped"
            if result in ("stopped", _manual):
                _multi_log.info(
                    f"[DIAG] _run_one ── {dev_id} {task_key!r} returned "
                    f"{result!r} — no recovery, no status commit")
                return "stopped"

            if result == "done":
                status_dict[dev_id] = "done"
                if td.get("header"):
                    bot.update_status(dev_id, td["header"], "done")
                    _multi_log.info(
                        f"[DIAG] _run_one ── {dev_id} {task_key!r} DONE ✓ "
                        f"| update_status queued for header={td['header']!r}"
                    )
                else:
                    _multi_log.info(f"[DIAG] _run_one ── {dev_id} {task_key!r} DONE ✓ (no header)")
                return "done"

            # 4B. restart — bounded local retry, unchanged.
            if result == "restart":
                restart_count += 1
                _multi_log.info(
                    f"[DIAG] _run_one ── {dev_id} {task_key!r} restart #{restart_count} "
                    f"(attempt={attempt}, cap={MAX_ATTEMPTS})"
                )
                continue  # cap enforced at top of loop

            # 4C. full_restart — the game state could not be recovered locally.
            if result == "full_restart":
                log_fn(f"  {task_key}: full_restart — running prepare_target_app", "warn")
                _multi_log.info(
                    f"[DIAG] _run_one ── {dev_id} {task_key!r} FULL_RESTART "
                    f"(attempt={attempt}/{MAX_ATTEMPTS})")
                # No blocking ADB pre-wait: a closed emulator cannot answer it,
                # and prepare_target_app -> setup_device is what re-launches the
                # instance. _recover_prepare_target_app does a short reconnect only when
                # netstat still shows it open.
                _rec = self._recover_prepare_target_app(dev_id, log_fn, stop,
                                                reason="full_restart")
                if _rec == "stopped":
                    return "stopped"
                if _rec != "recovered":
                    return "prepare_target_app_failed"
                guard = bot._target_app_guards.get(dev_id)
                self._seed_globals()
                restart_count += 1
                continue  # counts against MAX_ATTEMPTS at the top

            # 4D. vpn_down — mirror the Run-mode safety contract. prepare_target_app is
            #     NOT the first response: a live device with a dead tunnel needs
            #     a server change, not a full teardown.
            if result == "vpn_down":
                log_fn(f"  {task_key}: VPN down — changing server", "warn")
                _multi_log.warning(
                    f"[DIAG] _run_one ── {dev_id} {task_key!r} VPN_DOWN "
                    f"(attempt={attempt}/{MAX_ATTEMPTS})")
                def _emulator_alive() -> bool:
                    """
                    Is the BlueStacks WINDOW still open?

                    netstat-based, so it survives the ADB drop that a VPN
                    routing change causes. _device_exists_in_adb answers a
                    different question — "is ADB talking to it" — and returns
                    False during exactly the transient loss this branch exists
                    to handle, which is why it must not decide "closed".

                    Fails OPEN: a process-check error must never invent a crash.
                    """
                    try:
                        return bool(bot.is_emulator_process_alive(dev_id))
                    except Exception:
                        return True

                def _adb_alive() -> bool:
                    try:
                        return bool(bot._device_exists_in_adb(dev_id))
                    except Exception:
                        return True

                def _full_restart_here(why: str) -> "str | None":
                    """
                    Recover a closed/unconfirmed device.
                    None = recovered, carry on. Otherwise a result to return.
                    """
                    log_fn(f"  {why} — full restart", "warn")
                    _r = self._recover_prepare_target_app(dev_id, log_fn, stop,
                                                  reason="vpn_down")
                    if _r == "stopped":
                        return "stopped"
                    if _r != "recovered":
                        return "prepare_target_app_failed"
                    return None

                if not _emulator_alive():
                    err = _full_restart_here("Emulator closed before VPN recovery")
                    if err:
                        return err
                    guard = bot._target_app_guards.get(dev_id)
                    self._seed_globals()
                    restart_count += 1
                    continue

                changed = False
                try:
                    changed = bool(bot._vpn_change_server(dev_id, dlog, guard,
                                                          force_change=True))
                except Exception as _ve:
                    _multi_log.error(
                        f"[DIAG] _run_one ── {dev_id} _vpn_change_server raised: {_ve}")
                    changed = False

                # The emulator can close DURING the change, which is not a VPN
                # fault and must not fail the run. The bot records exactly that.
                if not changed:
                    reason = ""
                    try:
                        reason = bot._last_vpn_change_failure_reason.get(dev_id, "")
                    except Exception:
                        reason = ""

                    # A. genuinely closed — explicit reason, or the window is
                    #    gone according to netstat.
                    if reason == "device_closed" or not _emulator_alive():
                        _multi_log.warning(
                            f"[DIAG] _run_one ── {dev_id} VPN change failed with "
                            f"reason={reason!r} and the emulator is closed — "
                            f"recovering rather than failing")
                        err = _full_restart_here("Emulator closed during VPN recovery")
                        if err:
                            return err
                        guard = bot._target_app_guards.get(dev_id)
                        self._seed_globals()
                        restart_count += 1
                        continue

                    # B. window still open but ADB is missing. This is the VPN
                    #    routing transition, NOT a closed emulator — calling it
                    #    one would tear down a perfectly healthy instance.
                    if not _adb_alive():
                        log_fn("  ADB lost during VPN recovery (emulator still "
                               "open) — waiting for it to return", "warn")
                        _multi_log.warning(
                            f"[DIAG] _run_one ── {dev_id} ADB absent but emulator "
                            f"process alive — bounded reconnect, reason={reason!r}")
                        back = False
                        try:
                            back = bool(bot._adb_wait_for_device(dev_id, timeout=30,
                                                                 interval=3))
                        except Exception:
                            back = False
                        if back:
                            # ADB is back — the tunnel may have come up on its own
                            # during the transition.
                            try:
                                if bool(bot.vpn_activity(dev_id)):
                                    log_fn("  ADB back and tun0 is up — continuing",
                                           "ok")
                                    guard = bot._target_app_guards.get(dev_id)
                                    self._seed_globals()
                                    restart_count += 1
                                    continue
                            except Exception:
                                pass
                            log_fn("  ADB back but tun0 still down", "err")
                            return "vpn_recovery_failed"
                        _multi_log.error(
                            f"[DIAG] _run_one ── {dev_id} ADB never returned "
                            f"during VPN recovery")
                        return "adb_lost_during_vpn_recovery"

                # Never take the helper's word for it — confirm the tunnel.
                tun0 = False
                if changed:
                    try:
                        tun0 = bool(bot.vpn_activity(dev_id))
                    except Exception:
                        tun0 = False
                if not (changed and tun0):
                    log_fn("  VPN recovery failed — refusing to continue without "
                           "tun0", "err")
                    _multi_log.error(
                        f"[DIAG] _run_one ── {dev_id} {task_key!r} VPN recovery "
                        f"failed (changed={changed} tun0={tun0}) — failing the run")
                    return "vpn_recovery_failed"

                log_fn("  VPN restored (tun0 up) — returning to main screen", "ok")
                guard = bot._target_app_guards.get(dev_id)
                self._seed_globals()
                # Put the game back somewhere a task can start from, using the
                # shared helper rather than a bespoke Loading loop. Its result
                # matters: retrying from an unconfirmed screen is how a task
                # ends up clicking into whatever happens to be showing.
                back_ok = False
                try:
                    back_ok = bool(bot._back_to_main(dev_id, dlog, guard))
                except Exception as _be:
                    _multi_log.warning(
                        f"[DIAG] _run_one ── {dev_id} _back_to_main after VPN "
                        f"recovery raised: {_be}")
                    back_ok = False
                if not back_ok:
                    err = _full_restart_here("Could not confirm the main screen "
                                             "after VPN recovery")
                    if err:
                        return err
                    guard = bot._target_app_guards.get(dev_id)
                    self._seed_globals()
                restart_count += 1
                continue

            # 4E. Anything else is unknown. Fail loudly instead of guessing.
            _multi_log.error(
                f"[DIAG] _run_one ── {dev_id} {task_key!r} UNEXPECTED RESULT "
                f"{result!r}")
            dlog.error(f"── controller ── unexpected task result in {task_key}: "
                       f"{result!r}")
            log_fn(f"  Unexpected task result: {result}", "err")
            return f"unexpected task result: {result}"
        return "stopped"

    def _recover_prepare_target_app(self, dev_id: str, log_fn, stop,
                            reason: str = "", attempts: int = 3) -> str:
        """
        Bounded prepare_target_app(force_stop_first=True) recovery.

        Returns "recovered" | "stopped" | "failed".

        A bool could not express this: False meant both "recovery failed" and
        "the operator pressed Stop", so pressing Stop during a recovery was
        reported to the user as `prepare_target_app_failed` — a task failure that never
        happened.

        prepare_target_app -> setup_device -> _sd_wait_device_ready is what LAUNCHES a
        missing BlueStacks instance, so this must not be gated on ADB first: a
        closed emulator will never answer `_adb_wait_for_device`, and the old
        90s pre-wait simply burned the time and then gave up on exactly the case
        recovery exists for. A short reconnect is worth trying only while
        netstat still shows the instance open.

        `stop` is the Test stop event: every attempt and every inter-attempt
        wait honours it, so Stop is not stuck behind a recovery ladder.
        """
        bot = self.load_bot()
        _multi_log.info(f"[FORCE-STOP] controller startover path: "
                        f"prepare_target_app(force_stop_first=True) — {reason}")
        for r_attempt in range(1, attempts + 1):
            if stop is not None and stop.is_set():
                _multi_log.info(f"[DIAG] _recover_prepare_target_app ── {dev_id} "
                                f"stop requested — abandoning recovery")
                return "stopped"
            _t = time.time()

            # Only bother reconnecting when the instance is actually still up.
            # If it is closed, go straight to prepare_target_app, which owns launching.
            try:
                if bot._device_exists_in_adb(dev_id) and not bot._adb_ping(dev_id):
                    bot._adb_wait_for_device(dev_id, timeout=15, interval=3)
            except Exception:
                pass

            try:
                if bot.prepare_target_app(dev_id, force_stop_first=True):
                    _multi_log.info(
                        f"[DIAG] _recover_prepare_target_app ── {dev_id} attempt "
                        f"{r_attempt}/{attempts} SUCCESS in {time.time()-_t:.1f}s "
                        f"({reason})")
                    return "recovered"
            except Exception as exc:
                _multi_log.warning(
                    f"[DIAG] _recover_prepare_target_app ── {dev_id} attempt "
                    f"{r_attempt}/{attempts} EXCEPTION: {exc}")
            log_fn(f"  prepare_target_app recovery attempt {r_attempt}/{attempts} failed…",
                   "warn")
            # No sleep after the final attempt — it delays the failure report
            # by 5s and buys nothing.
            if r_attempt < attempts:
                if stop is not None:
                    if stop.wait(timeout=5):
                        _multi_log.info(
                            f"[DIAG] _recover_prepare_target_app ── {dev_id} stop during "
                            f"the inter-attempt wait — abandoning recovery")
                        return "stopped"
                else:
                    time.sleep(5)
        log_fn("  prepare_target_app recovery failed — aborting", "err")
        _multi_log.error(f"[DIAG] _recover_prepare_target_app ── {dev_id} FAILED all "
                         f"{attempts} attempts ({reason})")
        return "failed"

# ==============================================================================
# FIX 5: DELAYED-OPEN FILE HANDLER — releases lock when not writing
# ==============================================================================
class _DelayedFileHandler(logging.Handler):
    """
    Opens the log file only when actually emitting a record, then closes it
    immediately.  This ensures Windows never holds the file open between
    writes, so users can freely edit, compress, or delete log files while
    the bot is idle.  Missing files are recreated silently on the next write.
    """
    def __init__(self, filename: str, mode: str = "a", encoding: str = "utf-8"):
        super().__init__()
        self.filename = filename
        self.mode     = mode
        self.encoding = encoding
        self.setFormatter(logging.Formatter(
            "%(asctime)s  %(levelname)-8s  %(message)s", "%Y-%m-%d %H:%M:%S"))

    def emit(self, record):
        try:
            msg = self.format(record) + "\n"
            with open(self.filename, self.mode, encoding=self.encoding) as fh:
                fh.write(msg)
        except Exception:
            self.handleError(record)


def _make_logger_v8(name: str, fname: str) -> logging.Logger:
    lg = logging.getLogger(name + "_v8")
    lg.setLevel(logging.DEBUG)
    lg.propagate = False
    if not lg.handlers:
        lg.addHandler(_DelayedFileHandler(fname))
    return lg



# ==============================================================================
# FIX 6: ORPHAN BLUESTACKS CLEANUP
# ==============================================================================
def _get_bluestacks_pids() -> dict[int, str]:
    """
    Returns {pid: cmdline} for every running HD-Player.exe process.
    Works on Windows only; returns {} on other platforms.
    """
    result = {}
    try:
        out = subprocess.run(
            ["wmic", "process", "where",
             "name='HD-Player.exe'",
             "get", "ProcessId,CommandLine", "/format:csv"],
            capture_output=True, text=True, timeout=10,
        ).stdout
        for line in out.splitlines():
            line = line.strip()
            if not line or line.startswith("Node"):
                continue
            parts = line.split(",", 2)
            if len(parts) < 3:
                continue
            try:
                pid = int(parts[1].strip())
                cmd = parts[2].strip()
                result[pid] = cmd
            except ValueError:
                continue
    except Exception:
        pass
    return result


def _port_from_cmdline(cmdline: str) -> str | None:
    """Extract the --adb-port or similar port from an HD-Player command line."""
    import re as _re
    m = _re.search(r"--?(?:adb.?port|port)[=\s]+(\d+)", cmdline, _re.IGNORECASE)
    if m:
        return m.group(1)
    m = _re.search(r"-s\s+localhost:(\d+)", cmdline)
    if m:
        return m.group(1)
    return None


def cleanup_orphan_bluestacks(active_adb_ids: list[str], max_allowed: int) -> list[int]:
    """
    Kill HD-Player.exe processes beyond max_allowed that are NOT serving any
    of the currently active adb_ids.

    Returns list of PIDs that were terminated.
    """
    protected_ports = {aid.split(":")[-1] for aid in active_adb_ids if ":" in aid}
    pids = _get_bluestacks_pids()
    if len(pids) <= max_allowed:
        return []

    killed = []
    # Sort oldest-first (lowest pid = oldest) to keep newest instances
    for pid, cmd in sorted(pids.items()):
        if len(pids) - len(killed) <= max_allowed:
            break
        port = _port_from_cmdline(cmd)
        if port and port in protected_ports:
            continue  # never kill an active device
        try:
            subprocess.run(["taskkill", "/F", "/PID", str(pid)],
                           capture_output=True, timeout=5)
            killed.append(pid)
            _multi_log.info(f"[orphan] killed HD-Player PID {pid} (port={port})")
        except Exception as e:
            _multi_log.warning(f"[orphan] failed to kill PID {pid}: {e}")
    return killed


# ==============================================================================
# DEMO DATA
# ==============================================================================
DEMO_CONF = [
    {"adb_id": "localhost:5557", "name": "TARGET_APP-1", "instance": "Nougat64_1", "device_type": "new1720", "statuses": {}},
    {"adb_id": "localhost:5559", "name": "TARGET_APP-2", "instance": "Nougat64_2", "device_type": "new1720", "statuses": {}},
    {"adb_id": "localhost:5561", "name": "TARGET_APP-3", "instance": "Nougat64_3", "device_type": "veteran", "statuses": {}},
    {"adb_id": "localhost:5563", "name": "TARGET_APP-4", "instance": "Nougat64_4", "device_type": "", "statuses": {}},
]
DEMO_ACTIVE = [
    {"adb_id": "localhost:5557", "name": "TARGET_APP-1", "device_type": "new1720",
     "statuses": {"vip_collect": "done"}},
    {"adb_id": "localhost:5559", "name": "TARGET_APP-2", "device_type": "new1720",
     "statuses": {"vip_collect": ""}},
    {"adb_id": "localhost:5561", "name": "TARGET_APP-3", "device_type": "veteran",
     "statuses": {"vip_collect": "done"}},
    {"adb_id": "localhost:5563", "name": "TARGET_APP-4", "device_type": "",
     "statuses": {"vip_collect": ""}},
]


# ==============================================================================
# HELPERS
# ==============================================================================
def _btn(parent, text, cmd, bg=BG_CELL, fg=FG_MAIN, font=FN,
         state=tk.NORMAL, padx=8, pady=5, **kw) -> tk.Button:
    return tk.Button(parent, text=text, command=cmd, bg=bg, fg=fg,
                     font=font, relief=tk.FLAT, padx=padx, pady=pady,
                     cursor="hand2", state=state,
                     activebackground=PRI, activeforeground="white", **kw)


def _sec_label(parent, text: str, side=None):
    lbl = tk.Label(parent, text=text, font=(F, 9, "bold"), bg=BG_PANEL,
                   fg=PRI, padx=8, pady=8)
    if side:
        lbl.pack(side=side)
    else:
        lbl.pack(anchor=tk.W)
    return lbl


def _ts() -> str:
    return datetime.now().strftime("%H:%M:%S")


def _group_devices_by_type(devices: list[dict]) -> list[tuple[str, list[dict]]]:
    """Group devices by device_type, named groups first sorted, (no tag) last."""
    groups: dict[str, list[dict]] = {}
    for d in devices:
        dt = d.get("device_type", "") or ""
        groups.setdefault(dt, []).append(d)
    result = []
    for k in sorted(g for g in groups if g):
        result.append((k, groups[k]))
    if "" in groups:
        result.append(("(no tag)", groups[""]))
    return result


# ==============================================================================
# TASK SELECTOR WIDGET
# ==============================================================================
class TaskSelector(tk.Frame):
    """Scrollable task checklist used in the Test tab.
    Shows task sets (if any) at the top in gold, then individual tasks."""

    def __init__(self, parent, task_sets_mgr=None, **kw):
        super().__init__(parent, bg=BG_PANEL, **kw)
        self._ts_mgr = task_sets_mgr          # TaskSetsManager or None
        self._full_var = tk.BooleanVar(value=False)
        self._vars: dict[str, tk.BooleanVar] = {k: tk.BooleanVar(value=False) for k in SUBTASK_ORDER}
        self._set_vars: dict[str, tk.BooleanVar] = {}  # set: keys
        self._build()

    def _build(self):
        # ── fixed header ──────────────────────────────────────────────────
        hdr = tk.Frame(self, bg=BG_PANEL)
        hdr.pack(fill=tk.X)
        tk.Label(hdr, text="TASKS TO RUN", font=FNB, bg=BG_PANEL,
                 fg=PRI).pack(anchor=tk.W, pady=(4, 2))
        full_cb = tk.Checkbutton(hdr, text="Select All Tasks",
                                 variable=self._full_var,
                                 font=FNB, bg=BG_PANEL, fg=FG_MAIN,
                                 selectcolor=BG_CELL, activebackground=BG_PANEL,
                                 command=self._on_full_toggled, anchor=tk.W)
        full_cb.pack(fill=tk.X, padx=4)
        tk.Frame(hdr, bg=BG_CELL, height=1).pack(fill=tk.X, pady=4)

        # ── scrollable checklist ──────────────────────────────────────────
        wrap = tk.Frame(self, bg=BG_PANEL)
        wrap.pack(fill=tk.BOTH, expand=True)
        wrap.rowconfigure(0, weight=1)
        wrap.columnconfigure(0, weight=1)

        canvas = tk.Canvas(wrap, bg=BG_PANEL, bd=0, highlightthickness=0)
        sb = tk.Scrollbar(wrap, orient=tk.VERTICAL, command=canvas.yview,
                          bg=BG_MID, troughcolor=BG_MID)
        canvas.configure(yscrollcommand=sb.set)
        sb.grid(row=0, column=1, sticky="ns")
        canvas.grid(row=0, column=0, sticky="nsew")

        self._inner = tk.Frame(canvas, bg=BG_PANEL)
        win_id = canvas.create_window((0, 0), window=self._inner, anchor=tk.NW)
        self._inner.bind("<Configure>",
                   lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.bind("<Configure>",
                    lambda e: canvas.itemconfig(win_id, width=e.width))

        def _on_wheel(event):
            canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        canvas.bind_all("<MouseWheel>", _on_wheel)

        self._populate_inner()

    def _populate_inner(self):
        for w in self._inner.winfo_children():
            w.destroy()
        self._set_vars.clear()

        # ── Task Sets section ─────────────────────────────────────────────
        if self._ts_mgr:
            sets = self._ts_mgr.all_sets()
            if sets:
                tk.Label(self._inner, text="── Task Sets ──",
                         font=(FN[0], FN[1], "bold"),
                         bg=BG_PANEL, fg=ACC_BLUE).pack(fill=tk.X, padx=4, pady=(4,1))
                for s in sets:
                    sk = self._ts_mgr.set_key(s["name"])
                    v = tk.BooleanVar(value=False)
                    self._set_vars[sk] = v
                    self._vars[sk] = v   # unified dict for selected_tasks()
                    tk.Checkbutton(self._inner, text=f"  📦 {s['name']}",
                                   variable=v, font=FN, bg=BG_PANEL, fg="#FFD700",
                                   selectcolor=BG_CELL, activebackground=BG_PANEL,
                                   command=self._on_sub_toggled, anchor=tk.W
                                   ).pack(fill=tk.X, padx=4)
                tk.Label(self._inner, text="── Individual Tasks ──",
                         font=(FN[0], FN[1], "bold"),
                         bg=BG_PANEL, fg=FG_DIM).pack(fill=tk.X, padx=4, pady=(6,1))

        for k in SUBTASK_ORDER:
            tk.Checkbutton(self._inner, text=f"  {TASK_DEFS[k]['label']}",
                           variable=self._vars[k],
                           font=FN, bg=BG_PANEL, fg=FG_MAIN,
                           selectcolor=BG_CELL, activebackground=BG_PANEL,
                           command=self._on_sub_toggled, anchor=tk.W
                           ).pack(fill=tk.X, padx=4)

    def refresh_sets(self):
        """Call after adding/deleting a task set to update the list."""
        self._populate_inner()

    def _on_full_toggled(self):
        v = self._full_var.get()
        for var in self._vars.values():
            var.set(v)

    def _on_sub_toggled(self):
        self._full_var.set(all(v.get() for v in self._vars.values()))

    def selected_tasks(self) -> list[str]:
        # Return all checked keys (set: and individual), preserving set: order first
        result = []
        for k in self._set_vars:
            if self._vars.get(k, tk.BooleanVar()).get():
                result.append(k)
        for k in SUBTASK_ORDER:
            if self._vars[k].get():
                result.append(k)
        return result

    def select_all(self):
        self._full_var.set(True)
        self._on_full_toggled()

    def select_none(self):
        self._full_var.set(False)
        self._on_full_toggled()


# ==============================================================================
# TASK POPOVER
# ==============================================================================
class TaskPopover(tk.Toplevel):
    def __init__(self, parent, anchor_widget, initial, on_confirm):
        super().__init__(parent)
        self.overrideredirect(True)
        self.configure(bg=BG_PANEL)
        self.on_confirm = on_confirm
        # FIX 4: _vars for individual tasks; set: keys added below if sets exist
        self._vars = {k: tk.BooleanVar(value=(k in initial)) for k in SUBTASK_ORDER}
        self.update_idletasks()
        x = anchor_widget.winfo_rootx()
        y = anchor_widget.winfo_rooty() + anchor_widget.winfo_height() + 2
        self.geometry(f"+{x}+{y}")
        hf = tk.Frame(self, bg=BG_PANEL)
        hf.pack(fill=tk.X, padx=8, pady=(6, 2))
        tk.Label(hf, text="Select tasks:", font=FSB, bg=BG_PANEL, fg=FG_DIM).pack(side=tk.LEFT)
        _btn(hf, "None", self._sel_none, bg=BG_CELL, fg=FG_DIM, font=FS, padx=5, pady=2).pack(side=tk.RIGHT, padx=(2, 0))
        _btn(hf, "All", self._sel_all, bg=BG_CELL, fg=ACC_BLUE, font=FS, padx=5, pady=2).pack(side=tk.RIGHT, padx=2)
        # Scrollable task list — capped at 420px so it always fits the window
        list_frame = tk.Frame(self, bg=BG_PANEL)
        list_frame.pack(fill=tk.BOTH, expand=True, padx=0, pady=0)
        list_canvas = tk.Canvas(list_frame, bg=BG_PANEL, bd=0, highlightthickness=0,
                                height=420)
        list_sb = tk.Scrollbar(list_frame, orient=tk.VERTICAL,
                               command=list_canvas.yview, bg=BG_MID, troughcolor=BG_MID)
        list_canvas.configure(yscrollcommand=list_sb.set)
        list_sb.pack(side=tk.RIGHT, fill=tk.Y)
        list_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        inner = tk.Frame(list_canvas, bg=BG_PANEL)
        win_id = list_canvas.create_window((0, 0), window=inner, anchor=tk.NW)
        inner.bind("<Configure>", lambda e: list_canvas.configure(
            scrollregion=list_canvas.bbox("all")))
        list_canvas.bind("<Configure>", lambda e: list_canvas.itemconfig(
            win_id, width=e.width))
        def _mw(e):
            delta = int(-1*(e.delta/120)) if e.delta else (-1 if e.num==4 else 1)
            list_canvas.yview_scroll(delta, "units")
        list_canvas.bind("<MouseWheel>", _mw)
        inner.bind("<MouseWheel>", _mw)
        # ── Task Sets section (if any sets exist) ─────────────────────────
        _ts_mgr = getattr(parent, "_task_sets", None)
        if _ts_mgr and _ts_mgr.all_sets():
            tk.Label(inner, text="── Task Sets ──", font=(FS[0], FS[1], "bold"),
                     bg=BG_PANEL, fg=ACC_BLUE).pack(fill=tk.X, padx=8, pady=(6,2))
            for s in _ts_mgr.all_sets():
                sk = _ts_mgr.set_key(s["name"])
                cb = tk.Checkbutton(inner, text=f"📦 {s['name']}",
                               variable=self._vars.setdefault(sk, tk.BooleanVar(value=(sk in initial))),
                               font=FS, bg=BG_PANEL, fg="#FFD700",
                               selectcolor=BG_CELL, activebackground=BG_PANEL,
                               anchor=tk.W)
                cb.pack(fill=tk.X, padx=8)
                cb.bind("<MouseWheel>", _mw)
            tk.Label(inner, text="── Individual Tasks ──", font=(FS[0], FS[1], "bold"),
                     bg=BG_PANEL, fg=FG_DIM).pack(fill=tk.X, padx=8, pady=(6,2))
        for k in SUBTASK_ORDER:
            cb = tk.Checkbutton(inner, text=TASK_DEFS[k]["label"],
                           variable=self._vars[k],
                           font=FS, bg=BG_PANEL, fg=FG_MAIN,
                           selectcolor=BG_CELL, activebackground=BG_PANEL,
                           anchor=tk.W)
            cb.pack(fill=tk.X, padx=8)
            cb.bind("<MouseWheel>", _mw)
        bf = tk.Frame(self, bg=BG_PANEL)
        bf.pack(fill=tk.X, padx=8, pady=6)
        _btn(bf, "OK", self._confirm, bg=PRI, fg="white", font=FSB).pack(side=tk.LEFT, padx=2)
        _btn(bf, "Cancel", self.destroy, bg=BG_CELL, fg=FG_DIM, font=FS).pack(side=tk.LEFT)
        self.bind("<FocusOut>", lambda e: self.destroy())
        self.focus_set()

    def _sel_all(self):
        for v in self._vars.values(): v.set(True)

    def _sel_none(self):
        for v in self._vars.values(): v.set(False)

    def _confirm(self):
        # Return set: keys + individual task keys that are checked
        selected = [k for k in list(self._vars.keys()) if self._vars[k].get()]
        self.on_confirm(selected)
        self.destroy()


# ==============================================================================
# MAIN UI
# ==============================================================================
# ==============================================================================
# LOG ANALYZER  — local log parsing + summary generation (no Google Sheets)
# ------------------------------------------------------------------------------
# Pure standard-library parser, fully decoupled from the UI.  Scans controller
# and per-device log files, groups entries into timeframes/sessions, and builds
# overall / per-task / per-DeviceType / per-device summaries plus an event
# timeline and a "potential issues" list.
#
# This class performs NO Google Sheets reads and does not touch bot task logic,
# VPN logic, OCR, coordinates, multiprocessing, or sheet writing.  DeviceType
# enrichment is optional and supplied by the caller (controller rows_by_device).
# ==============================================================================
# ==============================================================================
# HUMAN-READABLE PER-DEVICE RUN LOG
# ==============================================================================
# An ADDITIONAL product, generated after a device reaches its terminal state in a
# Run session. The raw per-device log under logs/<device>.log remains the
# forensic source of truth and is never modified, reduced or redirected — this
# reads it and narrates it.
#
# Standard library only. No AI, no network, no Sheets, no ADB, no screenshots,
# no OCR, no bot calls. Deterministic: the same slice always renders the same
# report.
# ==============================================================================

# ==============================================================================
# HUMAN-READABLE PER-DEVICE RUN LOG
# ==============================================================================
# An ADDITIONAL product, generated after a device reaches its terminal state in a
# Run session. The raw per-device log under logs/<device>.log remains the
# forensic source of truth and is never modified, reduced or redirected — this
# reads it and narrates it.
#
# Standard library only. No AI, no network, no Sheets, no ADB, no screenshots,
# no OCR, no bot calls. Deterministic: the same slice always renders the same
# report.
# ==============================================================================

HUMAN_LOG_DIRNAME = "human"
# Abandonment-route notes. Both phases of a route quote the same sentence, so
# a device finalized before the kill and one finalized after cannot disagree
# about why the Run ended.
NOTE_SAFE_RESET = "Stopped by the safe daily reset while the Run was active."
NOTE_CONTROLLER_CLOSE = ("The controller window was closed while this device "
                         "was running.")
NOTE_FATAL_RUN = "The Run was aborted by a fatal error on another device."
# How long the fatal TRIGGER worker may keep running its own _finalize()
# before the controller kills it. Long enough for recording finalisation plus
# the counter snapshot and [WORKER-END]; short enough that a wedged worker
# cannot hold the fatal popup back.
FATAL_TRIGGER_GRACE_SECONDS = 20.0


class HumanDeviceLogContext:
    """
    Everything the generator needs about one (run_session_id, adb_id) pair.

    Created when the device first participates in an accepted Run session and
    kept across ADB retries and hard-emergency relaunches inside that session —
    a retry is not a finished lifecycle, so the report tells the whole story.
    """

    __slots__ = ("session_id", "adb_id", "friendly_name", "device_type",
                 "requested_tasks", "resolved_tasks", "task_action",
                 "started_at", "raw_log_path", "raw_start_offset",
                 "raw_end_offset", "attempts", "final_result", "final_ok",
                 "close_ok", "retry_count", "final_badge", "finalized",
                 "finished_at", "notes", "retry_skip_reason", "retry_skip_detail",
                 "close_disposition", "prior_close_result")

    def __init__(self, session_id, adb_id, friendly_name="", device_type="",
                 requested_tasks=None, resolved_tasks=None, task_action="run",
                 raw_log_path="", raw_start_offset=0):
        self.session_id = session_id
        self.adb_id = adb_id
        self.friendly_name = friendly_name or adb_id
        self.device_type = device_type or ""
        self.requested_tasks = list(requested_tasks or [])
        self.resolved_tasks = list(resolved_tasks or [])
        self.task_action = task_action           # run | setup_only | skip | invalid
        self.started_at = datetime.now()
        self.raw_log_path = raw_log_path
        self.raw_start_offset = int(raw_start_offset or 0)
        self.raw_end_offset = None
        self.attempts = []                        # [{"n","started_at","result"}]
        self.final_result = ""
        self.final_ok = None
        self.close_ok = None
        self.retry_count = 0
        self.final_badge = ""
        self.finalized = False                    # idempotency latch
        self.finished_at = None
        self.notes = []
        # WHY Retry mode skipped this device. `retry_skipped` on its own covers
        # genuinely different situations and must never be narrated as though
        # they were all "already done":
        #     no_task_config  — the DeviceType has no Task Config at all
        #     empty_task_list — it has one, but it is empty / nothing eligible
        #     all_tasks_done  — every configured task is already recorded done
        self.retry_skip_reason = ""      # one of the codes above
        self.retry_skip_detail = ""      # e.g. the DeviceType name
        # WHY close_ok looks the way it does. close_ok=None alone conflated
        # "Stop All deliberately left the window open", "the device never
        # launched" and "nobody recorded a result":
        #     attempted_success            — a close ran and reported success
        #     attempted_failed             — a close ran and reported failure
        #     not_requested_stop_all       — Stop All leaves windows open
        #     not_applicable_never_launched— no window this run opened
        #     ""                           — unknown / not recorded
        self.close_disposition = ""
        # The close outcome this Run already recorded for the device, from an
        # EARLIER attempt, independent of what the terminal route did:
        #     True / False / None(unverified) / "no_attempt"
        # A route that deliberately requests no close must not erase a known
        # failed or unverified close from earlier in the same Run.
        self.prior_close_result = "no_attempt"

    def note_attempt(self, launch_token=None):
        self.attempts.append({
            "n": len(self.attempts) + 1,
            "launch_token": launch_token,
            "started_at": datetime.now(),
            "result": "",
        })

    def close_attempt(self, result):
        if self.attempts:
            self.attempts[-1]["result"] = result


class HumanDeviceLogGenerator:
    """
    Renders one human-readable narrative from an exact raw-log byte range.

    Deliberately separate from LogAnalyzer: that produces cross-run aggregate
    issue reports and its behaviour is unchanged. This produces one per-device,
    per-session narrative and writes it under logs/human/<device>/ with a .txt
    extension so raw-log globbing (*.log) can never pick it up.
    """

    # "2026-08-08 01:44:56  INFO      message"
    _TS_RE = re.compile(
        r"^(\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2})\s+"
        r"(DEBUG|INFO|WARNING|ERROR|CRITICAL)\s+(.*)$")
    _SEVERE = ("WARNING", "ERROR", "CRITICAL")
    # INFO-level markers that describe a problem or a control action and must
    # survive even though their level is not WARNING+.
    # Deliberately specific. Broad words like "stopped" or "recovery" match
    # healthy prose ("VpnGuard stopped", "no network recovery needed") and would
    # bury the real problems under noise — which is its own kind of evidence
    # loss. Anything WARNING+ is captured regardless of this list.
    _INFO_MARKERS = (
        "FATAL", "Traceback", "exception", "max attempts", "cap exhausted",
        "cap reached", "close_failed", "CLOSE_FAILED", "screenshot failure",
        "unknown page", "escalat", "abandon", "manual stop", "MANUAL STOP",
        "recovery attempt", "recovery failed", "recovering", "reopening",
        "reinstall", "force-killing", "did not respond", "giving up",
        "PAUSE", "paused", "restored after", "retry ", "RETRY",
    )
    # …but never when the line is one of these healthy phrasings.
    _INFO_MARKER_EXCLUDE = (
        "no network recovery needed",
        "device internet OK",
    )
    _RULE = "=" * 80

    def __init__(self, ctx, task_defs=None, renderers=None):
        self.ctx = ctx
        self.task_defs = task_defs or {}
        self.renderers = renderers or {}
        self.records = []
        self._claimed = set()
        # name -> (start_idx, end_idx) half-open record windows. Every section
        # analyses ONLY its own window: a whole-run search let a page matched by
        # vip_collect be reported as an interstitial found during Loading.
        self._ranges = {}
        self._task_ranges = []          # [(key, start_idx, end_idx)]
        # One entry per WORKER attempt in this device's lifecycle. A controller
        # retry relaunches the worker, so the slice can hold several complete
        # attempts; phase windows must bind to the attempt that actually ran
        # them, and the terminal result must come from the LAST attempt.
        self._attempts = []             # [{lo, hi, start, end, ok, result}]
        self._terminal = None           # (lo, hi) of the final attempt

    # ── parsing ───────────────────────────────────────────────────────────────
    def _read_slice(self) -> str:
        """
        Exactly the bytes this run appended, never a timestamp window.

        The raw log is append-only and holds every previous run for the device.
        Byte offsets are immune to date rollover, duplicate timestamps and a
        later run appending while this one is being rendered.
        """
        path = self.ctx.raw_log_path
        if not path or not os.path.exists(path):
            return ""
        start = max(0, int(self.ctx.raw_start_offset or 0))
        end = self.ctx.raw_end_offset
        try:
            with open(path, "rb") as fh:
                fh.seek(start)
                data = fh.read() if end is None else fh.read(max(0, int(end) - start))
        except Exception:
            return ""
        return data.decode("utf-8", errors="replace")

    def _parse(self, text):
        """
        One record per timestamped line.

        A line with no timestamp prefix is OCR text that contained a newline —
        it belongs to the record above it, not to a new event. Treating those as
        independent lines is how a report ends up narrating garbage OCR as if it
        were a program decision.
        """
        recs = []
        for line in text.splitlines():
            m = self._TS_RE.match(line)
            if m:
                ts_s, level, msg = m.groups()
                try:
                    ts = datetime.strptime(ts_s, "%Y-%m-%d %H:%M:%S")
                except Exception:
                    ts = None
                recs.append({"ts": ts, "level": level, "msg": msg,
                             "cont": [], "raw": line})
            elif recs:
                recs[-1]["cont"].append(line)
            # a continuation with no preceding record is unattributable: drop it
        return recs

    # ── small helpers ─────────────────────────────────────────────────────────
    @staticmethod
    def _fmt_dur(sec):
        """Derived duration. Never invents precision the source did not have."""
        try:
            sec = float(sec)
        except Exception:
            return "unknown"
        if sec < 0:
            return "unknown"
        if sec < 60:
            return f"{sec:.1f}s"
        m, s = divmod(int(round(sec)), 60)
        if m < 60:
            return f"{m}m {s}s"
        h, m = divmod(m, 60)
        return f"{h}h {m}m {s}s"

    @staticmethod
    def _fmt_logged(val):
        """
        A duration the PROGRAM logged (elapsed=/took=/waited=).

        Shown exactly as logged — the spec wants `prepare_target_app: 120.8s`, not a
        re-derived `2m 1s` that loses the tenth the program actually measured.
        """
        if val is None:
            return "unknown"
        try:
            f = float(val)
        except Exception:
            return str(val)
        return f"{f:g}s"

    @staticmethod
    def _kv(msg, key):
        """Read `key=value` out of a structured log message."""
        m = re.search(rf"\b{re.escape(key)}=(-?[\w.:%/()\-]+)", msg)
        return m.group(1) if m else None

    @staticmethod
    def _kv_wide(msg, key):
        """
        `key=value` where the value may contain spaces or commas.

        Needed for `parsed=1920x1080 @ 240dpi`, `coord=(960,828)` and
        `percent=None->10%`, all of which the narrow reader truncates.
        """
        m = re.search(rf"\b{re.escape(key)}=(\([^)]*\)|[^=|]+?)(?:\s+\w+=|\s*\||$)", msg)
        return m.group(1).strip() if m else None

    @staticmethod
    def _ts(rec):
        return rec["ts"].strftime("%H:%M:%S") if rec and rec["ts"] else "??:??:??"

    def _find(self, *needles, level=None, first=True, rng=None):
        """
        Search records, optionally restricted to a phase window.

        `rng` is a (start, end) index pair or a phase name. Sections that do not
        pass one are searching the whole slice deliberately (header, counters,
        worker end) — anything phase-specific must scope itself.
        """
        lo, hi = self._window(rng)
        out = []
        for i in range(lo, hi):
            r = self.records[i]
            if level and r["level"] != level:
                continue
            if all(n in r["msg"] for n in needles):
                if first:
                    return i, r
                out.append((i, r))
        return (None, None) if first else out

    def _window(self, rng):
        if rng is None:
            return 0, len(self.records)
        if isinstance(rng, str):
            rng = self._ranges.get(rng)
            if not rng:
                return 0, 0            # phase absent -> empty window, not whole run
        lo, hi = rng
        return max(0, lo), min(len(self.records), hi if hi is not None else len(self.records))

    def _idx(self, *needles, after=0, rng=None):
        lo, hi = self._window(rng)
        for i in range(max(lo, after), hi):
            if all(n in self.records[i]["msg"] for n in needles):
                return i
        return None

    _WORKER_START = "device_worker started"
    _WORKER_END = "[WORKER-END]"

    def _compute_attempts(self):
        """
        Split the slice into worker attempts.

        Each `device_worker started` opens an attempt; it runs to the next start
        or to the end of the slice. Using the FIRST start/end pair for the whole
        lifecycle is what let a successful retry report attempt 1's failure time
        and ok=False as the terminal result.
        """
        starts = [i for i, r in enumerate(self.records)
                  if self._WORKER_START in r["msg"]]
        n = len(self.records)
        out = []
        for j, lo in enumerate(starts):
            hi = starts[j + 1] if j + 1 < len(starts) else n
            end_rec = None
            for k in range(lo, hi):
                if self._WORKER_END in self.records[k]["msg"]:
                    end_rec = self.records[k]        # last one wins
            ok = res = None
            if end_rec is not None:
                ok = (self._kv(end_rec["msg"], "ok") or "").lower() == "true"
                m = re.search(r"result='([^']*)'", end_rec["msg"])
                res = m.group(1) if m else None
            out.append({"lo": lo, "hi": hi, "start": self.records[lo],
                        "end": end_rec, "ok": ok, "result": res})
        self._attempts = out
        self._terminal = (out[-1]["lo"], out[-1]["hi"]) if out else None
        return out

    def _terminal_attempt(self):
        return self._attempts[-1] if self._attempts else None

    _CTRL_BOUNDARY = "[HUMAN-BOUNDARY] controller cleanup begins"

    def _launch_state(self):
        """
        Three genuinely different situations that all used to read as one:

            "never_launched"  ctx attempts 0, raw starts 0
                              nothing was ever started for this device.
            "no_worker_mark"  ctx attempts > 0, raw starts 0
                              the controller DID start a worker process — it
                              exited before writing `device_worker started`.
            "ran"             raw starts > 0
                              the normal parsed-attempt model applies.

        Since _human_note_launch_attempt moved to after proc.start() returns,
        a non-zero ctx attempt count is proof a process really started, so
        "no_worker_mark" cannot be produced by a cfg-build or start() failure.
        """
        if self._attempts:
            return "ran"
        return ("no_worker_mark" if len(getattr(self.ctx, "attempts", []) or [])
                else "never_launched")

    def _attempt_boundaries(self, att):
        """
        (worker_end_index, controller_boundary_index) for one attempt, either
        None. These are the ONLY two things that decide who wrote a counter
        snapshot. Values never decide it — a controller snapshot can be
        non-zero, and a worker snapshot can be all zeros.
        """
        end_i = ctrl_i = None
        for i in range(att["lo"], att["hi"]):
            m = self.records[i]["msg"]
            if end_i is None and self._WORKER_END in m:
                end_i = i
            if ctrl_i is None and self._CTRL_BOUNDARY in m:
                ctrl_i = i
        return end_i, ctrl_i

    def _counter_snaps(self, lo, hi):
        """Indices of every "final counters before wipe" record in [lo, hi)."""
        return [i for i in range(lo, hi)
                if "final counters before wipe" in self.records[i]["msg"]]

    @staticmethod
    def _counter_vals(msg):
        return dict(re.findall(r"(\w+)=(\d+/\d+)", msg))

    def _attempt_counters(self, att):
        """
        The counter snapshot this attempt's WORKER produced, and how sure we are.

        Returns (vals, idx, source) where source is one of:

            "worker_end"     — the snapshot precedes this attempt's
                               [WORKER-END]. A completed worker wrote it.
            "pre_controller" — no [WORKER-END], but the snapshot precedes the
                               controller's cleanup boundary. The bot's
                               _finalize() resets counters (step 4) BEFORE it
                               writes [WORKER-END] (step 5), so a worker killed
                               in between leaves exactly this. Worker-side, but
                               NOT proof of a normal completion.
            "ambiguous"      — no [WORKER-END] and no controller boundary
                               (a legacy log). A snapshot exists but nothing in
                               the log says who wrote it. Reported as unknown;
                               never silently assigned to either side.
            None             — no snapshot at all.
        """
        end_i, ctrl_i = self._attempt_boundaries(att)
        if end_i is not None:
            limit, source = end_i, "worker_end"
        elif ctrl_i is not None:
            limit, source = ctrl_i, "pre_controller"
        else:
            snaps = self._counter_snaps(att["lo"], att["hi"])
            if not snaps:
                return None, None, None
            for i in snaps:
                self._claim(i)
            return (self._counter_vals(self.records[snaps[0]]["msg"]),
                    snaps[0], "ambiguous")
        snaps = self._counter_snaps(att["lo"], limit)
        if not snaps:
            return None, None, None
        for i in self._counter_snaps(att["lo"], att["hi"]):
            self._claim(i)
        return self._counter_vals(self.records[snaps[0]]["msg"]), snaps[0], source

    def _attempt_controller_reset(self, att):
        """
        A counter snapshot this attempt's CONTROLLER wrote — meaning one that
        falls after a proven boundary.

        With no boundary at all there is no such thing: calling the first
        snapshot in the range "controller cleanup" just because the attempt
        died is a guess, and it was wrong for exactly the case that motivated
        this — a worker that reset its own counters and was killed before
        [WORKER-END]. Returns (vals, idx) or (None, None).
        """
        end_i, ctrl_i = self._attempt_boundaries(att)
        start = ctrl_i if ctrl_i is not None else end_i
        if start is None:
            return None, None
        snaps = self._counter_snaps(start + 1, att["hi"])
        if not snaps:
            return None, None
        self._claim(snaps[0])
        return self._counter_vals(self.records[snaps[0]]["msg"]), snaps[0]

    def _attempt_recording(self, att):
        """
        The recording lifecycle belonging to ONE worker attempt.

        Each relaunched worker starts and finalises its own recording, so
        combining folders/segments/flags across attempts describes a session
        that never existed.
        """
        rng = (att["lo"], att["hi"])
        _, en = self._find("recording enabled ->", rng=rng)
        segs = self._find("segment", "saved and validated", first=False, rng=rng)
        _, stop = self._find("recording stopped —", rng=rng)
        folder = en["msg"].split("-> ")[-1].strip() if en else None
        # Problem evidence counts as recording activity in its own right: an
        # attempt that only ever produced invalid segments or screenrecord
        # errors still had a recording lifecycle, and hiding it because no
        # segment validated is exactly backwards.
        bad = (self._find("segment", "invalid", first=False, rng=rng)
               + self._find("screenrecord", "stderr", first=False, rng=rng))
        _, loop = self._find("segment loop started", rng=rng)
        # Explicit recording-FINALISATION failures. Both are survivable: the
        # bot's _finalize() wraps stop_device_recording() in try/except and
        # keeps going, and stop_device_recording() has its own except that only
        # warns. After either, the worker still writes a normal [WORKER-END].
        # So "no stop summary" does NOT imply the worker died.
        fin_err = (self._find("stop_device_recording raised:", first=False,
                              rng=rng)
                   + self._find("[RECORD]", "| stop failed:", first=False,
                                rng=rng))
        info = {"enabled": en, "folder": folder, "segments": segs, "stop": stop,
                "failed": None, "incomplete": None, "merged": None,
                # Recording activity with no "recording stopped —" summary.
                # The worker writes that line during _finalize; a worker killed
                # first leaves validated segments on disk and no verdict. The
                # segments are real and must be kept, but completeness, merge
                # state and failure state are simply unknown — reporting the
                # folder and segment list alone reads as a success.
                "bad": bad, "loop": loop, "fin_err": fin_err,
                # Any evidence a recording lifecycle existed for this attempt.
                # This is what the renderer gates on, so the two can never
                # disagree about whether there was a recording to report.
                "activity": bool(en or segs or stop or folder or bad or loop),
                "unfinalized": bool((en or segs or folder or bad or loop)
                                    and not stop)}
        # WHY there is no stop summary — decided from raw evidence, never from
        # final_ok. The four states are mutually exclusive.
        if not info["activity"]:
            info["fin_state"] = None
        elif stop:
            info["fin_state"] = "completed_summary"
        elif att["end"] is None:
            info["fin_state"] = "interrupted_by_worker_exit"
        elif fin_err:
            info["fin_state"] = "finalization_error"
        else:
            info["fin_state"] = "missing_summary_after_worker_completion"
        if stop:
            info["failed"] = self._kv(stop["msg"], "failed")
            info["incomplete"] = self._kv(stop["msg"], "incomplete")
            info["merged"] = self._kv(stop["msg"], "merged")
        return info

    def _compute_ranges(self):
        """
        Establish the record windows every section is allowed to look at.

        Boundaries come from the program's own phase markers, never from "the
        next page match" — that is exactly how a later task's page detection
        leaked into the Loading narrative.
        """
        n = len(self.records)
        R = {}
        # Phase windows are computed INSIDE the terminal attempt. An abandoned
        # earlier attempt may have entered prepare_target_app/setup and left its markers
        # in the slice; binding the successful attempt's Setup/VPN/TargetApp sections
        # to those would describe work that was thrown away.
        T = self._terminal
        i_start = self._idx("device_worker started", rng=T) or (T[0] if T else 0)
        i_btarget_app = self._idx("prepare_target_app | start | SETUP BEGIN", rng=T)
        i_p1s = self._idx("| setup_device | start |", rng=T)
        i_p1e = self._idx("| setup_device | end |", rng=T)
        i_p2s = self._idx("| setup_vpn | start |", rng=T)
        i_p2e = self._idx("| setup_vpn | end |", rng=T)
        i_p3s = self._idx("| setup_target_app | start |", rng=T)
        i_p3e = self._idx("| setup_target_app | end |", rng=T)
        i_ld = self._idx("| Loading | start |", rng=T)
        i_pl = self._idx("| Loading | post_loading |", rng=T)
        i_btarget_appe = self._idx("prepare_target_app | end | SETUP COMPLETE", rng=T)
        _tlo, _thi = self._window(T)
        # First task header inside the terminal attempt.
        i_task0 = None
        for i in range(_tlo, _thi):
            if "TASK: " in self.records[i]["msg"]:
                i_task0 = i
                break

        def rng(a, b):
            if a is None:
                return None
            return (a, b if b is not None else n)

        R["terminal_attempt"] = (_tlo, _thi) if T else None
        R["startup"] = (i_start, i_btarget_app if i_btarget_app is not None else _thi)
        R["prepare_target_app"] = rng(i_btarget_app, (i_btarget_appe + 1) if i_btarget_appe is not None else i_task0)
        R["setup_device"] = rng(i_p1s, (i_p1e + 1) if i_p1e is not None else i_p2s)
        R["setup_vpn"] = rng(i_p2s, (i_p2e + 1) if i_p2e is not None else i_p3s)
        R["setup_target_app"] = rng(i_p3s, (i_p3e + 1) if i_p3e is not None else i_task0)
        # Loading ends where post-loading begins, else at the setup_target_app end, else
        # at the first task header. Never at an arbitrary later page match.
        ld_end = i_pl if i_pl is not None else (
            i_p3e if i_p3e is not None else (i_task0 if i_task0 is not None else n))
        R["loading"] = rng(i_ld, ld_end)
        pl_end = (i_p3e + 1) if i_p3e is not None else (
            i_task0 if i_task0 is not None else n)
        R["post_loading"] = rng(i_pl, pl_end)

        # One window per task attempt.
        heads = [i for i in range(_tlo, _thi) if "TASK: " in self.records[i]["msg"]]
        self._task_ranges = []
        for j, h in enumerate(heads):
            end = heads[j + 1] if j + 1 < len(heads) else n
            m = re.search(r"TASK: (\w+)", self.records[h]["msg"])
            self._task_ranges.append(((m.group(1) if m else "?"), h, end))
        R["tasks"] = (heads[0], n) if heads else None
        # Cleanup / recording finalisation: after the last task, or after
        # prepare_target_app when there is no task.
        i_clean = None
        for key in ("[WORKER-END]", "recording stopped —", "final counters before wipe"):
            k = self._idx(key, rng=T)
            if k is not None:
                i_clean = k if i_clean is None else min(i_clean, k)
        R["cleanup"] = rng(i_clean, n)
        return {k: v for k, v in R.items() if v is not None}

    def _claim(self, idx):
        if idx is not None:
            self._claimed.add(idx)

    # ── rendering ─────────────────────────────────────────────────────────────
    def build(self) -> str:
        self.records = self._parse(self._read_slice())
        self._compute_attempts()
        self._ranges = self._compute_ranges()
        parts = [self._header()]
        for section in (self._sec_no_worker, self._sec_device_start,
                        self._sec_recording_start,
                        self._sec_prepare_target_app, self._sec_phase1, self._sec_phase2,
                        self._sec_target_app_handover, self._sec_phase3,
                        self._sec_loading, self._sec_post_loading,
                        self._sec_prepare_target_app_complete, self._sec_tasks,
                        self._sec_guards, self._sec_pause,
                        self._sec_recording_final, self._sec_counters,
                        self._sec_attempts, self._sec_worker_finished,
                        self._sec_controller,
                        self._sec_problems, self._sec_summary):
            try:
                block = section()
            except Exception as exc:            # a broken section must not lose the rest
                block = [f"(section {section.__name__} could not be rendered: {exc!r})"]
            if block:
                parts.append("\n".join(block))
        return "\n\n".join(p for p in parts if p).rstrip() + "\n"

    def _title(self, name):
        return [self._RULE, name, self._RULE, ""]

    def _worker_times(self):
        """
        (first_start, terminal_end, lifecycle_span, active_total, terminal_dur).

        LIFECYCLE SEMANTICS:
          * `first_start`   — the first attempt's `device_worker started`.
          * `terminal_end`  — the FINAL attempt's own `[WORKER-END]`, or None.
                              It is NEVER taken from an earlier attempt: walking
                              backwards for "any end marker" produced
                              "Finished: 01:00:06 (worker attempt 2 of 2)" for a
                              worker that did not start until 01:01:00.
          * `lifecycle_span`— first_start → terminal_end, only when the terminal
                              attempt actually ended. Includes the retry gap and
                              is labelled as such.
          * `active_total`  — sum of the attempts that DID record an end.
          * `terminal_dur`  — the final attempt's own duration, or None when it
                              never wrote WORKER-END.
        ctx.finished_at is controller-side and is never used here.
        """
        if not self._attempts:
            return None, None, None, None, None
        first = self._attempts[0]["start"]
        term = self._attempts[-1]
        sa = first["ts"] if first and first["ts"] else None
        # Terminal attempt ONLY. No fallback.
        te = term["end"]["ts"] if (term["end"] and term["end"]["ts"]) else None
        span = (te - sa).total_seconds() if (sa and te) else None
        tstart = term["start"]["ts"] if (term["start"] and term["start"]["ts"]) else None
        tdur = (te - tstart).total_seconds() if (te and tstart) else None
        active = 0.0
        seen = False
        for a in self._attempts:
            if a["start"] and a["end"] and a["start"]["ts"] and a["end"]["ts"]:
                active += (a["end"]["ts"] - a["start"]["ts"]).total_seconds()
                seen = True
        return sa, te, span, (active if seen else None), tdur

    def _header(self):
        c = self.ctx
        tasks = self._task_label()
        lines = [self._RULE, "DEVICE RUN — HUMAN READABLE LOG", self._RULE, ""]
        lines.append(f"Device: {c.friendly_name} ({c.adb_id})")
        if c.device_type:
            lines.append(f"Device type: {c.device_type}")
        lines.append(f"Run session: {c.session_id}")
        wa, wb, wspan, wactive, wterm = self._worker_times()
        n_att = len(self._attempts)
        term = self._terminal_attempt()
        # `wa` is the first real `device_worker started` timestamp. Without one
        # this is the controller's Run-context registration time, and calling
        # it "Started" invites reading it as a worker start that never happened.
        _sl = self._launch_state()
        lines.append(
            f"{'Started' if _sl == 'ran' else 'Run context started'}: "
            f"{(wa or c.started_at).strftime('%Y-%m-%d %H:%M:%S')}")
        lines.append(f"Task(s): {tasks}")
        lines.append(f"Final result: {self._final_label()}")
        if n_att > 1 and term and term["start"] and term["start"]["ts"]:
            lines.append(f"Worker attempt {n_att} started: "
                         f"{term['start']['ts'].strftime('%H:%M:%S')}")
        if wb:
            lines.append(f"Finished: {wb.strftime('%Y-%m-%d %H:%M:%S')}"
                         + (f" (worker attempt {n_att} of {n_att})"
                            if n_att > 1 else ""))
        elif self._attempts:
            # The terminal worker never wrote WORKER-END. Say so rather than
            # borrowing an earlier attempt's timestamp.
            lines.append("Worker finish: unavailable — the terminal worker "
                         "exited without writing WORKER-END")
        if wspan is not None:
            if n_att > 1:
                lines.append(
                    f"Total worker time: {self._fmt_dur(wspan)}  "
                    f"(first start → final end, across {n_att} attempts, "
                    f"including the gap(s) between them)")
                if wterm is not None:
                    lines.append(f"Terminal worker duration: {self._fmt_dur(wterm)}")
                if wactive is not None and abs(wactive - wspan) >= 1:
                    lines.append(
                        f"Active worker time: {self._fmt_dur(wactive)}  "
                        f"(sum of the {n_att} attempts themselves)")
            else:
                lines.append(f"Total worker time: {self._fmt_dur(wspan)}")
        elif self._attempts:
            lines.append("Total worker time: unavailable — the terminal worker "
                         "did not record an end")
            if wactive is not None:
                lines.append(f"Active worker time (completed attempts only): "
                             f"{self._fmt_dur(wactive)}")
        elif self._launch_state() == "no_worker_mark":
            lines.append("Worker-start record: unavailable — the process "
                         "started but exited")
            lines.append("                     before writing "
                         "`device_worker started`")
        elif self._launch_state() == "never_launched":
            # NOT `not self.records`. _on_run_done runs its controller cleanup
            # for cfg_build_failed and proc_start_failed too, so the slice can
            # hold the [HUMAN-BOUNDARY] marker and a [RESET] line for a device
            # whose worker never started. A non-empty slice proves the
            # controller wrote something, not that a worker ran.
            lines.append("Worker: never launched")
        if c.finished_at and (wb is None or abs(
                (c.finished_at - wb).total_seconds()) >= 1):
            lines.append("Controller terminal at: "
                         f"{c.finished_at.strftime('%Y-%m-%d %H:%M:%S')}")
        if len(c.attempts) > 1 or n_att > 1:
            lines.append(f"Launch attempts: {max(len(c.attempts), n_att)}")
        elif self._launch_state() == "no_worker_mark":
            # A real process launch that produced no worker log. Stating 1 is
            # the whole point: it separates "we started something that died"
            # from "we never started anything".
            lines.append(f"Launch attempts: {len(c.attempts)}")
        elif not c.attempts and not self._attempts:
            lines.append("Launch attempts: 0 (never launched)")
        return "\n".join(lines)

    def _task_label(self):
        c = self.ctx
        if c.task_action == "retry_skipped":
            keys = c.resolved_tasks or c.requested_tasks
            labels = [(self.task_defs.get(k) or {}).get("label", k) for k in keys]
            reason = getattr(c, "retry_skip_reason", "")
            # "already done" is a CLAIM about the sheet/cache and may only be
            # made when the code actually proved it.
            if reason == "all_tasks_done" and labels:
                return "[" + ", ".join(labels) + " — already done]"
            if reason == "no_task_config":
                return "[No Task Config for this DeviceType]"
            if reason == "empty_task_list":
                return "[Task Config is empty — nothing to retry]"
            return ("[" + ", ".join(labels) + "]") if labels else "[None pending]"
        if c.task_action == "skip":
            return "[None]"
        if c.task_action == "invalid":
            keys = c.requested_tasks or c.resolved_tasks
            return f"[Invalid configuration: {', '.join(map(str, keys)) or 'unknown'}]"
        keys = c.resolved_tasks or c.requested_tasks
        if not keys:
            return "[Setup only — prepare_target_app]"
        labels = [(self.task_defs.get(k) or {}).get("label", k) for k in keys]
        return "[" + ", ".join(labels) + "]"

    def _final_label(self):
        c = self.ctx
        if c.task_action == "invalid":
            return "INVALID TASKS"
        if c.task_action == "retry_skipped" or (c.final_result or "") == "retry_skipped":
            return "SKIPPED BY RETRY MODE"
        if c.task_action == "skip":
            return "SKIPPED"
        r = (c.final_result or "").lower()
        if c.final_ok:
            return "SUCCESS"
        return {
            "stopped": "STOPPED",
            "stopped_before_launch": "STOPPED BEFORE LAUNCH",
            "stopped_by_safe_reset": "STOPPED — SAFE DAILY RESET",
            "stopped_by_fatal_run": "STOPPED — RUN ABORTED BY FATAL ERROR",
            "stopped_by_controller_close": "STOPPED — CONTROLLER CLOSED",
            "retry_schedule_failed": "FAILED — ADB RETRY COULD NOT BE SCHEDULED",
            "retry_skipped": "SKIPPED BY RETRY MODE",
            "skipped": "SKIPPED",
            "invalid_tasks": "INVALID TASKS",
            "cfg_build_failed": "FAILED — CONFIG BUILD",
            "proc_start_failed": "FAILED — WORKER START",
            "process_died": "FAILED — WORKER DIED",
            "adb_connect_failed": "FAILED — ADB CONNECTION EXHAUSTED",
        }.get(r, f"FAILED — {r.upper()}" if r else "FAILED")

    # ── sections ──────────────────────────────────────────────────────────────
    def _sec_no_worker(self):
        """
        Explicit narrative for a device whose worker never started.

        Without this the report is a header and a summary with no explanation.
        Nothing here invents worker events — it states, from controller
        metadata, that none exist.
        """
        if self._attempts:
            return []
        c = self.ctx
        res = (c.final_result or "").lower()
        if self._launch_state() == "no_worker_mark":
            # A process really did start — saying "never started" here would
            # contradict the controller's own record and hide a real crash.
            out = ["The controller successfully launched the worker process, but "
                   "it exited",
                   "before writing its `device_worker started` record.", "",
                   "No worker-side phase timing is available: there is no device "
                   "setup, VPN,",
                   "Target Application, Loading or task narrative below because the "
                   "worker never got",
                   "far enough to log one. This is NOT the same as the device "
                   "being skipped."]
            if res:
                out += ["", "Controller result:", f"    {res}"]
            for note in c.notes:
                out += ["", f"Controller note: {note}"]
            return self._title("WORKER LAUNCHED — NO WORKER LOG") + out
        out = ["No worker process was ever started for this device in this Run."]
        if res == "retry_skipped":
            reason = getattr(c, "retry_skip_reason", "")
            detail = getattr(c, "retry_skip_detail", "")
            out.append("")
            if reason == "no_task_config":
                out += ["Retry mode skipped this device because no Task Config "
                        "exists for",
                        f'DeviceType "{detail or c.device_type or "?"}".', "",
                        "Nothing was checked against the sheet or the status "
                        "cache, so this",
                        "report makes no claim about whether any task was "
                        "already done."]
            elif reason == "empty_task_list":
                out += ["Retry mode skipped this device because its Task Config "
                        "is empty —",
                        "there were no tasks eligible to retry.", "",
                        "This is not the same as the work being already "
                        "complete; nothing",
                        "was configured to run in the first place."]
            elif reason == "all_tasks_done":
                out += ["Retry mode found no pending work because all configured "
                        "tasks were",
                        "already recorded as done."]
            else:
                out += ["Retry mode skipped this device. The controller did not "
                        "record which",
                        "of its skip conditions applied, so this report does not "
                        "guess."]
        elif res == "stopped_before_launch":
            out += ["", "Reason:",
                    "    The device was queued, but the Run was stopped before its",
                    "    turn came."]
        elif res in ("skipped", "invalid_tasks"):
            out += ["", "Reason:",
                    f"    The device's task configuration resolved to "
                    f"{'no runnable tasks' if res == 'invalid_tasks' else 'nothing to do'}."]
        elif res in ("cfg_build_failed", "proc_start_failed"):
            out += ["", "Reason:",
                    "    The worker could not be created — see CONTROLLER COMPLETION."]
        elif res == "stopped":
            out += ["", "Reason:",
                    "    The Run was stopped while this device was waiting."]
        elif res == "stopped_by_safe_reset":
            out += ["", "Reason:",
                    "    The safe daily reset stopped the Run before this "
                    "device launched."]
        elif res == "stopped_by_fatal_run":
            out += ["", "Reason:",
                    "    The Run was aborted by a fatal error on another "
                    "device before",
                    "    this one launched."]
        elif res == "stopped_by_controller_close":
            out += ["", "Reason:",
                    "    The controller window was closed before this device "
                    "launched."]
        for note in c.notes:
            out += ["", f"Controller note: {note}"]
        out += ["",
                "There is therefore no device setup, VPN, Target Application, Loading or",
                "task narrative below — none of it happened."]
        return self._title("NO WORKER LAUNCHED") + out

    def _sec_device_start(self):
        """
        The TERMINAL attempt's startup. Earlier attempts are summarised here and
        detailed under WORKER ATTEMPTS, so a successful retry is not described
        using the abandoned attempt's connection story.
        """
        T = "terminal_attempt" if self._terminal else None
        out = []
        n_att = len(self._attempts)
        i, r = self._find("device_worker started", rng=T)
        if r:
            self._claim(i)
            out.append(f"At {self._ts(r)} the worker process started"
                       + (f" (attempt {n_att} of {n_att})." if n_att > 1 else "."))
        if n_att > 1:
            out.append("")
            out.append(f"{n_att - 1} earlier worker attempt(s) were made and "
                       f"abandoned; see WORKER ATTEMPTS.")
        i, r = self._find("NOT in adb devices", rng=T)
        if r:
            self._claim(i)
            out.append("")
            out.append("The device was NOT present in `adb devices`.")
            out.append("Opening the BlueStacks instance...")
        else:
            i, r = self._find("already in adb devices", rng=T)
            if r:
                self._claim(i)
                out.append("")
                out.append("The device was already present in `adb devices`.")
        i, r = self._find("waiting up to", "after launch", rng=T)
        if r:
            self._claim(i)
            w = re.search(r"waiting up to (\d+)s", r["msg"])
            if w:
                out.append("")
                out.append(f"Waiting up to {w.group(1)}s for the newly opened device.")
        for i, r in self._find("ADB connected on attempt", first=False, rng=T):
            self._claim(i)
            n = re.search(r"attempt (\d+)", r["msg"])
            out.append("")
            out.append(f"ADB connected successfully on attempt {n.group(1) if n else '?'}.")
            _, start = self._find("device_worker started", rng=T)
            if start and start["ts"] and r["ts"]:
                out.append(f"Time from worker start to ADB connection: about "
                           f"{self._fmt_dur((r['ts'] - start['ts']).total_seconds())}.")
        fails = self._find("Device not responding after launch", first=False, rng=T)
        if fails:
            for i, r in fails:
                self._claim(i)
            out.append("")
            out.append(f"ADB did not answer on {len(fails)} earlier attempt(s) "
                       f"within this worker; the launch was retried.")
        if not out:
            return []
        return self._title("DEVICE START") + out

    def _sec_recording_start(self):
        """The TERMINAL attempt's recording start — not attempt 1's folder."""
        term = self._terminal_attempt()
        rng = (term["lo"], term["hi"]) if term else None
        out = []
        i, r = self._find("recording enabled ->", rng=rng)
        if r:
            self._claim(i)
            out.append("Screen recording was enabled for this worker.")
            out.append(f"Folder: {r['msg'].split('-> ')[-1].strip()}")
        i, r = self._find("recording waiting for readiness", rng=rng)
        if r:
            self._claim(i)
            out.append("")
            out.append("Recording waited for Android and /sdcard to become ready "
                       "before starting a segment.")
            act = self._kv(r["msg"], "activity")
            if act:
                out.append(f"Activity at that moment: {act}")
        i, r = self._find("recording readiness complete", rng=rng)
        if r:
            self._claim(i)
            w = self._kv(r["msg"], "waited")
            out.append("")
            out.append(f"At {self._ts(r)} readiness completed after "
                       f"{w or 'an unknown time'}"
                       + (f" ({self._kv(r['msg'], 'activity')})"
                          if self._kv(r["msg"], "activity") else "") + ".")
            out.append("Segment capture could begin from this point.")
        i, r = self._find("segment loop started", rng=rng)
        if r:
            self._claim(i)
            out.append("")
            out.append(f"The segment loop started at {self._ts(r)}.")
        if not out:
            return []
        return self._title("RECORDING") + out

    def _sec_prepare_target_app(self):
        # Terminal attempt: an abandoned earlier attempt also logs SETUP BEGIN,
        # and a whole-run search reported ITS timestamp for this attempt.
        i, r = self._find("prepare_target_app | start | SETUP BEGIN", rng="prepare_target_app")
        if not r:
            return []
        self._claim(i)
        out = [f"prepare_target_app began at {self._ts(r)}."]
        fs = self._kv(r["msg"], "force_stop_first")
        if fs:
            out.append(f"ProtonVPN and TargetApp were force-stopped first: {fs}")
        return self._title("BEFORE_TARGET_APP") + out

    def _phase_block(self, fn_name, title, extra=None):
        rng = fn_name if fn_name in self._ranges else None
        i0, start = self._find(f"| {fn_name} | start |", rng=rng)
        ends = self._find(f"| {fn_name} | end |", first=False, rng=rng)
        if not start and not ends:
            return []
        self._claim(i0)
        out = []
        if start:
            out.append(f"Started at {self._ts(start)}.")
        if extra:
            out.extend(extra(rng))
        for i, e in ends:
            self._claim(i)
            el = self._kv(e["msg"], "elapsed")
            sig = self._kv(e["msg"], "signal")
            out.append("")
            out.append(f"Result: {sig or 'unknown'}")
            if el:
                out.append(f"Phase duration: {self._fmt_logged(el)}")
        return self._title(title) + out

    def _sec_phase1(self):
        def extra(rng):
            o = []
            i, r = self._find("device_ready | first activity detected", rng=rng)
            if r:
                self._claim(i)
                o.append("")
                o.append(f"First Android activity: {self._kv(r['msg'], 'page')}")
                el = self._kv(r["msg"], "elapsed")
                if el:
                    o.append(f"Device readiness took {self._fmt_logged(el)}.")
            i, r = self._find("[DISPLAY-PREFLIGHT]", rng=rng)
            if r:
                self._claim(i)
                o.append("")
                if "DISAGREES" in r["msg"]:
                    o.append("BlueStacks configuration contained a misleading display hint.")
                    o.append("This did NOT control the decision.")
                    hint = r["msg"].split("|")[-1].strip()
                    o.append(f"    {hint}")
                else:
                    o.append("BlueStacks configuration display hints were read "
                             "(informational only).")
            i, r = self._find("[DISPLAY]", "wm size raw=", rng=rng)
            if r:
                self._claim(i)
                parsed = self._kv_wide(r["msg"], "parsed")
                o.append("")
                o.append("Live Android display:")
                o.append(f"    {parsed or 'unknown'}")
                o.append(f"    Result: {'PASS' if 'PASS' in r['msg'] else 'FAIL'}")
            i, r = self._find("touch device", "confirmed as BlueStacks Virtual Touch", rng=rng)
            if r:
                self._claim(i)
                o.append("")
                o.append("Touch device confirmed.")
            i, r = self._find("startup_internet | device internet confirmed", rng=rng)
            if r:
                self._claim(i)
                o.append("")
                o.append("Startup internet check (pre-VPN): OK.")
            i, r = self._find("target_app_version | version comparison", rng=rng)
            if r:
                self._claim(i)
                inst, avail = self._kv(r["msg"], "installed"), self._kv(r["msg"], "available")
                o.append("")
                o.append(f"Target Application installed {inst}, available {avail}.")
                j, r2 = self._find("version match — no update needed", rng=rng)
                if r2:
                    self._claim(j)
                    o.append("Versions match — no update was needed.")
            i, r = self._find("vpn_install | ProtonVPN already installed", rng=rng)
            if r:
                self._claim(i)
                o.append("")
                o.append("ProtonVPN was already installed — the install cap was not consumed.")
            else:
                i, r = self._find("vpn_install", "installed", level="INFO", rng=rng)
                if r:
                    self._claim(i)
                    o.append("")
                    o.append("ProtonVPN install step ran.")
            return o
        return self._phase_block("setup_device", "PHASE 1 — DEVICE SETUP", extra)

    def _sec_phase2(self):
        def extra(rng):
            o = []
            i, r = self._find("stage1_routing | activity reached", rng=rng)
            if r:
                self._claim(i)
                o.append("")
                o.append(f"ProtonVPN RoutingActivity appeared after "
                         f"{self._fmt_logged(self._kv(r['msg'], 'elapsed'))}.")
            for i, r in self._find("| tun0 ", first=False, rng=rng):
                pass
            i, r = self._find("stage2_connect | UIA dump end", rng=rng)
            if r:
                self._claim(i)
                o.append("")
                o.append(f"UIAutomator dump took {self._fmt_logged(self._kv(r['msg'], 'elapsed'))} "
                         f"({self._kv(r['msg'], 'result')}).")
            i, r = self._find("[VPN-UI] state=", rng=rng)
            if r:
                self._claim(i)
                st = re.search(r"state='([^']+)'", r["msg"])
                o.append("")
                if st and "fallback" in st.group(1):
                    o.append("ProtonVPN was on the unprotected screen, but UIAutomator did")
                    o.append("not expose a usable Connect label or button bounds.")
                o.append("")
                o.append("Classification:")
                o.append(f"    {st.group(1) if st else 'unknown'}")
            i, r = self._find("[VPN-FIND]", "fallback Connect=", rng=rng)
            if r:
                self._claim(i)
                c = re.search(r"fallback Connect=\(([^)]+)\)", r["msg"])
                o.append("")
                o.append("Landscape fallback coordinate:")
                o.append(f"    ({c.group(1) if c else '?'})")
            for i, r in self._find("stage2_connect | clicking Connect", first=False, rng=rng):
                self._claim(i)
                o.append("")
                o.append(f"VPN Connect attempt:")
                o.append(f"    {self._kv(r['msg'], 'attempt') or '?'}")
                o.append("")
                o.append(f"Clicked at {self._kv_wide(r['msg'], 'coord') or '?'} "
                         f"({self._kv_wide(r['msg'], 'button') or 'Connect'}).")
            # A failed verification dump that a later tun0 success supersedes.
            i, r = self._find("[VPN-UI]", "UIA dump end", "result=FAILED", rng=rng)
            if r:
                self._claim(i)
                o.append("")
                o.append("A follow-up UIAutomator verification dump failed.")
                o.append("This did not invalidate the attempt — tun0 was checked directly.")
            for i, r in self._find("Connect click REGISTERED", first=False, rng=rng):
                self._claim(i)
                o.append("")
                o.append("The Connect click registered.")
            i, r = self._find("tun0 UP — VPN connected", rng=rng)
            if r:
                self._claim(i)
                o.append("")
                o.append("tun0 then appeared:")
                o.append("    UP")
            i, r = self._find("final_verify | tun0 verified UP", rng=rng)
            if r:
                self._claim(i)
                o.append("")
                o.append("Final verification confirmed tun0 UP.")
            downs = self._find("tun0", "DOWN", first=False, rng=rng)
            if downs:
                for i, _ in downs:
                    self._claim(i)
                o.append("")
                o.append(f"tun0 was observed DOWN {len(downs)} time(s) before it came UP.")
            for i, r in self._find("Change Server", first=False, rng=rng):
                self._claim(i)
                o.append("")
                o.append("A Change Server recovery was used.")
            return o
        return self._phase_block("setup_vpn", "PHASE 2 — PROTONVPN", extra)

    def _sec_target_app_handover(self):
        out = []
        i, r = self._find("prepare_target_app | gap |", rng="prepare_target_app")
        if r:
            self._claim(i)
            out.append(r["msg"].split("| gap |")[-1].strip() + ".")
        i, r = self._find("pre_setup_target_app | tun0 verified UP", rng="prepare_target_app")
        if r:
            self._claim(i)
            out.append("tun0 was re-verified UP immediately before Target Application was opened.")
        if not out:
            return []
        return self._title("BEFORE TARGET_APP → TARGET_APP") + out

    def _sec_phase3(self):
        def extra(rng):
            o = []
            i, r = self._find("open_target_app | launch attempt", rng=rng)
            if r:
                self._claim(i)
                o.append("")
                o.append("Target Application launch requested.")
            i, r = self._find("TargetApp foreground confirmed in", rng=rng)
            if r:
                self._claim(i)
                m = re.search(r"confirmed in ([\d.]+)s", r["msg"])
                o.append(f"TargetApp reached the foreground in {m.group(1)}s."
                         if m else "TargetApp reached the foreground.")
            return o
        return self._phase_block("setup_target_app", "PHASE 3 — TARGET APPLICATION", extra)

    # ── page-detection tracking ───────────────────────────────────────────────
    _PAGE_RE = re.compile(
        r"── is_on_page ── \[([^\]]+)\]: pixel=([\d.]+) text=([\d.]+) "
        r"final=([\d.]+) threshold=([\d.]+) → (MATCH|no match)")

    def _page_events(self, rng=None):
        """(idx, rec, page, pixel, text, final, threshold, matched) in a window."""
        lo, hi = self._window(rng)
        out = []
        for i in range(lo, hi):
            r = self.records[i]
            m = self._PAGE_RE.search(r["msg"])
            if m:
                out.append((i, r, m.group(1), float(m.group(2)), float(m.group(3)),
                            float(m.group(4)), float(m.group(5)), m.group(6) == "MATCH"))
        return out

    def _sec_loading(self):
        LR = "loading"
        i0, start = self._find("| Loading | start |", rng=LR)
        if not start:
            return []
        self._claim(i0)
        out = [f"Loading() began at {self._ts(start)}."]

        i, r = self._find("initial_window | valid page appeared", rng=LR)
        if r:
            self._claim(i)
            page, el = self._kv(r["msg"], "page"), self._kv(r["msg"], "elapsed")
            out += ["", "FIRST VALID PAGE", "",
                    f"At {self._ts(r)} a valid {page} page appeared.", "",
                    "Time from Loading() start:", f"    {self._fmt_logged(el)}", "",
                    "What was visible before this:",
                    "    TargetApp was foreground, but no recognized page was stable yet.", "",
                    f"{str(page).capitalize()} detector:", "    MATCH"]
        i, r = self._find("dispatch | page classified", rng=LR)
        if r:
            self._claim(i)
            if "reused" in r["msg"]:
                out += ["", "The page found by the initial window was reused for "
                            "dispatch — it was not re-classified."]

        prog = self._find("loading_percent | progress", first=False, rng=LR)
        if prog:
            seq = []
            for i, r in prog:
                self._claim(i)
                p = self._kv_wide(r["msg"], "percent")
                if p:
                    seq.append(p)
            pcts = []
            for s in seq:
                tail = s.split("->")[-1]
                if tail not in pcts:
                    pcts.append(tail)
            out += ["", "Progress detected:", ""] + [f"    {p}" for p in pcts]

        sweeps = self._find("periodic full interstitial sweep", first=False, rng=LR)
        if sweeps:
            reasons = {}
            for i, r in sweeps:
                self._claim(i)
                reasons[self._kv(r["msg"], "reason") or "?"] = \
                    reasons.get(self._kv(r["msg"], "reason") or "?", 0) + 1
            out += ["", f"{len(sweeps)} full interstitial sweep(s) ran while watching "
                        f"the loading percentage."]
            for k, n in reasons.items():
                out.append(f"    reason={k} ×{n}")
            interstitials = [x for x in self._page_events(LR)
                             if x[2] not in ("loading", "loading after update",
                                             "target app main", "game main map")]
            if interstitials and not any(x[7] for x in interstitials):
                out.append("Every sweep checked the warning / sign-in / "
                           "connection-issue fingerprints; none of them were present.")
            else:
                for _, r2, page, _px, _tx, fin, _thr, matched in interstitials:
                    if matched:
                        out.append(f"A sweep DID find an interstitial: {page} "
                                   f"(final {fin:.3f}).")

        # Near-miss page checks worth showing.
        near = []
        for i, r, page, px, tx, fin, thr, matched in self._page_events(LR):
            if not matched and (px >= 0.50 or fin >= thr - 0.10):
                near.append((page, px, tx, fin, thr))
            if not matched:
                self._claim(i)
        # A required-text failure only matters when the PIXEL score was high
        # enough that accepting it would have been plausible. The DEBUG line
        # "[page] pixel: a/b = 0.xxx" immediately precedes the checks.
        last_px = {}
        req_fail = []
        _lo, _hi = self._window(LR)
        for i in range(_lo, _hi):
            r = self.records[i]
            m = re.search(r"── is_on_page ── \[([^\]]+)\] pixel: \d+/\d+ = ([\d.]+)",
                          r["msg"])
            if m:
                last_px[m.group(1)] = float(m.group(2))
                continue
            if "required text FAILED" in r["msg"]:
                self._claim(i)
                pm = re.search(r"\[([^\]]+)\]", r["msg"])
                if pm and last_px.get(pm.group(1), 0.0) >= 0.40:
                    req_fail.append((i, r))
        if near or req_fail:
            out += ["", "FALSE POSITIVES REJECTED", ""]
            by_page = {}
            for page, px, tx, fin, thr in near:
                d = by_page.setdefault(page, {"n": 0, "px": [], "fin": [], "thr": thr})
                d["n"] += 1
                d["px"].append(px)
                d["fin"].append(fin)
            for page, d in by_page.items():
                times = f"{d['n']} times" if d["n"] > 1 else "once"
                out.append(f"The '{page}' fingerprint came close {times}: pixel "
                           f"similarity up to {max(d['px']):.3f}, best final score "
                           f"{max(d['fin']):.3f} against a {d['thr']:.2f} threshold.")
                out.append("The program correctly rejected it as a false positive.")
                out.append("")
            if req_fail:
                pages = sorted({re.search(r"\[([^\]]+)\]", r["msg"]).group(1)
                                for _, r in req_fail
                                if re.search(r"\[([^\]]+)\]", r["msg"])})
                out.append(f"A required text check failed for: {', '.join(pages)}, "
                           f"despite a notable pixel similarity.")
                out.append("Those pages were correctly scored 0 rather than accepted.")

        conn = [x for x in self._page_events(LR) if x[2] == "connection issue"]
        if conn and not any(x[7] for x in conn):
            out += ["", f"No connection-issue page was detected during Loading "
                        f"({len(conn)} checks, all negative)."]
        return self._title("LOADING") + out

    def _sec_post_loading(self):
        PR = "post_loading"
        out = []
        i, r = self._find("loading_percent | game reached main/popup", rng="loading")
        if r:
            self._claim(i)
            nxt, el = self._kv(r["msg"], "next_page"), self._kv(r["msg"], "elapsed")
            out.append(f"Loading ended after {self._fmt_logged(el)}.")
            out.append("")
            out.append("What was shown immediately before main screen:")
            if nxt == "popup_over_main":
                out.append("    An unidentified popup was covering the loaded main "
                           "game screen.")
                out.append("")
                out.append("The program established only that the main bottom bar was")
                out.append("visible behind it. The popup itself was never identified,")
                out.append("so it is not named here.")
            else:
                out.append(f"    {nxt or 'Not confidently identified.'}")

        backs = self._find("popup over main (bottom bar visible) — navigating back",
                           first=False, rng=PR)
        if backs:
            for i, _ in backs:
                self._claim(i)
            out += ["", "Action required:",
                    f"    {len(backs)} Back navigation" + ("s" if len(backs) > 1 else "") + "."]
        i, r = self._find("_back_to_main ── target app main confirmed", rng="setup_target_app")
        if r:
            self._claim(i)
            score = None
            for _, rr, page, px, tx, fin, thr, matched in self._page_events("setup_target_app"):
                if page == "target app main" and matched:
                    score = fin
            out += ["", "MAIN SCREEN REACHED", "",
                    f"Main screen was confirmed at {self._ts(r)}"
                    + (f" (final score {score:.3f})." if score is not None else ".")]
        if not out:
            return []
        return self._title("POST-LOADING CLEANUP") + out

    def _sec_prepare_target_app_complete(self):
        i, r = self._find("prepare_target_app | end | SETUP COMPLETE", rng="prepare_target_app")
        if not r:
            return []
        self._claim(i)
        el, cyc = self._kv(r["msg"], "elapsed"), self._kv(r["msg"], "cycle")
        return self._title("BEFORE_TARGET_APP COMPLETE") + [
            f"prepare_target_app completed successfully in {self._fmt_logged(el)}.",
            f"Setup cycles used: {cyc or '1'}",
        ]

    # ── tasks ─────────────────────────────────────────────────────────────────
    def _sec_tasks(self):
        if not self._task_ranges:
            return []
        out = []
        for key, lo, hi in self._task_ranges:
            rng = (lo, hi)
            self._claim(lo)
            head = self.records[lo]
            label = (self.task_defs.get(key) or {}).get("label", key)
            block = self._title(f"TASK — {label.upper()}")
            block.append(f"Started at {self._ts(head)}.")
            dur = self._task_duration(key, rng)
            renderer = self.renderers.get(key)
            if renderer:
                try:
                    block += renderer(self, key, rng)
                except Exception as exc:
                    block.append(f"(task detail unavailable: {exc!r})")
            block += self._generic_task_tail(key, rng, dur)
            out.append("\n".join(block))
        return ["\n\n".join(out)]

    def _task_duration(self, key, rng):
        """Seconds from the task header to its RESULT line, from real records."""
        lo, hi = self._window(rng)
        if lo >= hi:
            return None
        start = self.records[lo]
        _, end = self._find(f"── {key} ── RESULT:", rng=rng)
        if end is None:
            _, end = self._find("RUN COMPLETE", rng=rng)
        if start and end and start["ts"] and end["ts"]:
            return (end["ts"] - start["ts"]).total_seconds()
        return None

    def _generic_task_tail(self, key, rng=None, duration=None):
        o = []
        for i, r in self._find("restarting task", first=False, rng=rng):
            self._claim(i)
            o.append("")
            o.append(f"The task was RESTARTED: {r['msg'].split('── ')[-1].strip()}")
        i, r = self._find(f"── {key} ── RESULT:", rng=rng)
        if r:
            self._claim(i)
            res = r["msg"].split("RESULT:")[-1].strip()
            o += ["", "TASK COMPLETE", "", f"Result: {res}"]
            if duration is not None:
                o.append(f"Duration: about {self._fmt_dur(duration)}")
        hdr = (self.task_defs.get(key) or {}).get("header")
        if hdr:
            i, r = self._find(f"sent {hdr}:", rng=rng)
            if r:
                self._claim(i)
                o.append(f"Sheet status written: {hdr} = "
                         f"{r['msg'].split(':')[-1].strip()}")
        i, r = self._find("RUN COMPLETE", rng=rng)
        if r:
            self._claim(i)
            o.append(f"Worker recorded: {r['msg'].split('── ')[-1].strip()}")
        return o

    # ── guards / pause ────────────────────────────────────────────────────────
    def _sec_guards(self):
        # DELIBERATELY whole-run. A guard detection or recovery in an abandoned
        # earlier attempt is still part of this device's story, and the standing
        # rule is that a recovery is never hidden. The WORKER ATTEMPTS section
        # says which attempt stands, so nothing here is misattributed as the
        # terminal attempt's own narrative.
        out = []
        detected = self._find("DETECTED", first=False)
        for i, r in detected:
            self._claim(i)
            kind = "TargetAppGuard" if "[TARGET_APP-GUARD]" in r["msg"] else (
                "VpnGuard" if "[VPN-GUARD]" in r["msg"] else "A guard")
            what = r["msg"].split("DETECTED", 1)[-1].strip()
            out.append(f"{kind} detected: {what}")
        for needle in ("recovery attempt", "recovering", "reopening",
                       "restarting prepare_target_app", "escalat"):
            for i, r in self._find(needle, first=False):
                if r["level"] == "DEBUG":
                    continue
                self._claim(i)
                out.append(f"Recovery: {r['msg'].split('| ')[-1].strip()}")
        if not out:
            return []
        return self._title("GUARDS / RECOVERY") + out

    def _sec_pause(self):
        # DELIBERATELY whole-run: a host-internet pause is a lifecycle event and
        # can occur inside any attempt.
        out = []
        i, r = self._find("HOST INTERNET DOWN")
        if r:
            self._claim(i)
            out += [f"At {self._ts(r)} host internet was lost.",
                    "Device automation paused in place. The worker remained alive and",
                    "no task or device recovery was attempted while paused."]
        i, r = self._find("host internet RESTORED")
        if r:
            self._claim(i)
            el = self._kv(r["msg"], "elapsed")
            out += ["", f"Host internet was restored after {self._fmt_logged(el)}.",
                    "The worker resumed from its safe checkpoint."]
        i, r = self._find("manual stop while paused")
        if r:
            self._claim(i)
            out += ["", "The Run was manually stopped while waiting for host internet.",
                    "The worker exited from the pause gate without a normal resume."]
        if not out:
            return []
        return self._title("HOST-INTERNET PAUSE") + out

    # ── recording / counters / end ────────────────────────────────────────────
    def _sec_recording_final(self):
        """
        The TERMINAL attempt's recording result.

        Each relaunched worker runs its own recording lifecycle, so taking the
        first "recording enabled ->" and the first "recording stopped —" from
        the whole slice could describe attempt 1's folder, attempt 1's failure
        flags and segments from both attempts as if they were one session.
        """
        term = self._terminal_attempt()
        if not term:
            return []
        rng = (term["lo"], term["hi"])
        rec = self._attempt_recording(term)
        segs, stop = rec["segments"], rec["stop"]
        # Gate on ANY recording lifecycle evidence. Gating on valid segments or
        # a stop record dropped the whole section for the most important case:
        # recording enabled, the worker died before validating a single
        # segment, so there is neither. The report then showed "recording
        # started..." and nothing else, which reads as if nothing went wrong.
        if not rec["activity"]:
            return []
        out = []
        if rec["folder"]:
            out += [f"Folder: {rec['folder']}", ""]
        # Distinct index variables: the shared `i` used to leave the final
        # `_claim(i)` pointing at the last SEGMENT record instead of the
        # recording-stop record.
        for seg_i, r in segs:
            self._claim(seg_i)
            out.append(r["msg"].split("| ")[-1].strip())
        for bad_i, r in rec["bad"]:
            self._claim(bad_i)
            out.append(f"Problem: {r['msg'].split('| ')[-1].strip()}")
        if stop:
            stop_i = None
            for k in range(term["lo"], term["hi"]):
                if self.records[k] is stop:
                    stop_i = k
                    break
            self._claim(stop_i)
            msg = stop["msg"]
            valid = re.search(r"(\d+) valid segment", msg)
            nbad = re.search(r"(\d+) bad", msg)
            ev = re.search(r"(\d+) event", msg)
            dur = re.search(r"(\d+)s,", msg)
            failed, incomplete, merged = (rec["failed"], rec["incomplete"],
                                          rec["merged"])
            out += ["",
                    f"Valid segments: {valid.group(1) if valid else '?'}",
                    f"Bad segments:   {nbad.group(1) if nbad else '?'}",
                    f"Events:         {ev.group(1) if ev else '?'}",
                    f"Duration:       {self._fmt_dur(dur.group(1)) if dur else 'unknown'}",
                    f"failed={failed} incomplete={incomplete} merged={merged}"]
            if str(incomplete).lower() == "true":
                out += ["", "The recording is INCOMPLETE — some footage is missing.",
                        "The valid segments that were captured are still retained."]
            if str(failed).lower() == "true":
                out += ["", "The recording FAILED."]
            ff_i, ff = self._find("ffmpeg not available", rng=rng)
            if ff:
                self._claim(ff_i)
                # "This is not a recording failure." reads as a contradiction
                # three lines under "The recording FAILED." — it is about
                # ffmpeg, so say which condition it is separate from.
                if str(failed).lower() == "true":
                    out += ["",
                            "ffmpeg was also unavailable, so the valid segments "
                            "were kept separately.",
                            "The lack of ffmpeg was not the cause of the "
                            "recording failure."]
                elif str(incomplete).lower() == "true":
                    out += ["",
                            "ffmpeg was also unavailable, so the valid segments "
                            "were kept separately.",
                            "The lack of ffmpeg is separate from the "
                            "incomplete-recording condition."]
                else:
                    out += ["",
                            "ffmpeg was not available, so the valid segments were kept",
                            "separately. This is not a recording failure."]
            elif str(merged).lower() == "false" and str(failed).lower() == "false":
                out += ["", "The segments were not merged. This is not a recording failure."]
        if rec["unfinalized"]:
            nseg = len(segs)
            state = rec["fin_state"]
            # No leading blank when nothing was printed between the folder line
            # and this verdict — otherwise the section opens with a double gap.
            out += ([] if out and out[-1] == "" else [""])
            out += ["Recording did not produce a final stop summary."]
            if nseg:
                out += [f"{nseg} validated segment(s) were saved and are "
                        f"retained."]
            else:
                out += ["No validated segment is confirmed."]
            if state == "interrupted_by_worker_exit":
                out += ["",
                        "Because the worker exited before recording "
                        "finalisation, the final",
                        "failed / incomplete / merged status and the overall "
                        "completeness of this",
                        "recording cannot be confirmed from the log. This is "
                        "NOT a successful",
                        "recording, and it is not a confirmed failure either."]
            elif state == "finalization_error":
                # The worker DID reach [WORKER-END]. Saying it exited early
                # would contradict WORKER FINISHED in the same report.
                out += ["",
                        "The worker itself completed, but recording "
                        "finalisation failed before a",
                        "final recording summary could be written:"]
                for _i, _r in rec["fin_err"]:
                    self._claim(_i)
                    out.append(f"    {_r['msg'].split('] ')[-1].strip()}")
                out += ["",
                        "The final failed / incomplete / merged state and the "
                        "overall completeness",
                        "cannot be confirmed from the final recording summary. "
                        "This is NOT a",
                        "successful recording, and it is not a confirmed "
                        "failure either."]
            else:
                out += ["",
                        "The worker completed, but no final recording stop "
                        "summary was logged.",
                        "The exact final recording status cannot be confirmed "
                        "from the available",
                        "recording evidence. No reason for the missing summary "
                        "appears in the log."]
        if len(self._attempts) > 1:
            out += ["",
                    f"This is worker attempt {len(self._attempts)}'s recording. "
                    f"Earlier attempts recorded separately — see WORKER ATTEMPTS."]
        return self._title("RECORDING FINAL RESULT") + out

    _COUNTER_LABELS = (
        ("self_closed", "Device self-closed"),
        ("prog_reopen", "Program device reopen"),
        ("vpn_install", "ProtonVPN install"),
        ("connect", "VPN Connect"),
        ("chg_srv", "Change Server"),
        ("open_target_app", "TargetApp open"),
    )

    def _sec_counters(self):
        """
        The TERMINAL attempt's own pre-wipe counters.

        Not the first snapshot in the slice (that is an abandoned attempt's) and
        not the controller's later all-zero reset.
        """
        term = self._terminal_attempt()
        if not term:
            return []
        vals, idx, source = self._attempt_counters(term)
        n = len(self._attempts)
        if vals is not None and source == "ambiguous":
            # A snapshot exists but the log proves nothing about its author:
            # no [WORKER-END] after it and no controller cleanup boundary.
            shown = [f"    {lbl + ':':26s}{vals[k]}"
                     for k, lbl in self._COUNTER_LABELS if k in vals]
            return self._title("FINAL COUNTERS") + [
                "Counter ownership could not be confirmed for this attempt.",
                "",
                "A counter snapshot exists, but this attempt has no "
                "[WORKER-END] record and",
                "no controller cleanup boundary, so the log does not say "
                "whether the worker",
                "or the controller's own cleanup wrote it:",
                ""] + shown + [
                "",
                "It is therefore NOT reported as the worker's final counters. "
                "This is an",
                "older log written before the controller marked its cleanup "
                "boundary."]
        if vals is None:
            out = ["No confirmed final counter snapshot for the terminal worker."]
            # Only cite a boundary that this log actually contains.
            _end_i, _ctrl_i = self._attempt_boundaries(term)
            if term["end"] is not None:
                out += ["", "It wrote no counter snapshot before it finished."]
            elif _ctrl_i is not None:
                out += ["",
                        "It exited without writing a [WORKER-END] record, and no "
                        "counter snapshot",
                        "appears before the controller's cleanup boundary."]
            else:
                out += ["",
                        "It exited without writing a [WORKER-END] record, and "
                        "this attempt logged",
                        "no counter snapshot at all."]
            creset, _ci = self._attempt_controller_reset(term)
            if creset:
                shown = [f"    {lbl + ':':26s}{creset[k]}"
                         for k, lbl in self._COUNTER_LABELS if k in creset]
                out += ["",
                        "A counter line DOES appear after the controller cleanup "
                        "boundary. It was",
                        "written by the controller's own "
                        "reset_device_finished_state(), not by the",
                        "worker:",
                        ""] + shown + [
                        "",
                        "Those cleanup values are controller-side state and are "
                        "not reported as",
                        "the worker's final counters."]
            # Only claim earlier counters exist if they actually do. An earlier
            # attempt that also died wrote none, and saying otherwise sends the
            # reader to a WORKER ATTEMPTS section that has nothing to show.
            if n > 1 and any(self._attempt_counters(a)[2] in
                             ("worker_end", "pre_controller")
                             for a in self._attempts[:-1]):
                out += ["",
                        "Earlier attempt(s) did record counters — those values are "
                        "under WORKER",
                        "ATTEMPTS. They describe a DIFFERENT worker process and "
                        "are not this",
                        "attempt's state."]
            elif n > 1:
                out += ["",
                        "No earlier attempt recorded confirmed counters either."]
            return self._title("FINAL COUNTERS") + out
        out = []
        if source == "pre_controller":
            out += ["The terminal worker wrote no [WORKER-END] record, so this "
                    "is not a normal",
                    "completion. These values come from the counter snapshot it "
                    "emitted before",
                    "the controller's cleanup boundary — worker-side, but not "
                    "proof that the",
                    "worker finished its own shutdown.", ""]
        for key, label in self._COUNTER_LABELS:
            if key in vals:
                out.append(f"{label + ':':26s}{vals[key]}")
        used = {k: int(v.split("/")[0]) for k, v in vals.items()}
        meaning = []
        meaning.append("No emulator crash." if not used.get("self_closed")
                       else f"Emulator self-closed {used['self_closed']} time(s).")
        meaning.append("No device reopen." if not used.get("prog_reopen")
                       else f"Device was reopened {used['prog_reopen']} time(s).")
        meaning.append("No ProtonVPN reinstall." if not used.get("vpn_install")
                       else f"ProtonVPN was installed {used['vpn_install']} time(s).")
        meaning.append("One normal VPN Connect click." if used.get("connect") == 1
                       else f"{used.get('connect', 0)} VPN Connect click(s).")
        meaning.append("No Change Server recovery." if not used.get("chg_srv")
                       else f"Change Server used {used['chg_srv']} time(s).")
        meaning.append("One normal TargetApp launch." if used.get("open_target_app") == 1
                       else f"{used.get('open_target_app', 0)} TargetApp launch(es).")
        out += [""] + meaning
        if n > 1:
            out += ["",
                    f"These are worker attempt {n}'s counters. Each worker "
                    f"process keeps its own; earlier attempts' snapshots are "
                    f"under WORKER ATTEMPTS."]
        # a snapshot AFTER a proven boundary is the controller's own cleanup
        creset, _ci = self._attempt_controller_reset(term)
        if creset:
            out += ["",
                    "Worker state was cleared. The controller then performed its "
                    "additional",
                    "defensive finished-state reset; the snapshot it logged is "
                    "controller-side",
                    "cleanup state, not this attempt's final counter state."]
        return self._title("FINAL COUNTERS") + out

    def _sec_worker_finished(self):
        """
        The TERMINAL attempt's own result — never an earlier one, and never
        fabricated when the terminal worker died without writing WORKER-END.
        """
        term = self._terminal_attempt()
        if not term:
            return []
        n = len(self._attempts)
        if term["end"] is None:
            out = ["The terminal worker did not write a WORKER-END record.", "",
                   "No final worker timestamp, duration or ok/result tuple is",
                   "available from the worker itself — it exited without one",
                   "(killed, crashed, or terminated by the controller).", "",
                   "What the CONTROLLER recorded is in CONTROLLER COMPLETION."]
            if n > 1 and any(a["end"] is not None for a in self._attempts[:-1]):
                out += ["", "Earlier attempt(s) that DID finish normally are "
                            "listed under WORKER ATTEMPTS."]
            elif n > 1:
                out += ["", "No earlier attempt wrote one either — see WORKER "
                            "ATTEMPTS."]
            return self._title("WORKER FINISHED") + out
        end = term["end"]
        for i in range(term["lo"], term["hi"]):
            if self.records[i] is end:
                self._claim(i)
                break
        out = [f"The worker finished at {self._ts(end)}"
               + (f" (attempt {n} of {n})." if n > 1 else ".")]
        out.append(f"Reported: ok={term['ok']} result={term['result']}")
        if n > 1:
            out.append("")
            out.append("This is the terminal attempt's result. Earlier attempts "
                       "are listed under WORKER ATTEMPTS.")
        return self._title("WORKER FINISHED") + out

    def _sec_attempts(self):
        """
        One line per worker attempt. Only rendered when there was more than one,
        so a failed earlier attempt is preserved rather than erased — while the
        terminal sections above still describe the attempt that actually ran.

        An attempt with no [WORKER-END] is NOT "still running" once the
        controller has finalized the device: the header would then say
        "FAILED — WORKER DIED" while this section claimed the same attempt was
        still going. For the terminal attempt the controller's own verdict is
        the authority, and it is named as the source.
        """
        if len(self._attempts) < 2:
            return []
        term_result = (getattr(self.ctx, "final_result", "") or "").strip()
        out = []
        for j, a in enumerate(self._attempts, 1):
            is_terminal = (j == len(self._attempts))
            dur = None
            if a["start"] and a["end"] and a["start"]["ts"] and a["end"]["ts"]:
                dur = (a["end"]["ts"] - a["start"]["ts"]).total_seconds()
            if a["end"] is not None:
                verdict = f"ok={a['ok']} result={a['result']}"
            elif is_terminal and term_result:
                verdict = ("no [WORKER-END] record — the controller finalized "
                           f"this attempt as {term_result}")
            elif is_terminal:
                verdict = ("no [WORKER-END] record and no controller verdict "
                           "for this attempt")
            else:
                verdict = ("no [WORKER-END] record — abandoned when the worker "
                           "was relaunched")
            out.append(f"Attempt {j}: started {self._ts(a['start'])}"
                       + (f", ended {self._ts(a['end'])}" if a["end"] else "")
                       + (f", {self._fmt_dur(dur)}" if dur is not None else ""))
            out.append(f"    {verdict}")
            vals, _, csrc = self._attempt_counters(a)
            if vals and csrc == "ambiguous":
                out.append("    Final counters: present but unattributable "
                           "(no [WORKER-END], no cleanup boundary)")
            elif vals:
                shown = [f"{lbl}: {vals[k]}" for k, lbl in self._COUNTER_LABELS
                         if k in vals]
                out.append(f"    Final counters: {', '.join(shown)}"
                           + ("  (pre-cleanup snapshot; no [WORKER-END])"
                              if csrc == "pre_controller" else ""))
            elif a["end"] is None:
                out.append("    Final counters: none confirmed for this attempt "
                           "(no [WORKER-END] boundary)")
            rec = self._attempt_recording(a)
            if rec["stop"] or rec["folder"]:
                state = {"interrupted_by_worker_exit":
                         "never finalized (worker exited)",
                         "finalization_error":
                         "never finalized (finalisation failed)",
                         "missing_summary_after_worker_completion":
                         "never finalized (no stop summary logged)",
                         }.get(rec["fin_state"], "no stop record")
                if rec["stop"]:
                    if str(rec["failed"]).lower() == "true":
                        state = "FAILED"
                    elif str(rec["incomplete"]).lower() == "true":
                        state = "incomplete"
                    else:
                        state = "successful"
                out.append(f"    Recording: {state}"
                           + (f" — {rec['folder']}" if rec["folder"] else ""))
        out += ["",
                "The narrative sections above describe the terminal attempt.",
                "Earlier attempts' partial phase data are kept separate."]
        return self._title("WORKER ATTEMPTS") + out

    def _sec_controller(self):
        c = self.ctx
        out = []
        if c.final_result:
            out += ["Worker result:", f"    {c.final_result}"]
        # The DISPOSITION is authoritative — it names the controller action, so
        # one code can never stand in for three different causes. close_ok is
        # only consulted for older contexts that predate the field.
        _disp = getattr(c, "close_disposition", "")
        if not _disp and c.close_ok is not None:
            _disp = ("attempted_success" if c.close_ok is True
                     else "attempted_failed")
        _NOT_REQUESTED = {
            "not_requested_stop_all":
                "NOT REQUESTED — Stop All leaves emulator windows open.",
            "not_requested_safe_reset":
                "NOT REQUESTED — Safe Reset leaves emulator windows open.",
            "not_requested_controller_close":
                "NOT REQUESTED — controller shutdown leaves emulator windows "
                "open.",
            "not_applicable_never_launched":
                "NOT APPLICABLE — no emulator window was opened by this run.",
        }
        if _disp == "attempted_success":
            out += ["", "Emulator close:", "    SUCCESS"]
        elif _disp == "attempted_failed":
            out += ["", "Emulator close:", "    FAILED", "",
                    "The emulator window did NOT close. A zombie BlueStacks process",
                    "may still be running for this device."]
        elif _disp == "attempted_unverified":
            # Neither "SUCCESS" nor "a zombie remains" is proven.
            out += ["", "Emulator close:", "    UNVERIFIED", "",
                    "The controller attempted to close the emulator, but could "
                    "not confirm",
                    "whether the window actually closed."]
        elif _disp in _NOT_REQUESTED:
            out += ["", "Emulator close:", f"    {_NOT_REQUESTED[_disp]}"]
        # A route that requested no close does not erase what this Run already
        # learned about the window on an earlier attempt.
        _prior = getattr(c, "prior_close_result", "no_attempt")
        if _disp in _NOT_REQUESTED and _prior != "no_attempt":
            if _prior is False:
                out += ["",
                        "An EARLIER close attempt in this Run FAILED. A zombie "
                        "BlueStacks process",
                        "may still be running for this device."]
            elif _prior is None:
                out += ["",
                        "An earlier close attempt in this Run could not be "
                        "verified, so whether",
                        "the window is open is unknown."]
            else:
                out += ["",
                        "An earlier close attempt in this Run succeeded."]
        if c.retry_count:
            out += ["", f"ADB retries used: {c.retry_count}"]
        if c.final_badge:
            out += ["", f"Final status badge: {c.final_badge}"]
        for n in c.notes:
            out += ["", n]
        if not out:
            return []
        return self._title("CONTROLLER COMPLETION") + out

    def _sec_problems(self):
        """
        Every WARNING / ERROR / CRITICAL in this slice, plus INFO-level failure
        and control markers. Nothing here may be dropped: a report that loses
        evidence is worse than one that shows a technical line.
        """
        groups = {}
        order = []
        for i, r in enumerate(self.records):
            severe = r["level"] in self._SEVERE
            low = r["msg"].lower()
            marked = (r["level"] == "INFO"
                      and any(m.lower() in low for m in self._INFO_MARKERS)
                      and not any(x.lower() in low for x in self._INFO_MARKER_EXCLUDE))
            if not (severe or marked):
                continue
            if marked and not severe and i in self._claimed:
                continue          # already narrated in its own section
            # EXACT message. Normalising digits merged "attempt 1/3" with
            # "attempt 2/3" and silently destroyed evidence. Only byte-identical
            # severe messages may share an entry.
            key = (r["level"], r["msg"], tuple(r["cont"]))
            if key not in groups:
                groups[key] = {"n": 0, "sample": r}
                order.append(key)
            groups[key]["n"] += 1
        if not order:
            return []
        out = []
        for key in order:
            g = groups[key]
            lvl = key[0]
            msg = g["sample"]["msg"]
            times = f" (×{g['n']})" if g["n"] > 1 else ""
            out.append(f"[{lvl}]{times} {self._ts(g['sample'])}")
            out.append(f"    {msg}")
            for c in g["sample"]["cont"]:
                out.append(f"    {c}")
            out.append("")
        return self._title("WARNINGS / ERRORS") + out

    # ── recovery evidence ─────────────────────────────────────────────────────
    _RECOVERY_EVIDENCE = (
        "restarting task", "full_restart", "guarded wait interrupted",
        "restart_prepare_target_app", "restarting prepare_target_app", "setup cycle begin  attempt=2",
        "setup cycle begin  attempt=3", "recovery attempt", "recovery failed",
        "recovering", "self-close", "self_closed recovery", "reopening",
        "device reopen", "reinstall", "Change Server", "change-server",
        "chg_srv recovery",
        "escalat", "DETECTED", "guard recovery", "HOST INTERNET DOWN",
        "host internet RESTORED", "internet_killed", "re-queuing",
        "Device not responding after launch", "adb_connect_failed",
        "force-stopping ProtonVPN + TargetApp before retry",
    )

    def _run_had_recovery_or_restart(self):
        """
        The ONE test for "did this run need help?".

        Source-grounded: real markers from the raw slice plus controller
        evidence. Used by BOTH the Overall verdict and the "no guard recovery or
        task restart was needed" bullet, so those two can never disagree.
        Returns (bool, [reasons]).
        """
        reasons = []
        for needle in self._RECOVERY_EVIDENCE:
            hits = self._find(needle, first=False)
            for _, r in hits:
                if r["level"] == "DEBUG":
                    continue
                reasons.append(needle)
                break
        # prepare_target_app needed more than one cycle
        _, r = self._find("prepare_target_app | end | SETUP COMPLETE")
        if r:
            try:
                if int(self._kv(r["msg"], "cycle") or 1) > 1:
                    reasons.append("prepare_target_app cycle > 1")
            except Exception:
                pass
        # A counter that actually moved for a recovery action.
        # Only WORKER-OWNED snapshots count (see _attempt_counters): the
        # controller's own reset_device_finished_state() line is all zeros and
        # is not this worker's evidence. Every attempt is considered, because a
        # recovery during an abandoned attempt still means the run needed help.
        # Ambiguous snapshots ARE counted here on purpose. Recovery asks "did a
        # counter ever move", not "who logged it" — and a non-zero value proves
        # the action happened whichever process recorded it. Ownership only
        # matters for reporting a worker's FINAL counters, which this is not.
        vals = {}
        for _a in self._attempts:
            _v, _, _ = self._attempt_counters(_a)
            for _k, _pair in (_v or {}).items():
                _n = _pair.split("/")[0]
                try:
                    if int(_n) > int(vals.get(_k, "0")):
                        vals[_k] = _n
                except Exception:
                    pass
        if vals:
            for k, label in (("self_closed", "device self-close recovery"),
                             ("prog_reopen", "program device reopen"),
                             ("vpn_install", "ProtonVPN reinstall"),
                             ("chg_srv", "Change Server recovery")):
                try:
                    if int(vals.get(k, 0)) > 0:
                        reasons.append(label)
                except Exception:
                    pass
            for k, label, normal in (("connect", "extra VPN Connect attempts", 1),
                                     ("open_target_app", "extra TargetApp launches", 1)):
                try:
                    if int(vals.get(k, 0)) > normal:
                        reasons.append(label)
                except Exception:
                    pass
        # More than one launch attempt in this Run session.
        # The PARSED raw records are sufficient proof on their own: two
        # `device_worker started` lines mean the worker really was relaunched,
        # whether or not the controller context happened to record both. Reading
        # ctx.attempts alone let one report say "the worker was relaunched"
        # in WORKER ATTEMPTS and "no guard recovery or task restart was needed"
        # in the summary. Both sources are consulted, but they contribute the
        # single reason below so the wording never double-counts one relaunch.
        if (len(self._attempts) > 1
                or len(getattr(self.ctx, "attempts", []) or []) > 1):
            reasons.append("worker relaunched")
        if getattr(self.ctx, "retry_count", 0):
            reasons.append("ADB retry")
        return bool(reasons), sorted(set(reasons))

    def _had_host_pause(self):
        return bool(self._find("HOST INTERNET DOWN")[1])

    # ── summary ───────────────────────────────────────────────────────────────
    def _sec_summary(self):
        c = self.ctx
        out = ["Device:", f"    {c.friendly_name} ({c.adb_id})", "",
               "Task:", f"    {self._task_label()}", "",
               "Result:", f"    {self._final_label()}"]
        _wa, _wb, _wspan, _wactive, _wterm = self._worker_times()
        if _wspan is not None:
            _n = len(self._attempts)
            out += ["", "Worker runtime:",
                    f"    {self._fmt_dur(_wspan)}"
                    + (f"  (lifecycle span across {_n} attempts)" if _n > 1 else "")]
            if _n > 1 and _wactive is not None and abs(_wactive - _wspan) >= 1:
                out += [f"    {self._fmt_dur(_wactive)} active across the attempts"]
        elif self._attempts:
            out += ["", "Worker runtime:",
                    "    unavailable — the terminal worker did not record an end"]
        elif self._launch_state() == "no_worker_mark":
            # "never launched" here would contradict "Launch attempts: 1" in
            # the header of the same report.
            out += ["", "Worker runtime:",
                    "    unavailable — the process started but wrote no worker "
                    "log"]
        elif self._launch_state() == "never_launched":
            # Controller cleanup records in the slice must not suppress this.
            out += ["", "Worker runtime:", "    n/a — the worker never launched"]
        # Phase durations come from the TERMINAL attempt's own phase windows.
        for needle, label, _rng in (
                ("prepare_target_app | end | SETUP COMPLETE", "prepare_target_app", "prepare_target_app"),
                ("| setup_device | end |", "Device setup", "setup_device"),
                ("| setup_vpn | end |", "VPN setup", "setup_vpn"),
                ("| setup_target_app | end |", "TargetApp setup", "setup_target_app")):
            _, r = self._find(needle, rng=_rng)
            if r:
                el = self._kv(r["msg"], "elapsed")
                if el:
                    out += ["", f"{label}:", f"    {self._fmt_logged(el)}"]
        for key, lo, hi in self._task_ranges:
            d = self._task_duration(key, (lo, hi))
            if d is not None:
                label = (self.task_defs.get(key) or {}).get("label", key)
                out += ["", f"{label}:", f"    about {self._fmt_dur(d)}"]
        bullets = self._bullets()
        if bullets:
            out += ["", "Important decisions/fallbacks:", ""]
            out += [f"    • {b}" for b in bullets]
        out += ["", "Overall:", f"    {self._overall()}"]
        return self._title("FINAL SUMMARY") + out

    def _bullets(self):
        """
        Final-summary bullets.

        EVERY claim about a phase is scoped to that phase's window. The popup
        bullet in particular used a whole-run search while its Back count was
        scoped to post-loading, so a task-time "popup over main" produced
        "An unidentified popup covered the loaded main screen. 0 Back actions
        removed it." with no popup in post-loading at all.

        Whole-run lookups below are deliberate: recording, ffmpeg and the
        recovery test are lifecycle facts, not phase facts.
        """
        b = []
        T = "terminal_attempt" if self._terminal else None
        if self._find("NOT in adb devices", rng=T)[1]:
            b.append("Device was not present in ADB, so BlueStacks was launched.")
        _, r = self._find("ADB connected on attempt", rng=T)
        if r and "attempt 1" in r["msg"]:
            b.append("ADB connected on the first attempt.")
        elif r:
            n = re.search(r"attempt (\d+)", r["msg"])
            b.append(f"ADB connected on attempt {n.group(1) if n else '?'}.")
        if len(self._attempts) > 1:
            b.append(f"The worker was relaunched — {len(self._attempts)} attempts "
                     f"in total; the terminal one is described above.")
        if self._find("[DISPLAY-PREFLIGHT]", "DISAGREES", rng="setup_device")[1]:
            b.append("Live display passed despite misleading config hints.")
        if self._find("[VPN-UI] state=", "fallback", rng="setup_vpn")[1]:
            b.append("ProtonVPN Connect bounds were missing.")
            b.append("Fallback Connect coordinate was used successfully.")
        _, r = self._find("stage2_connect | clicking Connect", rng="setup_vpn")
        if r and (self._kv(r["msg"], "attempt") or "").startswith("1/"):
            b.append("VPN came UP on the first Connect attempt.")
        prog = self._find("loading_percent | progress", first=False, rng="loading")
        if prog and any("100" in (self._kv_wide(r["msg"], "percent") or "")
                        for _, r in prog):
            b.append("Loading progressed to 100%.")
        # Post-loading popup: evidence AND count both scoped to post-loading.
        if self._find("popup over main", rng="post_loading")[1]:
            b.append("An unidentified popup covered the loaded main screen.")
            n = len(self._find("navigating back", first=False, rng="post_loading"))
            if n:
                b.append(f"{n} Back action{'s' if n != 1 else ''} removed it.")
        if self._find("target app main confirmed", rng="setup_target_app")[1]:
            b.append("Main screen was confirmed.")
        for key, lo, hi in self._task_ranges:
            rng = (lo, hi)
            for _, r, page, px, tx, fin, thr, matched in self._page_events(rng):
                if matched and page == "vip":
                    b.append("VIP page matched.")
                    break
            _, r = self._find("OCR pass1 raw=", rng=rng)
            if r:
                raw = re.search(r"raw='([^']*)'", r["msg"])
                b.append(f'OCR read "{raw.group(1) if raw else "?"}" on pass 1.')
            if self._find("no click needed", rng=rng)[1]:
                b.append("VIP was already collected — no reward click was sent.")
            elif self._find("OCR inconclusive; clicking anyway", rng=rng)[1]:
                b.append("Both OCR passes were inconclusive; the programmed "
                         "fallback click was sent.")
            elif self._find("'Free' detected — collecting", rng=rng)[1]:
                b.append("Collection action completed.")
        # Whole-run by design. Skipped entirely when no worker ever ran — a
        # "no recovery was needed" bullet implies something ran that could have
        # needed one.
        _state = self._launch_state()
        if _state == "ran":
            recovered, why = self._run_had_recovery_or_restart()
            if recovered:
                b.append("Recovery or restart was required: " + ", ".join(why) + ".")
            else:
                # "was needed" is a claim that recovery would not have helped.
                # Only a successful run supports it. When the run failed, the
                # absence of recovery records proves only that none was
                # RECORDED before it failed — it may well have been needed.
                _r = (self.ctx.final_result or "").lower()
                if self.ctx.final_ok:
                    b.append("No guard recovery or task restart was needed.")
                elif _r in ("stopped", "stopped_before_launch",
                            "stopped_by_safe_reset", "stopped_by_fatal_run",
                            "stopped_by_controller_close"):
                    b.append("No guard recovery or task restart was recorded "
                             "before the run was stopped.")
                else:
                    b.append("No guard recovery or task restart was recorded "
                             "before the failure.")
        elif _state == "no_worker_mark":
            b.append("The controller launched the worker process, but it exited "
                     "before writing any worker log.")
        else:
            b.append("No worker ran, so there was nothing to recover.")
        # close_ok is tri-state: None means no close result was recorded, which
        # is not a failure. Only an explicit False earns the bullet.
        _cdisp = getattr(self.ctx, "close_disposition", "")
        if _cdisp == "attempted_failed" or (not _cdisp
                                            and self.ctx.close_ok is False):
            b.append("Emulator close failed — a zombie BlueStacks process may "
                     "still be running.")
        elif _cdisp == "attempted_unverified":
            b.append("Emulator close could not be verified — the window may or "
                     "may not have closed.")
        else:
            _pc = getattr(self.ctx, "prior_close_result", "no_attempt")
            if _pc is False:
                b.append("An earlier emulator close in this Run failed — a "
                         "zombie process may still be running.")
            elif _pc is None:
                b.append("An earlier emulator close in this Run could not be "
                         "verified.")
        # Recording bullets describe the TERMINAL attempt only.
        _term = self._terminal_attempt()
        _rrng = (_term["lo"], _term["hi"]) if _term else None
        _, r = self._find("recording stopped —", rng=_rrng)
        if r:
            v = re.search(r"(\d+) valid segment", r["msg"])
            _f = self._kv(r["msg"], "failed")
            _inc = self._kv(r["msg"], "incomplete")
            b.append(f"Recording produced {v.group(1) if v else '?'} valid segment(s)"
                     + (" — but the recording FAILED." if str(_f).lower() == "true"
                        else (" — the recording is incomplete."
                              if str(_inc).lower() == "true" else ".")))
        elif _term is not None:
            # Recording activity with no stop summary. Silence here read as
            # "no recording", which is the opposite of what happened.
            _rec = self._attempt_recording(_term)
            if _rec["unfinalized"]:
                _n = len(_rec["segments"])
                _st = _rec["fin_state"]
                # Same source-aware classification as RECORDING FINAL RESULT.
                # "before the worker exited" may only be said when this attempt
                # really has no [WORKER-END].
                if _st == "interrupted_by_worker_exit":
                    _why = "before the worker exited"
                elif _st == "finalization_error":
                    _why = "— the worker completed, but recording finalisation failed"
                else:
                    _why = "— the worker completed, but no stop summary was logged"
                b.append(f"Recording saved {_n} validated segment(s), but did "
                         f"not finalize {_why}."
                         if _n else
                         f"Recording started but did not produce a final stop "
                         f"summary {_why}; no validated segment is confirmed.")
        if self._find("ffmpeg not available", rng=_rrng)[1]:
            b.append("ffmpeg was unavailable, so segments were not merged.")
        if len(self._attempts) > 1:
            _earlier = [a for a in self._attempts[:-1]
                        if self._attempt_recording(a)["stop"]]
            if _earlier:
                b.append(f"{len(_earlier)} earlier attempt(s) also recorded — "
                         f"see WORKER ATTEMPTS.")
        return b

    def _overall(self):
        c = self.ctx
        if c.task_action == "invalid":
            return "NOT RUN — INVALID TASK CONFIGURATION."
        if c.task_action == "retry_skipped" or (c.final_result or "") == "retry_skipped":
            return {
                "no_task_config": "NOT RUN — NO TASK CONFIG FOR THIS DEVICETYPE.",
                "empty_task_list": "NOT RUN — TASK CONFIG IS EMPTY.",
                "all_tasks_done": "NOT RUN — ALL CONFIGURED TASKS WERE ALREADY DONE.",
            }.get(getattr(c, "retry_skip_reason", ""),
                  "NOT RUN — RETRY MODE FOUND NOTHING PENDING.")
        if (c.final_result or "") == "stopped_before_launch":
            return "STOPPED BEFORE THE WORKER LAUNCHED."
        # A failed or stopped run keeps its primary verdict, but a zombie
        # emulator is an operational problem the reader must not miss.
        _cd = getattr(c, "close_disposition", "")
        _cq = ""
        if _cd == "attempted_failed" or (not _cd and c.close_ok is False):
            _cq = " — EMULATOR CLOSE ALSO FAILED"
        elif _cd == "attempted_unverified":
            _cq = " — EMULATOR CLOSE UNVERIFIED"
        else:
            _pcr = getattr(c, "prior_close_result", "no_attempt")
            if _pcr is False:
                _cq = " — EARLIER EMULATOR CLOSE FAILED"
            elif _pcr is None:
                _cq = " — EARLIER EMULATOR CLOSE UNVERIFIED"
        if c.task_action == "skip":
            return "SKIPPED — NO TASKS AND skip_before WAS ON."
        r = (c.final_result or "").lower()
        if r == "stopped_by_safe_reset":
            return f"STOPPED BY THE SAFE DAILY RESET{_cq}."
        if r == "stopped_by_fatal_run":
            # Deliberately not "STOPPED MANUALLY": nobody pressed Stop.
            return (f"STOPPED — THE RUN WAS ABORTED BY A FATAL ERROR ON "
                    f"ANOTHER DEVICE{_cq}.")
        if r == "stopped_by_controller_close":
            return f"STOPPED — THE CONTROLLER WINDOW WAS CLOSED{_cq}."
        if r == "stopped":
            if self._find("manual stop while paused")[1]:
                return f"STOPPED MANUALLY WHILE WAITING FOR HOST INTERNET{_cq}."
            return f"STOPPED MANUALLY{_cq}."
        if not c.final_ok:
            if r == "adb_connect_failed":
                return f"FAILED — ADB CONNECTION EXHAUSTED{_cq}."
            if r == "cfg_build_failed":
                return "FAILED — WORKER CONFIG COULD NOT BE BUILT."
            if r == "proc_start_failed":
                return "FAILED — WORKER PROCESS DID NOT START."
            if r == "retry_schedule_failed":
                # Without this the raw result string leaked into Overall as
                # "FAILED — RETRY_SCHEDULE_FAILED".
                return f"FAILED — THE ADB RETRY COULD NOT BE SCHEDULED{_cq}."
            # Terminal attempt only: an abandoned earlier attempt's VPN failure
            # does not describe how THIS run ended.
            if self._find("| setup_vpn | end |", "signal=failed",
                          rng="setup_vpn")[1]:
                return f"FAILED DURING VPN SETUP{_cq}."
            return (f"FAILED — {r.upper()}{_cq}." if r else f"FAILED{_cq}.")
        # Recording is auxiliary: a recording problem never turns a successful
        # device/task run into a failure. But it must not vanish from Overall
        # either — the report could say "The recording FAILED." and then
        # "CLEAN SUCCESSFUL RUN." three lines later.
        # Auxiliary outcomes, in report order. Each is independent: a recording
        # problem and a failed emulator close are different facts and neither
        # may erase the other.
        _quals = [q for q in (self._recording_qualifier(),
                              self._close_qualifier()) if q]
        _suffix = "; ".join(_quals)
        recovered, _why = self._run_had_recovery_or_restart()
        if recovered:
            _base = ("SUCCESSFUL AFTER HOST-INTERNET PAUSE"
                     if self._had_host_pause() else "SUCCESSFUL AFTER RECOVERY")
            return f"{_base} — {_suffix}." if _suffix else f"{_base}."
        if _suffix:
            # "CLEAN" is a claim about the whole run, so it cannot survive an
            # auxiliary problem. The core result is still a successful run.
            return f"SUCCESSFUL RUN — {_suffix}."
        return "CLEAN SUCCESSFUL RUN."

    def _close_qualifier(self):
        """
        Emulator-close health as an Overall suffix, or "".

        Only a close that was actually attempted and reported failure counts.
        close_ok=None is not a failure — it means no close result was recorded,
        which for Stop All and never-launched devices is the correct outcome.
        """
        _d = getattr(self.ctx, "close_disposition", "")
        if _d == "attempted_failed" or (not _d and self.ctx.close_ok is False):
            return "EMULATOR CLOSE FAILED"
        if _d == "attempted_unverified":
            return "EMULATOR CLOSE UNVERIFIED"
        # A known-bad window from an earlier attempt is still a known-bad
        # window, even when the terminal route deliberately closed nothing.
        _p = getattr(self.ctx, "prior_close_result", "no_attempt")
        if _p is False:
            return "EARLIER EMULATOR CLOSE FAILED"
        if _p is None and _p != "no_attempt":
            return "EARLIER EMULATOR CLOSE UNVERIFIED"
        return ""

    def _recording_qualifier(self):
        """
        The TERMINAL attempt's recording health, as an Overall suffix, or "".

        A cleanly finalized recording and a run with no recording at all both
        return "" — neither is worth qualifying a verdict with.
        """
        term = self._terminal_attempt()
        if not term:
            return ""
        rec = self._attempt_recording(term)
        if not rec["activity"]:
            return ""
        if rec["stop"]:
            if str(rec["failed"]).lower() == "true":
                return "RECORDING FAILED"
            if str(rec["incomplete"]).lower() == "true":
                return "RECORDING INCOMPLETE"
            return ""
        return "RECORDING DID NOT FINALIZE"

    # ── output ────────────────────────────────────────────────────────────────
    def write(self, logs_dir) -> str:
        c = self.ctx
        safe = re.sub(r"[^A-Za-z0-9_.-]", "_", c.adb_id)
        folder = os.path.join(logs_dir, HUMAN_LOG_DIRNAME, safe)
        os.makedirs(folder, exist_ok=True)
        stamp = c.started_at.strftime("%Y%m%d-%H%M%S")
        base = f"run_{stamp}_session_{c.session_id}"
        # .txt, never .log — existing raw-log globbing must not pick these up.
        path = os.path.join(folder, base + ".txt")
        n = 1
        while os.path.exists(path):          # never overwrite an older report
            path = os.path.join(folder, f"{base}_{n}.txt")
            n += 1
        body = self.build()
        tmp = path + ".part"
        with open(tmp, "w", encoding="utf-8") as fh:
            fh.write(body)
        os.replace(tmp, path)
        return path


def _human_render_vip_collect(gen, key, rng=None):
    """
    Task-specific enrichment for VIP Collect.

    The narrative follows the BOT's real contract, which is deliberately
    asymmetric:
        sold_out              -> no reward click, returns done
        free                  -> one reward click
        unknown after pass 2  -> one reward click ANYWAY ("a wasted click on a
                                 Sold Out button is harmless")
    Only SOLD OUT may ever be described as "no reward click".
    """
    o = []
    i, r = gen._find("── vip_collect ── starting pass", rng=rng)
    if r:
        gen._claim(i)
        o += ["", "TASK ENTRY CHECKS", "",
              "The task confirmed it was on the main screen before navigating."]
    i, r = gen._find("── vip_collect ── clicking 'vip' on main screen", rng=rng)
    if r:
        gen._claim(i)
        rect = re.search(r"rect=(\([^)]*\))", r["msg"])
        o += ["", f"The VIP entry was clicked on the main screen"
                  + (f" at {rect.group(1)}." if rect else ".")]
    for _, rr, page, px, tx, fin, thr, matched in gen._page_events(rng):
        if page == "vip" and matched:
            o += ["", "VIP page detection:", f"    final score {fin:.3f} — MATCH"]
            break

    def _ocr(needle):
        idx, rec = gen._find(needle, rng=rng)
        if rec is None:
            return None
        gen._claim(idx)
        return {
            "raw": (re.search(r"raw=(?:'([^']*)'|\"([^\"]*)\")", rec["msg"]) or [None]),
            "raw_s": (lambda m: (m.group(1) or m.group(2) or "") if m else "")(
                re.search(r"raw=(?:'([^']*)'|\"([^\"]*)\")", rec["msg"])),
            "norm": (lambda m: (m.group(1) or m.group(2) or "") if m else "")(
                re.search(r"normalized=(?:'([^']*)'|\"([^\"]*)\")", rec["msg"])),
            "verdict": (gen._kv(rec["msg"], "verdict") or "unknown").lower(),
        }

    p1 = _ocr("OCR pass1 raw=")
    p2 = _ocr("OCR pass2")
    if p1:
        o += ["", "OCR pass 1:", "",
              f'    Raw text:        "{p1["raw_s"]}"',
              f'    Normalized text: "{p1["norm"]}"',
              f'    Verdict:         {p1["verdict"].upper()}']
    if p1 and p1["verdict"] != "unknown":
        o += ["", "The first OCR pass was conclusive.",
              "No second OCR pass was necessary."]
    elif p1 and p2:
        o += ["", "The first OCR pass was inconclusive, so a second pass ran",
              "(Otsu binarisation):", "",
              f'    Raw text:        "{p2["raw_s"]}"',
              f'    Normalized text: "{p2["norm"]}"',
              f'    Verdict:         {p2["verdict"].upper()}']
    elif p1:
        o += ["", "The first OCR pass was inconclusive.",
              "No second-pass record is present in this slice, so the final",
              "verdict cannot be stated from OCR evidence alone."]

    final = (p2 or p1 or {}).get("verdict")
    # Action evidence, straight from the program's own lines.
    i_sold, r_sold = gen._find("no click needed", rng=rng)
    i_free, r_free = gen._find("'Free' detected — collecting", rng=rng)
    i_any, r_any = gen._find("OCR inconclusive; clicking anyway", rng=rng)
    if r_sold:
        gen._claim(i_sold)
        o += ["", "Action:", "    None.", "",
              "The VIP Daily Chest was already collected (Sold Out).",
              "No reward click was sent."]
    elif r_any:
        gen._claim(i_any)
        o += ["", "Action:", "    Send the reward click anyway.", "",
              "Both OCR passes were inconclusive. The programmed fallback is to",
              "click regardless: a wasted click on a Sold Out button is harmless,",
              "whereas skipping a genuinely free chest is not.",
              "",
              "The collection action completed and the task returned DONE.",
              "(The report does not claim the server credited the reward — the",
              " program does not verify that.)"]
    elif r_free:
        gen._claim(i_free)
        o += ["", "Action:", "    Collect the free VIP Daily Chest.", "",
              "The collection action completed and the task returned DONE.",
              "(The report does not claim the server credited the reward — the",
              " program does not verify that.)"]
    elif final == "sold_out":
        o += ["", "Action:", "    None.", "",
              "The final verdict was SOLD OUT, so no reward click was sent."]
    elif final in ("free", "unknown") and p1:
        o += ["", "Action:",
              "    A reward click was expected, but no click record is present",
              "    in this slice, so the action cannot be confirmed."]
    return o


def _human_render_tutorial(gen, key, rng=None):
    """
    Task-specific enrichment for the Tutorial task.

    Narrates the three phases (tutorial_pg25, tutorial_pg27, one of the four
    end-state interstitials) straight from the task's own dlog lines, plus any
    phase-timeout ("restart") the task reported instead of reaching the next
    expected page.
    """
    o = []
    i, r = gen._find("── tutorial ── starting pass", rng=rng)
    if r:
        gen._claim(i)
        o += ["", "TASK ENTRY CHECKS", "",
              "The task returned to the main screen before starting the tutorial."]

    i, r = gen._find("── tutorial ── phase 1: clicking for tutorial_pg25", rng=rng)
    if r:
        gen._claim(i)
        o += ["", "Phase 1 — clicking once per second, watching for tutorial_pg25."]

    i, r = gen._find("── tutorial ── tutorial_pg25 seen", rng=rng)
    if r:
        gen._claim(i)
        o += ["", "tutorial_pg25 was detected and clicked."]
    else:
        i, r = gen._find("── tutorial ── phase 1 exceeded", rng=rng)
        if r:
            gen._claim(i)
            o += ["", "Phase 1 timed out — tutorial_pg25 never appeared, so the",
                  "task gave up and asked to be restarted rather than clicking",
                  "indefinitely."]

    i, r = gen._find("── tutorial ── clicked tutorial_pg25, entering phase 2", rng=rng)
    if r:
        gen._claim(i)
        o += ["", "Phase 2 — up to 4 clicks, 5s apart, watching for tutorial_pg27."]

    i, r = gen._find("── tutorial ── tutorial_pg27 seen", rng=rng)
    if r:
        gen._claim(i)
        o += ["", "tutorial_pg27 was detected — the tutorial itself is complete."]
    else:
        i, r = gen._find("── tutorial ── tutorial_pg27 not seen after 4 clicks", rng=rng)
        if r:
            gen._claim(i)
            o += ["", "tutorial_pg27 was never seen after 4 clicks, but the task",
                  "continued anyway rather than restarting — this phase is",
                  "designed to never fail the task on its own."]

    i, r = gen._find("── tutorial ── phase 3: clicking until an end page appears", rng=rng)
    if r:
        gen._claim(i)
        o += ["", "Phase 3 — clicking once per second, watching for one of the",
              "known post-tutorial pages (crisis forecast 1, midnight growth",
              "pack, bridge level rush, hancock offer)."]

    i, r = gen._find("── tutorial ── end page ", rng=rng)
    if r:
        gen._claim(i)
        m = re.search(r"end page '([^']+)' seen", r["msg"])
        page = m.group(1) if m else "an end page"
        o += ["", f"Action:", f"    '{page}' was seen — pressed back once.", "",
              "The tutorial task completed and returned DONE."]
    else:
        i, r = gen._find("── tutorial ── phase 3 exceeded", rng=rng)
        if r:
            gen._claim(i)
            o += ["", "Phase 3 timed out — none of the four expected end pages",
                  "appeared, so the task gave up and asked to be restarted."]

    for _, rr, page, px, tx, fin, thr, matched in gen._page_events(rng):
        if matched and page in ("tutorial_pg25", "tutorial_pg27",
                                 "crisis forecast 1", "midnight growth pack",
                                 "bridge level rush", "hancock offer"):
            o += ["", f"Page detection ({page}):", f"    final score {fin:.3f} — MATCH"]

    return o


HUMAN_TASK_RENDERERS = {
    "vip_collect": _human_render_vip_collect,
    "tutorial":    _human_render_tutorial,
}


class LogAnalyzer:
    """
    Local log scanner / summariser.  Stdlib only.

    v4 — SOURCE-GROUNDED parsing.  Every pattern below was derived by reading the
    actual log-producing calls in controller_ui_v7.py and android_automation_engine.py
    (see the `# emitted by:` comments on each entry in LOG_PATTERNS).

    Where logs land in FILES (what this analyzer can read):
      • controller_multi.log / controller_ui.log  ← _multi_log.* / _ui_log.* calls
            (run lifecycle, launch, stop, fatal, internet, close, retry, queue)
      • logs/<device>.log                          ← bot dlog.* calls
            (device_worker start, prepare_target_app, setup_vpn/target_app, task RESULT lines,
             guard recovery, RUN COMPLETE, fatal stage-2)
      • automation_log.log                          ← root logging.* (rare)
    NOTE: worker _push("log")/_log() and the controller's `_run_log_msg` write to
    the on-screen widgets / stdout, NOT to log files — so the "✓ dev → result"
    arrow line is screen-only.  Run SUCCESS in files is the device-log
    "── RUN COMPLETE ──" marker; run START is the controller "RUN START <adb> ..."
    / device "device_worker started" markers.
    """

    CONTROLLER_LOGS = ["controller_multi.log", "controller_ui.log", "automation_log.log"]

    _TS_PATTERNS = [
        (r"^(\d{4}-\d{2}-\d{2})[ T](\d{2}:\d{2}:\d{2}),(\d{3})", "%Y-%m-%d %H:%M:%S"),
        (r"^(\d{4}-\d{2}-\d{2})[ T](\d{2}:\d{2}:\d{2})", "%Y-%m-%d %H:%M:%S"),
        (r"^\[(\d{2}:\d{2}:\d{2})\]", "%H:%M:%S"),
    ]

    SESSION_GAP_SECONDS = 25 * 60
    _RUN_START_MARKERS = ("[RUN-START]", "RUN START", "device_worker started")
    RUN_START_DEDUPE_SECONDS = 5
    MAX_SCAN_BYTES_PER_FILE = 0
    MAX_UNCLASSIFIED_SAMPLES = 50

    # ──────────────────────────────────────────────────────────────────────────
    # A. SOURCE-DERIVED LOG PATTERN CATALOG
    # Each value is a list of lowercase substrings; a line matches the category if
    # ANY substring is present (substring match, cheap & robust to surrounding
    # text).  Comments cite the real emitting call.  Categories are checked in
    # _classify_entry().  Noisy categories are deduped in analyze().
    # ──────────────────────────────────────────────────────────────────────────
    LOG_PATTERNS = {
        # ── run lifecycle (controller _multi_log) ─────────────────────────────
        # emitted by _run_start_selected: _multi_log.info("[RUN-START] selected_ids=...")
        #                                 _multi_log.info("[RUN] selected_count=...")
        # emitted by _run_launch_one:     _multi_log.info(f"RUN START  {adb_id}  tasks=...")
        # emitted by device_worker:       dlog.info(f"device_worker started  dev=...  tasks=...")
        "run_start": ["[run-start]", "run start  ", "device_worker started", "[run] selected_count"],
        # emitted by device_worker end:   dlog.info(f"── RUN COMPLETE ── ...")
        "run_complete": ["── run complete ──", "run complete ──"],
        # emitted by run_done queue handler / _on_run_done path:
        #   _multi_log.info(f"[RUN-DONE] adb_id={adb_id} ok={ok} result={result}")
        # Reliable FILE record of the FINAL run result (success/failed/stopped).
        "run_done": ["[run-done]"],
        # emitted by _poll run_done handler is screen-only; device-log proxy below
        # emitted by _on_run_done badge path / run_tasks finally diag
        "run_done_diag": ["_on_run_done ──", "[diag] run_tasks ──"],

        # ── prepare_target_app lifecycle (bot dlog) ───────────────────────────────────
        # emitted by prepare_target_app(): dlog.info("prepare_target_app() ── START | ...")
        #           device_worker:  dlog.info("[DEVICE_WORKER] entering prepare_target_app adb_id=...")
        "prepare_target_app_start": ["prepare_target_app() ── start", "entering prepare_target_app",
                              "prepare_target_app: starting", "running prepare_target_app"],
        # emitted by prepare_target_app(): dlog.info("prepare_target_app() ── COMPLETED SUCCESSFULLY | ...")
        #           device_worker:  _log("prepare_target_app completed", "dim")
        #                           dlog.info("── task loop ── prepare_target_app complete ...")
        "prepare_target_app_success": ["prepare_target_app() ── completed", "prepare_target_app completed",
                               "prepare_target_app complete", "prepare_target_app: done"],
        # emitted by device_worker: dlog.error("[BA-RETRY] prepare_target_app failed after N attempts")
        #           prepare_target_app():   "prepare_target_app() ── setup_vpn() FAILED" / "setup_target_app() FAILED"
        #           _push("all_done", result="prepare_target_app failed...")
        "prepare_target_app_failure": ["prepare_target_app failed", "prepare_target_app() ── setup_vpn() failed",
                               "prepare_target_app() ── setup_target_app() failed",
                               "prepare_target_app attempt", "prepare_target_app_failed"],
        # emitted by device_worker BA-RETRY: dlog.error("[BA-RETRY] ... retry N/M")
        "prepare_target_app_retry": ["[ba-retry]", "prepare_target_app retry"],

        # ── setup_vpn (bot dlog) ───────────────────────────────────────────────
        # emitted by prepare_target_app(): dlog.info("prepare_target_app() ── calling setup_vpn()")
        "setup_vpn_start": ["── calling setup_vpn()", "_setup_vpn_inner ──"],
        # emitted by prepare_target_app(): dlog.info("prepare_target_app() ── setup_vpn() OK in ...")
        "setup_vpn_success": ["setup_vpn() ok in", "vpn ok ("],
        # emitted by prepare_target_app(): dlog.error("prepare_target_app() ── setup_vpn() FAILED after ...")
        "setup_vpn_failure": ["setup_vpn() failed", "setup_vpn failed", "[vpn-fail-restart]"],

        # ── setup_target_app (bot dlog) ───────────────────────────────────────────────
        # emitted by prepare_target_app(): dlog.info("prepare_target_app() ── calling setup_target_app()")
        #           setup_target_app():   dlog.info("setup_target_app() CALLED")
        "setup_target_app_start": ["── calling setup_target_app()", "setup_target_app() called", "setup_target_app() starting"],
        # emitted by _target_app_watch_loading: dlog.info("Loading confirmed done after ...")
        #           task loop: dlog.info("── task loop ── main screen confirmed ...")
        "setup_target_app_success": ["loading confirmed done", "main screen confirmed", "main screen reached"],
        # emitted by prepare_target_app(): dlog.error("prepare_target_app() ── setup_target_app() FAILED after ...")
        "setup_target_app_failure": ["setup_target_app() failed", "setup_target_app failed",
                              "main screen not reached"],
        # emitted by loading watcher: "[LOADING] ... stuck" / guard recovery failed during loading
        "loading_stuck": ["[loading]", "loading stuck", "guard recovery failed during loading"],

        # ── task lifecycle (bot dlog, device_worker task loop) ─────────────────
        # emitted by device_worker: dlog.info(f"{'─'*20} TASK: {task_key} {'─'*20}")
        #                           _log(f"▶  starting {task_key}", "info")
        "task_start": ["── task: ", " task: ", "▶  starting "],
        # emitted by device_worker: dlog.info(f"── {task_key} ── RESULT: complete ✓")
        "task_done": ["── result: complete", "result: complete ✓"],
        # emitted by device_worker: dlog.info(f"── {task_key} ── RESULT: skipped (already done)")
        "task_skipped": ["result: skipped"],
        # emitted by device_worker: dlog.error(f"── {task_key} ── RESULT: error — ... failed after max restarts")
        #                           dlog.error(f"── {task_key} ── RESULT: failed ({result})")
        "task_failed": ["result: error", "result: failed", "failed after max restarts"],
        # emitted by task loop / _run_one restart paths
        "task_restart": ["── task loop ── full_restart", "sub_restart", "restarting task loop",
                         "resuming tasks"],
        # emitted by device_worker error path / setup stage-2: max restarts exhausted
        "max_attempts": ["failed after max restarts", "exceeded max", "max_restarts reached",
                         "max restarts reached"],

        # ── guards (bot dlog) ──────────────────────────────────────────────────
        # emitted by guard_check_and_recover / VpnGuard / TargetAppGuard recovery:
        #   dlog.* "── Guard Recovery ── ..." / "── TargetAppGuard Recovery ── ..."
        "guard_recovery": ["── guard recovery ──", "── target_appguard recovery ──",
                           "── vpnguard ──", "guard recovered"],
        # emitted by device_worker: dlog.error(f"── {task_key} ── GuardRecoveryFailed (reason=...)")
        "guard_recovery_failed": ["guardrecoveryfailed", "guard recovery failed"],

        # ── connection / vpn / offline / reopen (bot dlog) ─────────────────────
        # emitted by task loop / B4 handler / pages: "connection issue ..."
        "connection_issue": ["connection issue"],
        # emitted by task loop: dlog.warning("── task loop ── vpn_down: changing server")
        #           TargetAppGuard recovery: "── TargetAppGuard Recovery ── VPN down ..."
        "vpn_down": ["vpn_down", "vpn down"],
        # emitted by TargetAppGuard recovery: "Unexpected page at stage N" / passive "unexpected page"
        "unexpected_page": ["unexpected page", "unexpected home"],
        # emitted by offline checks: "ADB offline" / "Device OFFLINE" / "device offline"
        "adb_offline": ["adb offline", "device offline", "device still offline",
                        "adb ping failed", "(device offline)"],
        # emitted by reopen_device / _reopen_device_capped: "── reopen_device ──"
        "emulator_reopen": ["reopen_device", "reopening device", "reopened",
                            "emulator relaunched", "relaunch"],

        # ── fatal / emergency (bot dlog + controller _multi_log) ───────────────
        # emitted by setup stage-2: dlog.error("── STAGE 2 ── Newer TargetApp version ... NOT in APK_FOLDER ...")
        #           device_worker:  dlog.error("FATAL: ...") + _push("run_fatal_stop")
        #           controller:     _multi_log.error(f"[FATAL] run_fatal_stop received: {reason}")
        "fatal_apk": ["fatalapkerror", "[fatal]", "fatal:", "not in apk_folder",
                      "apk is not in apk_folder", "run_fatal_stop"],
        # emitted by controller: _multi_log.error("[INTERNET] GLOBAL INTERNET DOWN ...")
        "internet_emergency": ["[internet] global internet down", "internet_down_emergency",
                               "global internet down"],
        # emitted by controller _run_stop_all / _force_stop_worker: "[STOP-ALL]" / "[STOP] stop_all"
        "stop_all": ["[stop-all]", "stop_all", "── stop_all"],
        # emitted by controller _on_run_done close-failed path: "[CLOSE_FAILED] ..."
        "close_failed": ["[close_failed]", "close_failed", "close failed"],

        # ── controller skip / config (controller _multi_log) ───────────────────
        # emitted by _run_launch_one / _run_start_selected:
        #   _multi_log.info("No Task Config found for DeviceType ...")
        "no_task_config": ["no task config found for devicetype", "no task config"],
        # emitted by device_worker: dlog.error("device_worker reached task loop with EMPTY task_keys")
        #           _run_launch_one: "[LAUNCH] {adb} skipped — empty ..."
        "empty_task_list": ["empty task_keys", "empty task list", "empty_task_list",
                            "skipped — empty"],
        # emitted by _run_start_selected/retry: "[RETRY] device=X skipped_no_pending"
        "skipped_no_pending": ["skipped_no_pending", "skipped — no task", "skipped no pending"],
    }

    # Categories whose raw lines are high-volume and must be deduped by
    # (device, category, minute) before counting.
    NOISY_CATEGORIES = {
        "connection_issue", "guard_recovery", "guard_recovery_failed", "vpn_down",
        "adb_offline", "emulator_reopen", "unexpected_page", "loading_stuck",
        "internet_emergency", "fatal_apk", "stop_all", "close_failed",
        "no_task_config", "skipped_no_pending",
    }

    def __init__(self, base_dir: str = "."):
        import os, threading
        self.base_dir = base_dir or "."
        self.logs_dir = os.path.join(self.base_dir, "logs")
        self.device_type_map: dict = {}
        self.device_name_map: dict = {}
        self._scan_cache: dict = {}
        self._scan_cache_lock = threading.Lock()
        self.last_scan_stats: dict = {}
        # Task-key registry for display names + RESULT line task extraction.
        # Populated by analyze() from the controller's TASK_DEFS / SUBTASK_ORDER.
        self.task_keys: set = set()
        self.task_label_map: dict = {}

    # ── precompiled regexes ──────────────────────────────────────────────────
    def _compiled(self):
        import re
        if getattr(self, "_rx", None) is None:
            self._rx = {
                "ts": [(re.compile(p), fmt) for p, fmt in self._TS_PATTERNS],
                "level": re.compile(r"^\d[\d\-: ,T]+\s+(DEBUG|INFO|WARNING|ERROR|CRITICAL)\b"),
                "dev_in_line": re.compile(
                    r"(localhost[:_-]\d{2,6}|127\.0\.0\.1[:_-]\d{2,6}|emulator-\d+)"),
                # task header: "── TASK: vip_collect ──" or "TASK: vip_collect"
                "task_hdr": re.compile(r"task:\s*([a-z0-9_]+)", re.I),
                # task result: "── vip_collect ── RESULT: complete ✓"
                "task_result": re.compile(r"──\s*([a-z0-9_]+)\s*──\s*result:\s*(.+)", re.I),
                # GuardRecoveryFailed task: "── vip_collect ── GuardRecoveryFailed"
                "guard_fail_task": re.compile(r"──\s*([a-z0-9_]+)\s*──\s*guardrecoveryfailed", re.I),
                # controller run start with device: "RUN START  localhost:5555  tasks=..."
                "run_start_dev": re.compile(
                    r"run start\s+(localhost[:_-]\d{2,6}|127\.0\.0\.1[:_-]\d{2,6}|emulator-\d+)", re.I),
                # device_worker started dev=...
                "worker_started_dev": re.compile(
                    r"device_worker started\s+dev=(localhost[:_-]\d{2,6}|127\.0\.0\.1[:_-]\d{2,6}|emulator-\d+)", re.I),
                # controller run_done screen line (also appears if ui log captured): "✓ dev → result"
                "run_done_arrow": re.compile(
                    r"[✓✗]\s*(localhost[:_-]\d{2,6}|127\.0\.0\.1[:_-]\d{2,6}|emulator-\d+)\s*→\s*(.+)"),
                # reliable file record: "[RUN-DONE] adb_id=<id> ok=<True|False> result=<text>"
                "run_done_kv": re.compile(
                    r"\[run-done\]\s+adb_id=(\S+)\s+ok=(true|false)\s+result=(.+)", re.I),
                # prepare_target_app attempt with explicit ok=True/False
                "ba_ok": re.compile(r"prepare_target_app.*ok=(true|false)", re.I),
            }
        return self._rx

    # ── filename → device normalisation ─────────────────────────────────────
    @staticmethod
    def _device_from_filename(base: str):
        import re
        stem = base[:-4] if base.lower().endswith(".log") else base
        m = re.match(r"^(emulator)-(\d{2,6})$", stem)
        if m:
            return f"emulator-{m.group(2)}"
        m = re.match(r"^(localhost|127\.0\.0\.1)[._-](\d{2,6})$", stem)
        if m:
            return f"{m.group(1)}:{m.group(2)}"
        m = re.match(r"^(localhost|127\.0\.0\.1)(\d{2,6})$", stem)
        if m:
            return f"{m.group(1)}:{m.group(2)}"
        return stem

    @staticmethod
    def _norm_device(d):
        if not d:
            return d
        d = d.strip()
        if d.startswith("emulator-"):
            return d
        return d.replace("_", ":").replace("-", ":")

    # ── file discovery ───────────────────────────────────────────────────────
    def _discover_log_files(self):
        import os, glob
        files = []
        for fn in self.CONTROLLER_LOGS:
            files.append((os.path.join(self.base_dir, fn), None))
        try:
            for fpath in sorted(glob.glob(os.path.join(self.logs_dir, "*.log"))):
                files.append((fpath, self._device_from_filename(os.path.basename(fpath))))
        except Exception:
            pass
        return files

    # ── single-file parse ──────────────────────────────────────────────────────
    def _scan_one_file(self, fpath: str, file_dev):
        import os
        from datetime import datetime
        rx = self._compiled()
        ts_compiled = rx["ts"]; level_re = rx["level"]; dev_in_line_re = rx["dev_in_line"]
        if not os.path.exists(fpath):
            return []
        source = os.path.basename(fpath)
        entries = []
        last_ts = None
        try:
            fsize = os.path.getsize(fpath)
            with open(fpath, "r", encoding="utf-8", errors="replace") as f:
                if self.MAX_SCAN_BYTES_PER_FILE and fsize > self.MAX_SCAN_BYTES_PER_FILE:
                    try:
                        f.seek(fsize - self.MAX_SCAN_BYTES_PER_FILE)
                        f.readline()
                    except Exception:
                        f.seek(0)
                for raw in f:
                    line = raw.rstrip("\n").rstrip("\r")
                    if not line.strip():
                        continue
                    ts = None
                    for rxx, fmt in ts_compiled:
                        m = rxx.match(line)
                        if not m:
                            continue
                        try:
                            if fmt == "%H:%M:%S":
                                base_day = (last_ts or datetime.now()).date()
                                tt = datetime.strptime(m.group(1), "%H:%M:%S").time()
                                ts = datetime.combine(base_day, tt)
                            else:
                                ts = datetime.strptime(
                                    f"{m.group(1)} {m.group(2)}", "%Y-%m-%d %H:%M:%S")
                        except Exception:
                            ts = None
                        break
                    if ts is not None:
                        last_ts = ts
                    else:
                        ts = last_ts
                    lvl = None
                    lm = level_re.match(line)
                    if lm:
                        lvl = lm.group(1)
                    dev = file_dev
                    if dev is None:
                        dm = dev_in_line_re.search(line)
                        if dm:
                            dev = self._norm_device(dm.group(1))
                    entries.append({"ts": ts, "source": source, "device": dev,
                                    "level": lvl, "line": line})
        except Exception:
            return []
        return entries

    # ── parallel scan with cache ─────────────────────────────────────────────
    def scan_logs(self, progress=None, max_workers=None, use_cache=True) -> list:
        import os, time
        from datetime import datetime
        from concurrent.futures import ThreadPoolExecutor, as_completed

        t0 = time.time()
        files = self._discover_log_files()
        existing = [(fp, dv) for fp, dv in files if os.path.exists(fp)]
        if progress:
            try: progress(f"queued {len(existing)} log files")
            except Exception: pass

        def _stat_key(fp):
            try:
                st = os.stat(fp)
                return (os.path.abspath(fp), st.st_mtime_ns, st.st_size)
            except Exception:
                return None

        results_by_path = {}
        to_scan = []
        for fp, dv in existing:
            key = _stat_key(fp)
            if use_cache and key is not None:
                with self._scan_cache_lock:
                    cached = self._scan_cache.get(key)
                if cached is not None:
                    results_by_path[fp] = list(cached)
                    if progress:
                        try: progress(f"cache hit {os.path.basename(fp)} ({len(cached)} entries)")
                        except Exception: pass
                    continue
            to_scan.append((fp, dv, key))

        if to_scan:
            workers = max_workers or min(8, max(2, (os.cpu_count() or 4)), len(to_scan))
            with ThreadPoolExecutor(max_workers=workers) as ex:
                fut_map = {ex.submit(self._scan_one_file, fp, dv): (fp, dv, key)
                           for fp, dv, key in to_scan}
                for fut in as_completed(fut_map):
                    fp, dv, key = fut_map[fut]
                    try: ents = fut.result()
                    except Exception: ents = []
                    results_by_path[fp] = ents
                    if key is not None:
                        with self._scan_cache_lock:
                            for k in [k for k in self._scan_cache if k[0] == key[0]]:
                                del self._scan_cache[k]
                            self._scan_cache[key] = list(ents)
                    if progress:
                        try: progress(f"scanned {os.path.basename(fp)} ({len(ents)} entries)")
                        except Exception: pass

        entries = []
        for fp, _dv in existing:
            entries.extend(results_by_path.get(fp, []))
        entries.sort(key=lambda e: (e["ts"] is None, e["ts"] or datetime.min))

        elapsed = time.time() - t0
        self.last_scan_stats = {
            "files": len(existing), "entries": len(entries),
            "elapsed": elapsed, "cache_hits": len(existing) - len(to_scan),
        }
        if progress:
            try: progress(f"scan complete: {len(existing)} files, {len(entries)} entries, {elapsed:.1f}s")
            except Exception: pass
        return entries

    # ── timeframe detection ──────────────────────────────────────────────────
    def available_timeframes(self, entries: list) -> list:
        from datetime import datetime, timedelta
        now = datetime.now()
        opts = [
            {"label": "All logs",     "start": None, "end": None},
            {"label": "Today",        "start": now.replace(hour=0, minute=0, second=0, microsecond=0), "end": None},
            {"label": "Last 1 hour",  "start": now - timedelta(hours=1), "end": None},
            {"label": "Last 3 hours", "start": now - timedelta(hours=3), "end": None},
            {"label": "Last 6 hours", "start": now - timedelta(hours=6), "end": None},
        ]
        for s, e in self._detect_sessions(entries):
            opts.append({"label": f"Session: {s:%Y-%m-%d %H:%M} → {e:%Y-%m-%d %H:%M}",
                         "start": s, "end": e})
        return opts

    def _detect_sessions(self, entries: list) -> list:
        ts_entries = [e for e in entries if e["ts"] is not None]
        if not ts_entries:
            return []
        ts_entries.sort(key=lambda e: e["ts"])
        sessions = []
        cur_start = ts_entries[0]["ts"]; cur_end = ts_entries[0]["ts"]; prev = ts_entries[0]["ts"]
        for e in ts_entries[1:]:
            ts = e["ts"]
            gap = (ts - prev).total_seconds()
            is_marker = any(mk.lower() in e["line"].lower() for mk in self._RUN_START_MARKERS)
            if gap > self.SESSION_GAP_SECONDS or (is_marker and gap > 60):
                sessions.append((cur_start, cur_end)); cur_start = ts
            cur_end = ts; prev = ts
        sessions.append((cur_start, cur_end))
        sessions.sort(key=lambda p: p[0], reverse=True)
        return sessions[:30]

    # ── filter / devices ───────────────────────────────────────────────────────
    def _filter(self, entries, start, end, device):
        out = []
        ndev = self._norm_device(device) if device else None
        for e in entries:
            ts = e["ts"]
            if start is not None and (ts is None or ts < start): continue
            if end is not None and (ts is None or ts > end): continue
            if ndev and self._norm_device(e["device"]) != ndev: continue
            out.append(e)
        return out

    def devices_in(self, entries):
        return sorted({self._norm_device(e["device"]) for e in entries if e["device"]})

    # ── clean sample line ──────────────────────────────────────────────────────
    def _clean_sample_line(self, entry) -> str:
        import re
        msg = entry.get("line", "")
        msg = re.sub(r"^\d{4}-\d{2}-\d{2}[ T]\d{2}:\d{2}:\d{2}(?:,\d{3})?\s+"
                     r"(?:DEBUG|INFO|WARNING|ERROR|CRITICAL)?\s*", "", msg)
        msg = re.sub(r"^\[\d{2}:\d{2}:\d{2}\]\s*", "", msg)
        dev = self._norm_device(entry.get("device")) or "-"
        m = re.match(r"^\s*((?:localhost|127\.0\.0\.1)[:_-]\d{2,6}|emulator-\d+)\b\s*", msg, flags=re.I)
        if m and self._norm_device(m.group(1)) == dev:
            msg = msg[m.end():]
        msg = msg.lstrip("─-·: ").strip()
        ts = self._fmt_ts(entry.get("ts"))
        return f"{ts}  {dev}  {msg[:200]}"

    # ──────────────────────────────────────────────────────────────────────────
    # D. CLASSIFICATION — turn one entry into zero+ event records using the
    # source-derived catalog.  Each event: {kind, device, ts, line, task_key?}
    # ──────────────────────────────────────────────────────────────────────────
    def _classify_entry(self, entry) -> list:
        rx = self._compiled()
        line = entry.get("line", "")
        low = line.lower()
        dev = self._norm_device(entry.get("device"))
        ts = entry.get("ts")
        events = []

        def emit(kind, task_key=None, override_dev=None):
            events.append({"kind": kind, "device": override_dev or dev,
                           "ts": ts, "line": line, "task_key": task_key})

        # Run start (capture device from controller form if present)
        rs_dev = None
        m = rx["run_start_dev"].search(line)
        if m:
            rs_dev = self._norm_device(m.group(1))
        else:
            m2 = rx["worker_started_dev"].search(line)
            if m2:
                rs_dev = self._norm_device(m2.group(1))
        if rs_dev or any(s in low for s in self.LOG_PATTERNS["run_start"]):
            emit("run_start", override_dev=rs_dev or dev)

        # Run complete (device-log success marker)
        if any(s in low for s in self.LOG_PATTERNS["run_complete"]):
            emit("run_complete")

        # Screen-only arrow line (only if a UI log somehow captured it) → run result
        ma = rx["run_done_arrow"].search(line)
        if ma:
            res = ma.group(2).strip().lower()
            rdev = self._norm_device(ma.group(1))
            kind = ("run_result_done" if res.startswith("done")
                    else "run_result_stopped" if "stopped" in res
                    else "run_result_failed")
            events.append({"kind": kind, "device": rdev, "ts": ts, "line": line,
                           "task_key": None, "result_text": res})

        # Reliable FILE run result: "[RUN-DONE] adb_id=<id> ok=<bool> result=<text>"
        mk = rx["run_done_kv"].search(line)
        if mk:
            rdev = self._norm_device(mk.group(1))
            okv = mk.group(2).lower() == "true"
            res = mk.group(3).strip().lower()
            # B: ok=True & done/success → done; result mentions stopped → stopped;
            #    otherwise (ok=False) → failed.
            if okv and ("done" in res or "success" in res or "complete" in res):
                kind = "run_result_done"
            elif "stopped" in res:
                kind = "run_result_stopped"
            else:
                kind = "run_result_failed"
            events.append({"kind": kind, "device": rdev, "ts": ts, "line": line,
                           "task_key": None, "result_text": res})

        # ── task RESULT lines (most reliable per-task signal) ──────────────────
        mr = rx["task_result"].search(line)
        if mr:
            tkk = mr.group(1)
            res = mr.group(2).strip().lower()
            if "skipped after max" in res or "skip after max" in res:
                emit("task_skipped_after_max", task_key=tkk)
            elif "already done" in res or "already-done" in res:
                emit("task_skipped_already_done", task_key=tkk)
            elif "skipped" in res:
                emit("task_skipped", task_key=tkk)
            elif res.startswith("complete") or "complete ✓" in res or res == "done":
                emit("task_done", task_key=tkk)
            elif ("failed after max" in res or "max_restarts" in res
                  or "max restarts" in res or "max_attempts" in res):
                emit("task_failed_max", task_key=tkk)
            elif "error" in res or "failed" in res:
                emit("task_failed", task_key=tkk)
        else:
            # task header (start) — only when not a RESULT line
            mh = rx["task_hdr"].search(line)
            if mh and ("task:" in low):
                emit("task_start", task_key=mh.group(1))
            elif "▶  starting " in low:
                # device_worker _log start (screen) — task key after 'starting '
                import re as _re
                mm = _re.search(r"starting\s+([a-z0-9_]+)", low)
                if mm:
                    emit("task_start", task_key=mm.group(1))

        # GuardRecoveryFailed (task-scoped)
        mg = rx["guard_fail_task"].search(line)
        if mg:
            emit("guard_recovery_failed", task_key=mg.group(1))
        elif any(s in low for s in self.LOG_PATTERNS["guard_recovery_failed"]):
            emit("guard_recovery_failed")

        # prepare_target_app attempt/success/failure (counted independently)
        if ("prepare_target_app" in low or "_prepare" in low or "prep:" in low):
            mok = rx["ba_ok"].search(line)
            if any(s in low for s in self.LOG_PATTERNS["prepare_target_app_start"]):
                emit("prepare_target_app_start")
            # success
            if (any(s in low for s in self.LOG_PATTERNS["prepare_target_app_success"])
                    or (mok and mok.group(1).lower() == "true")):
                emit("prepare_target_app_success")
            # failure
            if (any(s in low for s in self.LOG_PATTERNS["prepare_target_app_failure"]
                    if s not in ("prepare_target_app attempt",))  # 'attempt' alone isn't a failure
                    or (mok and mok.group(1).lower() == "false")):
                emit("prepare_target_app_failure")
        if any(s in low for s in self.LOG_PATTERNS["prepare_target_app_retry"]):
            emit("prepare_target_app_retry")

        # setup_vpn / setup_target_app
        for cat in ("setup_vpn_start", "setup_vpn_success", "setup_vpn_failure",
                    "setup_target_app_start", "setup_target_app_success", "setup_target_app_failure",
                    "loading_stuck", "task_restart", "max_attempts",
                    "guard_recovery", "connection_issue", "vpn_down",
                    "unexpected_page", "adb_offline", "emulator_reopen",
                    "fatal_apk", "internet_emergency", "stop_all", "close_failed",
                    "no_task_config", "empty_task_list", "skipped_no_pending"):
            if any(s in low for s in self.LOG_PATTERNS[cat]):
                emit(cat)

        return events

    # ── analysis ──────────────────────────────────────────────────────────────
    def analyze(self, entries, start=None, end=None, device=None, task_defs=None,
                subtask_order=None) -> dict:
        from collections import defaultdict

        task_defs = task_defs or {}
        self.task_keys = set(task_defs.keys())
        self.task_label_map = {k: (v.get("label") or k) for k, v in task_defs.items()}
        if subtask_order:
            for k in subtask_order:
                self.task_keys.add(k)
                self.task_label_map.setdefault(k, k)
        task_label = self.task_label_map

        scoped = self._filter(entries, start, end, None)
        sel_dev = self._norm_device(device) if device else None

        overall = defaultdict(int)
        per_task = defaultdict(lambda: defaultdict(int))
        per_device = defaultdict(lambda: defaultdict(int))
        per_device_task = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
        per_device_last_fail = {}
        per_device_last_task_result = defaultdict(dict)
        timeline = []
        issues_samples = defaultdict(list)
        issues_count = defaultdict(int)
        issues_raw = defaultdict(int)
        devices_seen = set()
        dedupe_seen = defaultdict(set)
        run_records = defaultdict(list)
        last_run_start_ts = {}
        unclassified = []
        classified_line_ids = set()
        # item 2: most recent "important" event per device (reason label + clean
        # line + ts) — used to explain incomplete runs.
        per_device_last_issue = defaultdict(lambda: {"reason": None, "line": None, "ts": None})
        # items 3/4: per-issue → per-device counts (deduped) for "top devices".
        issue_device_counts = defaultdict(lambda: defaultdict(int))
        # item 4: per-noisy-event → per-device counts (for affected-device stats).
        evt_device_counts = defaultdict(lambda: defaultdict(int))
        # item 5: did this timeframe contain any reliable [RUN-DONE] file lines?
        run_done_lines_present = [False]
        # reason labels for incomplete-run explanation (item 2)
        REASON_FOR_CAT = {
            "connection_issue": "connection issue",
            "loading_stuck": "loading stuck",
            "adb_offline": "adb offline",
            "prepare_target_app_failure": "prepare_target_app failed",
            "setup_target_app_failure": "setup_target_app failed",
            "setup_vpn_failure": "setup_vpn failed",
            "guard_recovery_failed": "guard recovery failed",
            "task_failed": "task failed",
            "task_failed_max": "task failed (max attempts)",
            "vpn_down": "vpn down",
            "unexpected_page": "unexpected page",
            "emulator_reopen": "emulator reopen",
            "fatal_apk": "FatalAPKError",
            "internet_emergency": "internet emergency",
        }

        def minute_bucket(ts):
            return ts.strftime("%Y-%m-%d %H:%M") if ts is not None else "none"

        def add_tl(ts, dev, text):
            timeline.append((ts, dev, text))

        # issue category → friendly label for Potential Issues panel
        ISSUE_LABEL = {
            "connection_issue": "repeated connection issue popup",
            "guard_recovery": "repeated guard recovery",
            "guard_recovery_failed": "guard recovery failed",
            "vpn_down": "repeated VPN down",
            "adb_offline": "repeated ADB offline",
            "emulator_reopen": "repeated emulator reopen",
            "unexpected_page": "unexpected page",
            "loading_stuck": "TargetApp loading stuck",
            "internet_emergency": "internet emergency",
            "fatal_apk": "FatalAPKError",
            "stop_all": "Stop All used",
            "close_failed": "close_failed Issues",
            "no_task_config": "no Task Config found for DeviceType",
            "empty_task_list": "empty task list",
            "skipped_no_pending": "skipped — no pending tasks",
            "task_failed_max": "task failed after max_attempts",
            "task_skipped_after_max": "task skipped after max restarts",
            "prepare_target_app_failure": "prepare_target_app failed",
            "setup_vpn_failure": "setup_vpn failed",
            "setup_target_app_failure": "setup_target_app failed",
        }

        def note_issue(cat, entry, noisy):
            issues_raw[cat] += 1
            if noisy:
                dev0 = self._norm_device(entry["device"]) or "-"
                bkey = (dev0, cat, minute_bucket(entry["ts"]))
                if bkey in dedupe_seen[("issue", cat)]:
                    return False
                dedupe_seen[("issue", cat)].add(bkey)
            issues_count[cat] += 1
            # item 3: per-issue per-device counts for "top devices"
            dev1 = self._norm_device(entry["device"]) or "-"
            issue_device_counts[cat][dev1] += 1
            # item 2: update this device's last important event + reason label
            reason = REASON_FOR_CAT.get(cat)
            if reason and dev1 != "-":
                li = per_device_last_issue[dev1]
                li["reason"] = reason
                li["line"] = self._clean_sample_line(entry)
                li["ts"] = entry["ts"]
            if len(issues_samples[cat]) < 5:
                issues_samples[cat].append(self._clean_sample_line(entry))
            return True

        def dedup_event(cat, dev, entry):
            dev0 = self._norm_device(dev) or "-"
            bkey = (dev0, cat, minute_bucket(entry["ts"]))
            if bkey in dedupe_seen[("evt", cat)]:
                return False
            dedupe_seen[("evt", cat)].add(bkey)
            # item 4: per-event per-device deduped counts (for affected devices)
            evt_device_counts[cat][dev0] += 1
            return True

        for e in scoped:
            dev = self._norm_device(e["device"])
            if dev:
                devices_seen.add(dev)
            evs = self._classify_entry(e)
            if evs:
                classified_line_ids.add(id(e))
            for ev in evs:
                kind = ev["kind"]; edev = ev["device"]; tkk = ev.get("task_key")
                if edev:
                    devices_seen.add(edev)

                # ── run lifecycle ──────────────────────────────────────────────
                if kind == "run_start":
                    add_tl(ev["ts"], edev, "RUN START")
                    if edev and ev["ts"] is not None:
                        prev = last_run_start_ts.get(edev)
                        if prev is None or abs((ev["ts"] - prev).total_seconds()) > self.RUN_START_DEDUPE_SECONDS:
                            run_records[edev].append({"start": ev["ts"], "result": None})
                            last_run_start_ts[edev] = ev["ts"]
                    elif edev:
                        run_records[edev].append({"start": None, "result": None})
                elif kind == "run_complete":
                    add_tl(ev["ts"], edev, "RUN COMPLETE")
                    self._attach_run_result(run_records, edev, "done", ev["ts"])
                elif kind in ("run_result_done", "run_result_stopped", "run_result_failed"):
                    res = {"run_result_done": "done", "run_result_stopped": "stopped",
                           "run_result_failed": "failed"}[kind]
                    self._attach_run_result(run_records, edev, res, ev["ts"])
                    add_tl(ev["ts"], edev, f"run_done → {res}")
                    # item 5: note whether reliable [RUN-DONE] file lines exist
                    if "[run-done]" in ev["line"].lower():
                        run_done_lines_present[0] = True

                # ── prepare_target_app ────────────────────────────────────────────────
                elif kind == "prepare_target_app_start":
                    overall["prepare_target_app_attempts"] += 1
                    if edev: per_device[edev]["prepare_target_app_attempts"] += 1
                    add_tl(ev["ts"], edev, "prepare_target_app started")
                elif kind == "prepare_target_app_success":
                    overall["prepare_target_app_success"] += 1
                    if edev: per_device[edev]["prepare_target_app_success"] += 1
                    add_tl(ev["ts"], edev, "prepare_target_app success")
                elif kind == "prepare_target_app_failure":
                    overall["prepare_target_app_failure"] += 1
                    if edev:
                        per_device[edev]["prepare_target_app_failures"] += 1
                        per_device_last_fail[edev] = "prepare_target_app failed"
                    add_tl(ev["ts"], edev, "prepare_target_app failed")
                    note_issue("prepare_target_app_failure", e, noisy=True)
                elif kind == "prepare_target_app_retry":
                    overall["prepare_target_app_retries"] += 1

                # ── setup stages ──────────────────────────────────────────────
                elif kind == "setup_vpn_start":
                    if dedup_event("vpn_setup", edev, e):
                        overall["vpn_setup_events"] += 1
                        if edev: per_device[edev]["vpn_setup"] += 1
                elif kind == "setup_vpn_success":
                    if dedup_event("vpn_connect", edev, e):
                        overall["vpn_connect_events"] += 1
                        if edev: per_device[edev]["vpn_connect"] += 1
                        add_tl(ev["ts"], edev, "VPN ok")
                elif kind == "setup_vpn_failure":
                    overall["setup_vpn_failures"] += 1
                    if edev:
                        per_device[edev]["setup_vpn_failures"] += 1
                        per_device_last_fail[edev] = "setup_vpn failed"
                    note_issue("setup_vpn_failure", e, noisy=True)
                    add_tl(ev["ts"], edev, "setup_vpn failed")
                elif kind == "setup_target_app_start":
                    if dedup_event("target_app_setup", edev, e):
                        overall["target_app_setup_events"] += 1
                        if edev: per_device[edev]["target_app_setup"] += 1
                elif kind == "setup_target_app_success":
                    if dedup_event("target_app_main", edev, e):
                        add_tl(ev["ts"], edev, "TargetApp main reached")
                elif kind == "setup_target_app_failure":
                    overall["setup_target_app_failures"] += 1
                    if edev:
                        per_device[edev]["setup_target_app_failures"] += 1
                        per_device_last_fail[edev] = "setup_target_app failed"
                    note_issue("setup_target_app_failure", e, noisy=True)
                    add_tl(ev["ts"], edev, "setup_target_app failed")
                elif kind == "loading_stuck":
                    if dedup_event("loading_stuck", edev, e):
                        overall["target_app_loading_stuck_events"] += 1
                        if edev: per_device[edev]["target_app_loading_stuck"] += 1
                    note_issue("loading_stuck", e, noisy=True)

                # ── tasks ──────────────────────────────────────────────────────
                elif kind == "task_start":
                    if tkk:
                        per_task[tkk]["attempts"] += 1
                        if edev: per_device_task[edev][tkk]["attempts"] += 1
                        add_tl(ev["ts"], edev, f"{tkk} start")
                elif kind == "task_done":
                    if tkk:
                        per_task[tkk]["done"] += 1; overall["task_done"] += 1
                        if edev:
                            per_device_task[edev][tkk]["done"] += 1
                            per_device_last_task_result[edev][tkk] = "done"
                        add_tl(ev["ts"], edev, f"{tkk} done")
                elif kind == "task_skipped":
                    if tkk:
                        per_task[tkk]["skipped"] += 1; overall["task_skipped"] += 1
                        if edev:
                            per_device_task[edev][tkk]["skipped"] += 1
                            per_device_last_task_result[edev][tkk] = "skipped"
                        add_tl(ev["ts"], edev, f"{tkk} skipped")
                elif kind == "task_skipped_already_done":
                    if tkk:
                        per_task[tkk]["skipped"] += 1
                        overall["task_skipped"] += 1; overall["task_skipped_already_done"] += 1
                        if edev:
                            per_device_task[edev][tkk]["skipped"] += 1
                            per_device_last_task_result[edev][tkk] = "skipped(done)"
                        add_tl(ev["ts"], edev, f"{tkk} skipped (already done)")
                elif kind == "task_skipped_after_max":
                    if tkk:
                        per_task[tkk]["skipped"] += 1
                        overall["task_skipped"] += 1; overall["task_skipped_after_max"] += 1
                        if edev:
                            per_device_task[edev][tkk]["skipped"] += 1
                            per_device_last_task_result[edev][tkk] = "skipped(max)"
                        add_tl(ev["ts"], edev, f"{tkk} skipped after max restarts")
                    note_issue("task_skipped_after_max", e, noisy=True)
                elif kind == "task_failed_max":
                    if tkk:
                        per_task[tkk]["failed"] += 1; per_task[tkk]["max_attempts"] += 1
                        overall["task_failed"] += 1; overall["max_attempts_failures"] += 1
                        if edev:
                            per_device_task[edev][tkk]["failed"] += 1
                            per_device_task[edev][tkk]["max_attempts"] += 1
                            per_device_last_task_result[edev][tkk] = "failed(max)"
                            per_device_last_fail[edev] = f"{tkk}: failed after max restarts"
                        add_tl(ev["ts"], edev, f"{tkk} failed: max_attempts")
                    note_issue("task_failed_max", e, noisy=True)
                elif kind == "task_failed":
                    if tkk:
                        per_task[tkk]["failed"] += 1; overall["task_failed"] += 1
                        if edev:
                            per_device_task[edev][tkk]["failed"] += 1
                            per_device_last_task_result[edev][tkk] = "failed"
                            per_device_last_fail[edev] = f"{tkk}: failed"
                        add_tl(ev["ts"], edev, f"{tkk} failed")
                elif kind == "task_restart":
                    overall["task_restarts"] += 1
                elif kind == "max_attempts":
                    # standalone max-attempts mention not tied to a RESULT line
                    if dedup_event("max_attempts", edev, e):
                        note_issue("task_failed_max", e, noisy=True)

                # ── guards / noisy events ──────────────────────────────────────
                elif kind == "guard_recovery_failed":
                    if dedup_event("guard_recovery", edev, e):
                        overall["guard_recoveries"] += 1
                        if edev: per_device[edev]["guard_recovery"] += 1
                        add_tl(ev["ts"], edev, "GuardRecoveryFailed")
                    note_issue("guard_recovery_failed", e, noisy=True)
                    if tkk and edev:
                        per_device_last_fail[edev] = f"{tkk}: GuardRecoveryFailed"
                elif kind == "guard_recovery":
                    if dedup_event("guard_recovery", edev, e):
                        overall["guard_recoveries"] += 1
                        if edev: per_device[edev]["guard_recovery"] += 1
                        add_tl(ev["ts"], edev, "guard recovery")
                    note_issue("guard_recovery", e, noisy=True)
                elif kind == "connection_issue":
                    if dedup_event("connection_issue", edev, e):
                        overall["connection_issue_events"] += 1
                        if edev: per_device[edev]["connection_issue"] += 1
                    note_issue("connection_issue", e, noisy=True)
                elif kind == "vpn_down":
                    if dedup_event("vpn_down", edev, e):
                        overall["vpn_down_events"] += 1
                        if edev: per_device[edev]["vpn_down"] += 1
                        add_tl(ev["ts"], edev, "VPN down")
                    note_issue("vpn_down", e, noisy=True)
                elif kind == "unexpected_page":
                    if dedup_event("unexpected_page", edev, e):
                        overall["unexpected_page_events"] += 1
                    note_issue("unexpected_page", e, noisy=True)
                elif kind == "adb_offline":
                    if dedup_event("adb_offline", edev, e):
                        overall["adb_offline_events"] += 1
                        add_tl(ev["ts"], edev, "ADB/device offline")
                    note_issue("adb_offline", e, noisy=True)
                elif kind == "emulator_reopen":
                    if dedup_event("emulator_reopen", edev, e):
                        overall["emulator_reopen_events"] += 1
                        if edev: per_device[edev]["emulator_reopen"] += 1
                        add_tl(ev["ts"], edev, "Emulator reopen")
                    note_issue("emulator_reopen", e, noisy=True)
                elif kind == "fatal_apk":
                    if dedup_event("fatal_apk", edev, e):
                        overall["fatal_apk_events"] += 1
                        if edev:
                            per_device[edev]["fatal_apk"] += 1
                            per_device_last_fail[edev] = "FatalAPKError"
                        add_tl(ev["ts"], edev, "FatalAPKError")
                    note_issue("fatal_apk", e, noisy=True)
                elif kind == "internet_emergency":
                    if dedup_event("internet_emergency", edev, e):
                        overall["internet_emergency_events"] += 1
                        if edev: per_device[edev]["internet_down"] += 1
                        add_tl(ev["ts"], edev, "Internet down emergency")
                    note_issue("internet_emergency", e, noisy=True)
                elif kind == "stop_all":
                    note_issue("stop_all", e, noisy=True)
                elif kind == "close_failed":
                    note_issue("close_failed", e, noisy=True)
                elif kind == "no_task_config":
                    note_issue("no_task_config", e, noisy=True)
                elif kind == "empty_task_list":
                    overall["empty_task_list_events"] += 1
                    note_issue("empty_task_list", e, noisy=True)
                elif kind == "skipped_no_pending":
                    dev0 = edev or self._norm_device(e["device"])
                    if dev0 and dedup_event("skipped_no_pending", dev0, e):
                        per_device[dev0]["skipped"] += 1
                    note_issue("skipped_no_pending", e, noisy=True)

            # ── unclassified important line collector (F) ──────────────────────
            if id(e) not in classified_line_ids:
                lvl = (e.get("level") or "").upper()
                low2 = e["line"].lower()
                important = (lvl in ("ERROR", "CRITICAL", "WARNING")
                             or any(w in low2 for w in
                                    ("failed", "exception", "traceback", "timeout",
                                     "offline", "unexpected", "restart", "fatal")))
                if important and len(unclassified) < self.MAX_UNCLASSIFIED_SAMPLES:
                    unclassified.append(self._clean_sample_line(e))

        # ── skipped_no_pending devices overall count (distinct devices) ─────────
        sk = set()
        for cat_key in (("evt", "skipped_no_pending"),):
            for (d0, _c, _m) in dedupe_seen.get(cat_key, set()):
                sk.add(d0)
        overall["skipped_no_pending"] = len(sk)

        # ── roll run records into outcomes ──────────────────────────────────────
        total_runs = completed = failed = stopped = incomplete = 0
        for d, recs in run_records.items():
            for rec in recs:
                total_runs += 1; per_device[d]["runs"] += 1
                res = rec["result"]
                if res == "done":
                    completed += 1; per_device[d]["success"] += 1
                elif res == "stopped":
                    stopped += 1; per_device[d]["stopped"] += 1
                elif res in ("failed", "cfg_build_failed", "proc_start_failed"):
                    failed += 1; per_device[d]["failed"] += 1
                else:
                    # item 2: incomplete/unknown — attach last important event +
                    # likely reason for this device (do NOT mark as failed).
                    incomplete += 1; per_device[d]["incomplete"] += 1
                    li = per_device_last_issue.get(d)
                    if li and li.get("reason"):
                        rec["incomplete_reason"] = li["reason"]
                        rec["incomplete_line"] = li.get("line")
                    else:
                        rec["incomplete_reason"] = "unknown"
                        rec["incomplete_line"] = None
            devices_seen.add(d)

        overall["total_devices_seen"] = len(devices_seen)
        overall["total_device_runs"] = total_runs
        overall["completed_runs"] = completed
        overall["failed_runs"] = failed
        overall["stopped_runs"] = stopped
        overall["incomplete_runs"] = incomplete

        total_attempts = sum(t.get("attempts", 0) for t in per_task.values())
        overall["total_task_attempts"] = total_attempts

        resolved_runs = completed + failed + stopped
        known_success_rate = (completed / resolved_runs * 100.0) if resolved_runs else 0.0
        incl_success_rate = (completed / total_runs * 100.0) if total_runs else 0.0
        task_exec_rate = (overall["task_done"] / total_attempts * 100.0) if total_attempts else 0.0
        eff_denom = overall["task_done"] + overall["task_skipped"]
        effective_rate = (eff_denom / total_attempts * 100.0) if total_attempts else 0.0

        devtype_rows, devtype_unknown = self._devtype_rollup(per_device, devices_seen)

        task_rows = []
        for tkk in sorted(per_task.keys()):
            t = per_task[tkk]; att = t.get("attempts", 0); done = t.get("done", 0)
            sr = (done / att * 100.0) if att else 0.0
            task_rows.append({"task": tkk, "label": task_label.get(tkk, tkk),
                              "attempts": att, "done": done, "skipped": t.get("skipped", 0),
                              "failed": t.get("failed", 0), "restarts": t.get("restarts", 0),
                              "max_attempts": t.get("max_attempts", 0), "success_pct": sr})

        device_detail = None
        if sel_dev:
            pd = per_device.get(sel_dev, {})
            dtasks = []
            for tkk, tc in sorted(per_device_task.get(sel_dev, {}).items()):
                dtasks.append({"task": tkk, "label": task_label.get(tkk, tkk),
                               "attempts": tc.get("attempts", 0), "done": tc.get("done", 0),
                               "skipped": tc.get("skipped", 0), "failed": tc.get("failed", 0),
                               "restarts": tc.get("restarts", 0),
                               "last_result": per_device_last_task_result.get(sel_dev, {}).get(tkk, "-")})
            _succ = pd.get("success", 0); _fail = pd.get("failed", 0); _stop = pd.get("stopped", 0)
            _runs = pd.get("runs", 0); _resolved = _succ + _fail + _stop
            _known_sr = (_succ / _resolved * 100.0) if _resolved else 0.0
            _overall_sr = (_succ / _runs * 100.0) if _runs else 0.0
            # item 2: last issue / incomplete reason for this device
            _li = per_device_last_issue.get(sel_dev) or {}
            _last_issue = per_device_last_fail.get(sel_dev)
            if not _last_issue or _last_issue == "-":
                if _li.get("reason"):
                    _last_issue = f"likely {_li['reason']}"
                    if _li.get("line"):
                        _last_issue += f"  ({_li['line']})"
                else:
                    _last_issue = "-"
            device_detail = {
                "device": sel_dev, "name": self.device_name_map.get(sel_dev, ""),
                "device_type": self.device_type_map.get(sel_dev, "unknown") or "unknown",
                "runs": _runs, "success": _succ,
                "failed": _fail, "stopped": _stop,
                "incomplete": pd.get("incomplete", 0), "skipped": pd.get("skipped", 0),
                "known_success_pct": _known_sr, "overall_success_pct": _overall_sr,
                "prepare_target_app_attempts": pd.get("prepare_target_app_attempts", 0),
                "prepare_target_app_success": pd.get("prepare_target_app_success", 0),
                "prepare_target_app_failures": pd.get("prepare_target_app_failures", 0),
                "emulator_reopen": pd.get("emulator_reopen", 0),
                "vpn_setup": pd.get("vpn_setup", 0), "vpn_connect": pd.get("vpn_connect", 0),
                "vpn_down": pd.get("vpn_down", 0), "target_app_setup": pd.get("target_app_setup", 0),
                "target_app_loading_stuck": pd.get("target_app_loading_stuck", 0),
                "connection_issue": pd.get("connection_issue", 0),
                "guard_recovery": pd.get("guard_recovery", 0),
                "setup_vpn_failures": pd.get("setup_vpn_failures", 0),
                "setup_target_app_failures": pd.get("setup_target_app_failures", 0),
                "fatal_apk": pd.get("fatal_apk", 0), "internet_down": pd.get("internet_down", 0),
                "last_failure": per_device_last_fail.get(sel_dev, "-"),
                "last_issue": _last_issue,                 # item 2
                "tasks": dtasks,
            }

        tl = [t for t in timeline if (not sel_dev or t[1] == sel_dev)]
        tl = [t for t in tl if t[0] is not None]
        tl.sort(key=lambda x: x[0])
        timeline_lines = [f"{self._fmt_ts(ts)}  {dv or '-'}  {txt}" for ts, dv, txt in tl][:600]

        # opened-but-no-tasks
        for d in devices_seen:
            ran_any = any(per_device_task.get(d, {}).get(tk, {}).get("attempts", 0) > 0
                          for tk in per_device_task.get(d, {}))
            opened = (per_device.get(d, {}).get("target_app_setup", 0) > 0
                      or per_device.get(d, {}).get("prepare_target_app_attempts", 0) > 0
                      or per_device.get(d, {}).get("runs", 0) > 0)
            if opened and not ran_any:
                issues_count["device opened but no tasks ran"] += 1
                issues_raw["device opened but no tasks ran"] += 1
                if len(issues_samples["device opened but no tasks ran"]) < 5:
                    issues_samples["device opened but no tasks ran"].append(
                        f"{d}: opened (run/prepare_target_app) but no task attempts in timeframe")

        # NOISY event categories that also report raw line count + affected devices
        NOISY_ISSUE_CATS = {"connection_issue", "guard_recovery", "guard_recovery_failed",
                            "vpn_down", "adb_offline", "loading_stuck", "emulator_reopen",
                            "unexpected_page", "internet_emergency", "fatal_apk"}

        def top_devices_for(cat, limit=5):
            dc = issue_device_counts.get(cat, {})
            ranked = sorted(dc.items(), key=lambda kv: (-kv[1], kv[0]))
            return [{"device": d, "count": c} for d, c in ranked[:limit] if d != "-"]

        issues = []
        for cat in sorted(issues_count.keys()):
            dc = issue_device_counts.get(cat, {})
            devices_affected = len([d for d in dc if d != "-"])
            issues.append({"issue": ISSUE_LABEL.get(cat, cat),
                           "cat": cat,
                           "count": issues_count[cat],
                           "raw_lines": issues_raw.get(cat, issues_count[cat]),
                           "devices_affected": devices_affected,
                           "top_devices": top_devices_for(cat),       # item 3
                           "noisy": cat in NOISY_ISSUE_CATS,           # item 4
                           "samples": list(issues_samples.get(cat, []))})

        notes = []
        if incomplete > 0:
            notes.append(f"Incomplete/unknown runs: {incomplete} "
                         f"(run start seen without RUN COMPLETE / result in files).")
        if devtype_unknown:
            notes.append("DeviceType unknown for some devices because no device "
                         "map was available in logs/controller cache.")
        # item 5: old-log note — incomplete runs but no [RUN-DONE] file lines
        if incomplete > 0 and not run_done_lines_present[0]:
            notes.append("These logs appear to predate [RUN-DONE] file logging. "
                         "Failed/stopped runs may appear as incomplete/unknown. "
                         "New logs will classify failed/stopped more accurately.")
        else:
            notes.append("Run SUCCESS is read from device-log 'RUN COMPLETE' and "
                         "controller '[RUN-DONE]'; runs with neither show as incomplete.")

        return {
            "timeframe": {"start": self._fmt_ts(start) if start else "(all)",
                          "end": self._fmt_ts(end) if end else "(now)",
                          "entries_scanned": len(scoped)},
            "overall": dict(overall),
            "rates": {"run_success_rate": known_success_rate,
                      "run_success_rate_incl_incomplete": incl_success_rate,
                      "task_execution_success_rate": task_exec_rate,
                      "effective_completion_rate": effective_rate},
            "task_rows": task_rows, "devtype_rows": devtype_rows,
            "device_detail": device_detail, "timeline_lines": timeline_lines,
            "issues": issues, "notes": notes, "devices": sorted(devices_seen),
            "unclassified": unclassified,
        }

    # Window (seconds) within which a second result signal for the same device
    # (e.g. device-log "RUN COMPLETE" plus controller "[RUN-DONE]") is treated as
    # belonging to the SAME run record rather than a new run.
    RESULT_MERGE_SECONDS = 5 * 60

    @staticmethod
    def _attach_run_result(run_records, dev, res, ts):
        res = (res or "").lower()
        norm = {"done": "done", "ok": "done", "true": "done", "stopped": "stopped",
                "failed": "failed", "error": "failed", "false": "failed",
                "cfg_build_failed": "failed", "proc_start_failed": "failed"}.get(res, res)
        recs = run_records.get(dev)
        if recs:
            # 1. Prefer the latest still-OPEN run record.
            for rec in reversed(recs):
                if rec["result"] is None:
                    rec["result"] = norm
                    rec["result_ts"] = ts
                    return
            # 2. No open record.  B: avoid double-counting — if the most recent
            #    record was just closed (within RESULT_MERGE_SECONDS), this second
            #    signal belongs to the SAME run, not a new one.
            last = recs[-1]
            last_ts = last.get("result_ts") or last.get("start")
            close_enough = True
            if ts is not None and last_ts is not None:
                try:
                    close_enough = abs((ts - last_ts).total_seconds()) <= LogAnalyzer.RESULT_MERGE_SECONDS
                except Exception:
                    close_enough = True
            if close_enough:
                # Same run.  Keep a definite result over a tentative "done":
                # a failed/stopped signal overrides a prior "done" (the bot logs
                # RUN COMPLETE optimistically before a late failure can appear).
                if last["result"] == norm:
                    return                      # identical → no-op (no double count)
                if last["result"] == "done" and norm in ("failed", "stopped"):
                    last["result"] = norm       # upgrade to the more definite result
                    last["result_ts"] = ts
                return                          # otherwise keep first result, same run
            # 3. Genuinely later → a distinct result-only run record.
            recs.append({"start": ts, "result": norm, "result_ts": ts})
        else:
            run_records.setdefault(dev, []).append({"start": ts, "result": norm, "result_ts": ts})

    def _devtype_rollup(self, per_device, devices_seen):
        from collections import defaultdict
        agg = defaultdict(lambda: {"devices": set(), "runs": 0, "success": 0,
                                   "failed": 0, "stopped": 0, "incomplete": 0})
        any_unknown = False
        for d in devices_seen:
            dt = self.device_type_map.get(d, "") or ""
            if not dt:
                dt = "unknown"; any_unknown = True
            a = agg[dt]; a["devices"].add(d); pd = per_device.get(d, {})
            a["runs"] += pd.get("runs", 0); a["success"] += pd.get("success", 0)
            a["failed"] += pd.get("failed", 0); a["stopped"] += pd.get("stopped", 0)
            a["incomplete"] += pd.get("incomplete", 0)
        rows = []
        for dt, a in sorted(agg.items()):
            resolved = a["success"] + a["failed"] + a["stopped"]
            known_sr = (a["success"] / resolved * 100.0) if resolved else 0.0
            overall_sr = (a["success"] / a["runs"] * 100.0) if a["runs"] else 0.0
            rows.append({"device_type": dt, "devices": len(a["devices"]), "runs": a["runs"],
                         "success": a["success"], "failed": a["failed"], "stopped": a["stopped"],
                         "incomplete": a["incomplete"],
                         # item 1: known = success/(success+failed+stopped);
                         #         overall = success/total runs (incl. incomplete)
                         "known_success_pct": known_sr,
                         "overall_success_pct": overall_sr,
                         "success_pct": known_sr})   # back-compat alias
        return rows, any_unknown

    # ──────────────────────────────────────────────────────────────────────────
    # C. PATTERN COVERAGE REPORT
    # ──────────────────────────────────────────────────────────────────────────
    def pattern_coverage_report(self) -> str:
        lines = []
        lines.append("PATTERN COVERAGE")
        lines.append("=" * 60)
        lines.append(f"Event categories: {len(self.LOG_PATTERNS)}")
        lines.append(f"Noisy (deduped) categories: {len(self.NOISY_CATEGORIES)}")
        lines.append("")
        lines.append("Patterns per category (substring matches, source-derived):")
        for cat in sorted(self.LOG_PATTERNS.keys()):
            n = len(self.LOG_PATTERNS[cat])
            noisy = " [deduped]" if cat in self.NOISY_CATEGORIES else ""
            lines.append(f"  {cat:<24} {n} pattern(s){noisy}")
        lines.append("")
        lines.append("Run-result sources (for completed/failed/stopped accuracy):")
        lines.append("  run_start    ← controller 'RUN START <adb> ...' / device 'device_worker started'")
        lines.append("  run_complete ← device-log '── RUN COMPLETE ──' (success evidence)")
        lines.append("  run_done     ← '[RUN-DONE] adb_id=<id> ok=<bool> result=<text>'")
        lines.append("                 emitted by the run_done queue handler / _on_run_done path")
        lines.append("                 (reliable file record of failed/stopped/done; merged with")
        lines.append("                 RUN COMPLETE for the same run, never double-counted)")
        lines.append("")
        tk = sorted(self.task_keys)
        lines.append(f"Task keys known from TASK_DEFS/SUBTASK_ORDER: {len(tk)}")
        if tk:
            lines.append("  " + ", ".join(tk[:60]))
        lines.append("")
        lines.append("Log sources scanned:")
        for s in self.CONTROLLER_LOGS:
            lines.append(f"  {s}")
        lines.append("  logs/*.log  (per-device)")
        if self.last_scan_stats:
            st = self.last_scan_stats
            lines.append("")
            lines.append(f"Last scan: {st.get('files',0)} files, {st.get('entries',0)} "
                         f"entries, {st.get('elapsed',0):.1f}s, "
                         f"{st.get('cache_hits',0)} cache hit(s)")
        return "\n".join(lines)

    @staticmethod
    def _fmt_ts(ts) -> str:
        try:
            return ts.strftime("%Y-%m-%d %H:%M:%S")
        except Exception:
            return "-"

    def render_text_report(self, result: dict) -> str:
        o = result.get("overall", {}); r = result.get("rates", {}); tf = result.get("timeframe", {})
        L = []
        L.append("=" * 70)
        L.append("TargetApp LOG ANALYSIS")
        L.append(f"Timeframe: {tf.get('start')} → {tf.get('end')}   "
                 f"(entries scanned: {tf.get('entries_scanned')})")
        L.append("=" * 70); L.append(""); L.append("OVERALL")
        ordered = [
            ("total devices seen", "total_devices_seen"),
            ("total device runs", "total_device_runs"),
            ("completed runs", "completed_runs"),
            ("failed runs", "failed_runs"),
            ("stopped runs", "stopped_runs"),
            ("incomplete/unknown runs", "incomplete_runs"),
            ("skipped/no-pending devices", "skipped_no_pending"),
            ("prepare_target_app attempts", "prepare_target_app_attempts"),
            ("prepare_target_app success", "prepare_target_app_success"),
            ("prepare_target_app failure", "prepare_target_app_failure"),
            ("prepare_target_app retries", "prepare_target_app_retries"),
            ("setup_vpn failures", "setup_vpn_failures"),
            ("setup_target_app failures", "setup_target_app_failures"),
            ("total task attempts", "total_task_attempts"),
            ("total task done", "task_done"),
            ("total task skipped", "task_skipped"),
            ("  · skipped already done", "task_skipped_already_done"),
            ("  · skipped after max restarts", "task_skipped_after_max"),
            ("total task failed", "task_failed"),
            ("total task restarts", "task_restarts"),
            ("max_attempts failures", "max_attempts_failures"),
            ("guard recoveries (deduped)", "guard_recoveries"),
            ("vpn down events (deduped)", "vpn_down_events"),
            ("emulator reopen events (deduped)", "emulator_reopen_events"),
            ("connection issue events (deduped)", "connection_issue_events"),
            ("internet emergency events (deduped)", "internet_emergency_events"),
            ("FatalAPKError events (deduped)", "fatal_apk_events"),
        ]
        for label, key in ordered:
            L.append(f"  - {label}: {o.get(key, 0)}")
        L.append("")
        L.append(f"  known finished run success rate      = {r.get('run_success_rate', 0):.1f}%  "
                 f"(completed / resolved runs)")
        L.append(f"  run success incl. incomplete         = {r.get('run_success_rate_incl_incomplete', 0):.1f}%  "
                 f"(completed / all runs)")
        L.append(f"  task execution success rate          = {r.get('task_execution_success_rate', 0):.1f}%  "
                 f"(done / attempts)")
        L.append(f"  effective completion rate            = {r.get('effective_completion_rate', 0):.1f}%  "
                 f"(done+skipped / attempts)")
        for n in result.get("notes", []):
            L.append(f"  NOTE: {n}")
        L.append(""); L.append("TASK SUMMARY")
        L.append(f"  {'task':<20}{'attempts':>9}{'done':>6}{'skip':>6}{'fail':>6}"
                 f"{'restart':>8}{'maxatt':>7}{'succ%':>7}")
        for t in result.get("task_rows", []):
            L.append(f"  {t['label'][:20]:<20}{t['attempts']:>9}{t['done']:>6}"
                     f"{t['skipped']:>6}{t['failed']:>6}{t['restarts']:>8}"
                     f"{t.get('max_attempts',0):>7}{t['success_pct']:>6.0f}%")
        L.append(""); L.append("DEVICETYPE SUMMARY")
        L.append(f"  {'type':<16}{'devices':>8}{'runs':>6}{'succ':>6}{'fail':>6}"
                 f"{'stop':>6}{'inc':>5}{'known%':>8}{'over%':>7}")
        for d in result.get("devtype_rows", []):
            L.append(f"  {str(d['device_type'])[:16]:<16}{d['devices']:>8}{d['runs']:>6}"
                     f"{d['success']:>6}{d['failed']:>6}{d['stopped']:>6}"
                     f"{d.get('incomplete',0):>5}"
                     f"{d.get('known_success_pct', d.get('success_pct',0)):>7.0f}%"
                     f"{d.get('overall_success_pct',0):>6.0f}%")
        L.append("")
        dd = result.get("device_detail")
        if dd:
            L.append("SELECTED DEVICE")
            L.append(f"  device: {dd['device']}  name: {dd.get('name') or '-'}  type: {dd.get('device_type')}")
            L.append(f"  known success: {dd.get('known_success_pct',0):.0f}%   "
                     f"overall success (incl. incomplete): {dd.get('overall_success_pct',0):.0f}%")
            for k in ("runs", "success", "failed", "stopped", "incomplete", "skipped",
                      "prepare_target_app_attempts", "prepare_target_app_success", "prepare_target_app_failures",
                      "emulator_reopen", "vpn_setup", "vpn_connect", "vpn_down",
                      "target_app_setup", "target_app_loading_stuck", "connection_issue",
                      "guard_recovery", "setup_vpn_failures", "setup_target_app_failures",
                      "fatal_apk", "internet_down"):
                L.append(f"    {k}: {dd.get(k, 0)}")
            L.append(f"    last issue / incomplete reason: {dd.get('last_issue', dd.get('last_failure', '-'))}")
            L.append("")
        L.append("POTENTIAL ISSUES")
        if not result.get("issues"):
            L.append("  (none detected)")
        for it in result.get("issues", []):
            if it.get("noisy"):
                L.append(f"  - {it['issue']}: events {it['count']} | raw lines "
                         f"{it.get('raw_lines', it['count'])} | devices affected "
                         f"{it.get('devices_affected', 0)}")
            else:
                extra = (f"  (raw lines: {it['raw_lines']})"
                         if it.get("raw_lines", it["count"]) != it["count"] else "")
                L.append(f"  - {it['issue']}: {it['count']}{extra}")
            top = it.get("top_devices", [])
            if top:
                L.append("      Top devices: "
                         + ", ".join(f"{t['device']} x{t['count']}" for t in top))
            for s in it["samples"]:
                L.append(f"      · {s}")
        L.append("")
        unc = result.get("unclassified", [])
        L.append(f"UNCLASSIFIED IMPORTANT LINES ({len(unc)} shown, max {self.MAX_UNCLASSIFIED_SAMPLES})")
        if not unc:
            L.append("  (none)")
        for s in unc:
            L.append(f"  · {s}")
        L.append("")
        L.append(self.pattern_coverage_report())
        L.append(""); L.append("EVENT TIMELINE")
        for tl in result.get("timeline_lines", []):
            L.append(f"  {tl}")
        return "\n".join(L)


class ControllerUI(_ControllerBase):

    def __init__(self, bot_path: str, demo: bool = False):
        super().__init__()
        self.demo   = demo
        self.bridge = BotBridge(bot_path)

        self.q: Queue = Queue()
        self.conf_devices:   list[dict] = []
        # Currently-online adb ids, refreshed by the optional scan.
        #
        # This is STATUS DECORATION ONLY. Devices are not expected to be running:
        # the Run tab always lists everything configured, and device_worker opens
        # and connects whatever instance you selected before prepare_target_app runs.
        # Gating the Run list on this set would make closed devices unselectable
        # and break the normal workflow.
        self._online_adb_ids: set = set()
        self.active_devices: list[dict] = []
        self._test_devices:  list[dict] | None = None   # set by test scan; None = use active_devices

        # task config per device type
        self.task_config: dict[str, list[str]] = {}
        # Provenance for selections that were NOT empty on disk but became empty
        # after validation (deleted task, missing set, malformed key).
        #
        # Without this, ["set:Missing"] -> [] is indistinguishable from a config
        # the user deliberately left empty, and Run mode starts a setup-only run
        # for a device whose configured work does not exist. Keyed by DeviceType
        # / adb_id, holding the discarded keys so the reason can be shown.
        self._invalid_task_config: dict[str, list[str]] = {}
        self._invalid_multi_tasks: dict[str, list[str]] = {}
        # Canonical Multi-Test selection model. The widgets DISPLAY this; they
        # do not own it. _render_test_multi_panel used to hand every recreated
        # row "all sets + SUBTASK_ORDER", so a scan silently reset an explicit
        # [], a restored selection, or anything the user had just picked.
        #
        # Key PRESENCE is what distinguishes "never chosen" from "chosen empty";
        # an empty list is a real, meaningful value here, so truthiness must
        # never be used to test for it.
        self._multi_task_selections: dict[str, list[str]] = {}
        # Set while a rebuild is skipped because workers are live, so the panel
        # can be refreshed once they finish.
        self._multi_panel_refresh_pending: bool = False
        self._multi_refresh_after_id = None
        # Canonical Test display state, so a rebuild does not erase DONE /
        # FAILED / STOPPED and the last log line. Never holds thread objects.
        self._multi_display_state: dict[str, dict] = {}

        # concurrency
        self._max_concurrent = tk.IntVar(value=5)
        self._run_queue: list[str] = []
        self._running_devs: dict[str, dict] = {}  # adb_id → {process, bridge, stop_event, mp_q}
        self._run_retry_counts: dict[str, int] = {}  # adb_id → retry attempts so far
        # adb_id → the last emulator-close result the controller actually got.
        # A device waiting on an ADB retry has ALREADY had a close attempted
        # (adb_connect_failed is not in _no_close_results), and that close can
        # have failed. Without this, Stop One during the retry window would say
        # "no emulator to close" over a window it knows may still be open.
        # None is a real value here: "a close was attempted but could not be
        # verified" is different from both success and failure.
        self._run_last_close: dict[str, bool | None] = {}
        # adb_id -> {"session_id", "launch_token", "result", "ok"}
        # A terminal result the CONTROLLER owns for one EXACT launch. The fatal
        # route sets it: after run_fatal_stop is accepted, the trigger's
        # terminal wording must not depend on whether the worker's own
        # already-bridged run_done or the controller's synthetic one reaches
        # _on_run_done first. Both normalise to the same value.
        self._run_terminal_override: dict[str, dict] = {}
        self._retry_task_keys_by_device: dict[str, list[str]] = {}  # Retry mode: pre-filtered task lists
        self._shutdown_pending: bool = False        # True once reset shutdown starts; blocks queue pump
        # ── Run session lifecycle ────────────────────────────────────────────
        # A Run is one session from RUN SELECTED until the last device, queued
        # device and delayed ADB retry is gone. Only one may exist at a time:
        # a second start used to overwrite _run_queue and the run metadata
        # underneath a live run, and could queue an already-running device.
        self._run_session_active: bool = False
        # Monotonic id. A delayed retry captures the value current when it was
        # scheduled, so a callback from an older session cannot append its
        # device into a newer session's queue.
        self._run_session_id: int = 0
        # adb_id → {"session_id": int, "token": int, "after_id": object} for a
        # pending 10s ADB retry. Entries keep the session alive and the RUN
        # button disabled, and are cancellable.
        #
        # The TOKEN is what makes this safe. Keying on adb_id alone, a stale
        # callback from session A would pop — and therefore silently destroy —
        # session B's tracking entry for the same device, leaving B's real
        # callback untracked and its session unable to complete. A callback
        # carries the token it was created with and touches nothing unless the
        # currently tracked entry still bears that exact token.
        self._run_retry_after_ids: dict[str, dict] = {}
        self._run_retry_token_seq: int = 0
        # ── Worker launch identity ───────────────────────────────────────────
        # Every launch ATTEMPT gets a unique token. A session id alone is not
        # enough: attempt 1 and attempt 2 after an ADB retry belong to the same
        # session, so attempt 1's late completion would pop attempt 2's live
        # worker out of _running_devs and orphan the process.
        #
        # adb_id → {"session_id": int, "launch_token": int}: the ONLY completion
        # this controller will act on for that device right now.
        self._run_launch_token_seq: int = 0
        self._run_expected_launch: dict[str, dict] = {}
        # The exact launch whose run_done was most recently ACCEPTED, per
        # device. recording_done legitimately arrives after run_done — the grace
        # drain is often the only thing that ever sees the folder/report paths —
        # by which point the expectation has been consumed. Evicted when a newer
        # launch is minted, a new Run starts, a reset happens or the app closes.
        self._run_recent_completion: dict[str, dict] = {}
        # ── Human-readable per-device run log ────────────────────────────────
        # (session_id, adb_id) → HumanDeviceLogContext. Created when the device
        # first participates in an accepted Run session and kept across ADB
        # retries and emergency relaunches, so ONE report tells the whole story.
        # Generation happens on a background daemon after the device is truly
        # terminal; nothing here is on the Run critical path.
        self._human_ctx: dict = {}
        self._human_log_jobs = Queue(maxsize=256)
        self._human_pending_retry_snapshot: list = []
        self._human_log_thread = None
        # RECORDING-ONLY allowance for a launch the hard emergency killed. The
        # emergency invalidates the expectation so the dead worker's run_done,
        # fatal and pause all become stale — but _drain_worker_queue may already
        # have forwarded its recording_done, and that folder/report metadata is
        # real and worth keeping. Consulted ONLY by _recording_identity_matches;
        # never by _run_identity_matches or _run_control_identity_matches.
        self._run_recent_recording_identity: dict[str, dict] = {}
        # Owner of an in-progress hard internet emergency, so a restore message
        # arriving after Stop All (or after a newer run started) is recognised
        # as stale. {"session_id": int, "token": int} or None.
        self._internet_emergency_token_seq: int = 0
        self._internet_emergency_owner: "dict | None" = None

        # run mode device rows
        self._run_rows: dict[str, dict] = {}
        # Canonical Run display state, the exact counterpart of
        # _multi_display_state. The rows DISPLAY this; they do not own it, so a
        # Reload Devices no longer resets RUNNING / queued / RETRY / DONE ✓ /
        # FAILED ✗ / STOPPED / SKIPPED and the device's last log line back to
        # IDLE and "—". Never holds a Process, Event, thread or queue object.
        self._run_display_state: dict[str, dict] = {}
        # Set while a Run-panel rebuild is skipped because a Run session is
        # live; the panel is rebuilt once the session is genuinely idle.
        self._run_panel_refresh_pending: bool = False
        # The rendered BooleanVars. Recreated by every _render_run_device_list,
        # so they are a VIEW, never the source of truth.
        self._run_checks: dict[str, tk.BooleanVar] = {}
        # Canonical Run-tab tick model, on the same principle as
        # _multi_task_selections: it outlives the widgets, so a Reload Devices
        # or a devices_connected refresh cannot silently untick everything and
        # have the next autosave write that loss to disk. Entries persist for
        # devices with no row, so an offline device is restored ticked when it
        # reappears. A missing key simply means False.
        self._run_check_selections: dict[str, bool] = {}

        # test mode
        self._single_stop   = threading.Event()
        self._single_device = tk.StringVar()
        self._test_mode = tk.StringVar(value="single")

        # multi-test rows
        self._multi_rows: dict[str, dict] = {}

        self.skip_var  = tk.BooleanVar(value=False)
        # Optional per-run screen recording + event timeline.  Off by default;
        # when off the bot's recording hooks are a dict lookup and an early return.
        self._record_video = tk.BooleanVar(value=False)
        # adb_id -> recording folder, filled in as devices finish. Read by the
        # Log Analyzer so exports can point at the matching recording.
        self._recording_paths: dict = {}
        self.retry_var = tk.BooleanVar(value=False)   # Retry mode: skip fully-done devices
        self.script_var = tk.StringVar(value=bot_path)

        # FIX 3/4: state cache + task sets managers
        self._state_mgr       = StateManager()
        self._task_sets       = TaskSetsManager()
        self._named_state_mgr = NamedStateManager()   # H: named state save/load

        # ── Controller status cache ───────────────────────────────────────────
        # Persisted immediately after each task completes so latest done-states
        # survive forced process termination and internet loss.
        # Format: { device_id: { task_header: "done"|"error"|"" } }
        self._status_cache: dict[str, dict[str, str]] = {}
        self._pending_sheet_status: dict[str, dict[str, str]] = {}  # to flush when internet returns
        self._status_cache_lock = threading.Lock()
        self._cache_dirty: bool = False       # D: True when pending writes have not been synced
        self._fatal_run_stop: bool = False    # C: True after FatalAPKError received
        # E: serialises _flush_pending_sheet_status so overlapping sync threads
        # (60s tick + Stop All + fatal + close + internet-restore) never collide.
        self._sheet_sync_lock = threading.Lock()
        self._load_status_cache()

        # ── Internet-down monitor ─────────────────────────────────────────────
        self._internet_monitor_thread: threading.Thread | None = None
        self._internet_monitor_stop   = threading.Event()
        self._internet_down_emergency = False   # True while emergency stop is active

        # ── Host-internet PAUSE tier (primary response to host internet down) ──
        # Pausing is deliberately separate from the emergency stop below.  A host
        # outage is not the device's fault, so killing subprocesses and closing
        # emulators only destroys progress that would have survived the outage.
        # While paused we hold everything in place: no new launches, no queue
        # draining, no emulator closes, no subprocess kills, no counter changes.
        # The emergency path is retained for manual Stop, controller shutdown and
        # user-requested hard reset only.
        self._internet_pause_active     = False
        self._internet_pause_started_at = 0.0
        self._internet_pause_devices: set = set()   # devices that reported the outage
        self._internet_pause_thread: threading.Thread | None = None
        # Exact owner of the CURRENT pause. The poll thread can outlive the
        # pause it was started for — Stop All, a reset, or simply a later pause
        # — so its resume must prove it belongs to the pause that is running
        # now, or it would release workers and pump a queue that a newer pause
        # is deliberately holding.
        self._internet_pause_token_seq: int = 0
        self._internet_pause_owner: "dict | None" = None
        self._internet_killed_ids: set = set()   # adb_ids killed during internet emergency
        self._internet_restart_ids: set = set()  # running + queued + retrying at emergency
        # Kept apart because restoration treats them differently: a QUEUED
        # device never ran prepare_target_app, so its task statuses say nothing about
        # whether it still needs to run.
        self._internet_running_ids: set = set()
        self._internet_queued_ids: set = set()
        self._internet_retry_ids: set = set()
        self._current_run_selected_ids: set = set()    # exact IDs selected for current run
        self._current_run_selected_order: list = []    # exact order selected for current run

        # ── Sync Devices state ────────────────────────────────────────────────
        self._sync_result: dict = {}

        # ── VPN Monitor state ─────────────────────────────────────────────────
        self._vpn_stop_event   = threading.Event()
        self._vpn_stop_event.set()          # starts as "not running"
        self._vpn_threads:     list[threading.Thread] = []
        self._vpn_last_status: dict[str, bool | None] = {}
        self._vpn_device_rows: dict[str, dict]        = {}

        # ── Screenshotor state ────────────────────────────────────────────────
        # Standalone UI helper: scans open devices once, then screenshots them
        # on demand (S / button).  Completely independent of the run/cache/sheet
        # machinery — it never touches _running_devs, the run queue, or sync.
        self._ss_active   = False
        self._ss_devices: list[dict] = []          # [{adb_id, friendly, folder}]
        self._ss_stats:   dict[str, dict] = {}      # adb_id → stats dict
        self._ss_hashes_by_device: dict[str, set] = {}   # adb_id → {sha256,…} (seeded from disk)
        self._ss_records_by_device: dict[str, list] = {}  # adb_id → [visual record,…]
        self._ss_last_hash_by_device: dict[str, str] = {}
        self._ss_folder_by_device: dict[str, str] = {}   # adb_id → friendly folder name
        self._ss_rows:    dict[str, dict] = {}      # adb_id → table row widgets/vars
        self._ss_mini_window = None
        self._ss_mini_lbl = None
        self._ss_busy     = False                   # True while a batch is in flight
        self._ss_session_dir = ""                   # base screenshots dir
        # Thread-safety for shared screenshot state mutated by the batch worker:
        self._ss_lock = threading.Lock()
        # Set by Stop to cancel an in-flight batch between devices:
        self._ss_stop_event = threading.Event()
        # Session id — bumped on Start/Stop/Clear so a late result from an old
        # batch worker is recognised as stale and ignored by the _poll handlers.
        self._ss_session_id = 0
        # True while a device scan is in flight (blocks overlapping scans).
        self._ss_scanning = False
        # Page tagging: dropdown var (set when tab builds), cached page-name list,
        # and the per-(device,page) saved counts used for the status table.
        self._ss_page_var = None
        self._ss_mini_page_var = None
        self._ss_page_names = []                    # loaded from screenshot_pages.json
        self._ss_page_status: dict[str, dict] = {}  # page → {done:[adb..], missing:[adb..]}
        self._ss_retry_btn = None                   # Retry Failed button (set on tab build)
        self._ss_mini_retry_btn = None              # mini-window Retry Failed button
        self._ss_index_dirty = False                # hash index needs saving at batch end
        self._ss_page_status_dirty = False          # page status needs rebuild at batch end

        # ── Data Extractor state (trial; manual image → page detect → OCR) ────
        # Controller-side only.  Never touches devices, run, cache, or sheets.
        self._de_image_path = ""
        self._de_image = None            # PIL.Image of the uploaded screenshot
        self._de_detected_page = None
        self._de_page_confidence = 0.0
        self._de_last_result = None
        self._de_busy = False
        self._de_easyocr_reader = None   # lazy-loaded EasyOCR reader (or False)
        self._de_pages_cache = None      # ((path, mtime), {name: spec}) cache
        self._de_current_row = None      # persistent combined output row (set in tab build)
        self._de_filled_pages = []        # pages that have contributed to the row

        self.title("TargetApp Bot Controller v7")
        self.configure(bg=BG_BASE)
        w, h = 1620, 960
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        self.geometry(f"{w}x{h}+{(sw-w)//2}+{(sh-h)//2}")
        self.minsize(1400, 800)

        self.protocol("WM_DELETE_WINDOW", self._on_close)

        # Feature 6: show loading screen first
        self._loading_frame = tk.Frame(self, bg=BG_BASE)
        self._loading_frame.place(relx=0, rely=0, relwidth=1, relheight=1)
        self._loading_label = tk.Label(self._loading_frame,
                                        text="⚓ Loading TargetApp Bot Controller…",
                                        font=(F, 16, "bold"), bg=BG_BASE, fg=PRI)
        self._loading_label.place(relx=0.5, rely=0.45, anchor="center")
        self._loading_status = tk.Label(self._loading_frame,
                                         text="Importing bot module and reading sheet…",
                                         font=(F, 10), bg=BG_BASE, fg=FG_DIM)
        self._loading_status.place(relx=0.5, rely=0.52, anchor="center")

        self._poll()

        if demo:
            self.after(300, self._finish_loading_demo)
        else:
            threading.Thread(target=self._startup_loader, daemon=True).start()

    def _startup_loader(self):
        try:
            self.q.put(("loading_msg", "Importing bot module…"))
            self.bridge.load_bot()
            # B: Daily reset MUST run before any cache seeding.
            # run_daily_reset() reads the sheet, applies reset if needed, then
            # re-reads the sheet fresh and seeds all bot globals from clean values.
            # We must NOT call refresh_sheet() before this — it would seed stale
            # "done" values into cache before the reset clears them.
            self.q.put(("loading_msg", "Checking daily reset…"))
            _ui_log.info("[startup] checking daily reset before cache load")
            did_reset = self.bridge.run_daily_reset()
            if did_reset:
                self.q.put(("loading_msg", "Daily reset done — clearing stale cache…"))
                _ui_log.info("[startup] daily reset applied; cache seeded from fresh sheet")
                # Fix 1: After reset the sheet is clean.  Wipe any stale "done"
                # values that were loaded from controller_status_cache.json at
                # __init__ time, then rebuild _status_cache from the fresh
                # post-reset sheet data that run_daily_reset() already loaded.
                with self._status_cache_lock:
                    self._status_cache = {}
                    self._pending_sheet_status = {}
                    self._cache_dirty = False
                self._persist_status_cache()
                # Seed _status_cache from the fresh rows_by_device snapshot so
                # Retry mode has accurate done-state without needing a sheet read.
                self._rebuild_status_cache_from_sheet()
                # NOTE: do NOT call _apply_pending_sheet_status_to_local_cache here —
                # _pending_sheet_status was intentionally cleared above (nothing to overlay).
                _ui_log.info("[startup] stale local cache cleared; rebuilt from post-reset sheet")
            else:
                _ui_log.info("[startup] daily reset not needed; cache seeded from sheet")
                # Seed _status_cache from current sheet values.
                self._rebuild_status_cache_from_sheet()
                # Overlay any pending writes loaded from disk onto _status_cache and
                # rows_by_device.  This ensures Retry sees up-to-date done-statuses
                # even before the first 1-minute sync flush writes them to Sheets.
                # If the controller previously crashed before syncing, pending writes
                # carry values newer than what the sheet shows.
                self._apply_pending_sheet_status_to_local_cache()
                _ui_log.info("[startup] cache built from sheet + pending-write overlay")
            # run_daily_reset() already read and seeded from the current sheet.
            # Do NOT call refresh_sheet() again here — it would cause a double read
            # and can re-introduce stale values between the reset and the seed.
            self.q.put(("loading_msg", "Scanning BlueStacks conf…"))
            devs = self.bridge.list_conf_devices()
            self.q.put(("startup_done", devs, None))
        except Exception as ex:
            self.q.put(("startup_done", [], str(ex)))

    def _finish_loading_demo(self):
        self._loading_frame.destroy()
        self._build()
        self._setup_mousewheel()
        self._setup_shortcuts()
        self._tick_reset_countdown()
        self._log("⚠  DEMO MODE — bot script not loaded", "warn")
        self.conf_devices = DEMO_CONF
        self._discover_task_config(DEMO_CONF)
        self._render_run_device_list()
        self._build_task_config_tab()
        # Simulate device connection after short delay
        self.after(400, lambda: self.q.put(("devices_connected", DEMO_ACTIVE)))

    def _on_startup_done(self, devs, error):
        self.conf_devices = devs
        self._discover_task_config(devs)

        # Report which BlueStacks conf we resolved, and from which candidates.
        # Path logic lives in the bot module only — the controller never
        # duplicates it, it just reports what the bot resolved.
        try:
            bot = self.bridge.load_bot()
            status = bot.log_bluestacks_conf_status(
                log_fn=lambda msg, tag="dim": self._log(msg, tag))
            _multi_log.info(
                f"[CONF] candidates="
                f"{[(pth, ex) for pth, ex in status['candidates']]} "
                f"selected={status['selected']!r} found={status['found']}"
            )
            if not status["found"]:
                self._log("Device scan will not work until BlueStacks config "
                          "is found at one of the paths above.", "err")
        except Exception as exc:
            self._log(f"Could not resolve BlueStacks config path: {exc}", "warn")

        if error:
            self._log(f"⚠  Startup error: {error}", "err")
            self._log("Running in limited mode — retry with Reload Sheet", "warn")
        else:
            self._log(f"✓  Loaded {len(devs)} instance(s)", "ok")
        self._render_run_device_list()
        self._render_test_multi_panel()
        self._draw_sheet_grid()
        self._build_task_config_tab()

    def _mark_invalid_config(self, dt: str, validation: dict) -> None:
        """
        Remember a DeviceType whose stored selection had entries but validated
        to nothing. An explicitly empty selection clears the marker, because
        "the user chose no tasks" is a legitimate setup-only run.
        """
        v = validation or {}
        if v.get("had_input") and not v.get("valid"):
            self._invalid_task_config[dt] = list(v.get("invalid") or [])
        else:
            self._invalid_task_config.pop(dt, None)

    def _mark_invalid_multi(self, adb_id: str, validation: dict) -> None:
        """Same, per device, for the multi-panel selections."""
        v = validation or {}
        if v.get("had_input") and not v.get("valid"):
            self._invalid_multi_tasks[adb_id] = list(v.get("invalid") or [])
        else:
            self._invalid_multi_tasks.pop(adb_id, None)

    def _clear_invalid_multi(self, adb_id: str) -> None:
        """
        Called when the user EDITS a Multi-Test selection, including clearing it.

        After an explicit clear the selection is *explicitly* empty, so
        Multi-Test still reports no_runnable_tasks — but as "empty", not as
        "stale/invalid".
        """
        if self._invalid_multi_tasks.pop(adb_id, None) is not None:
            _multi_log.info(f"[TASKS] invalid multi-test marker cleared for "
                            f"{adb_id} — selection edited by the user")

    def _clear_invalid_config(self, dt: str) -> None:
        """
        Called when the user EDITS a Task Config, including clearing it.

        An explicit empty selection must mean setup-only again, so the stale
        marker from a previous load has to go.
        """
        if self._invalid_task_config.pop(dt, None) is not None:
            _multi_log.info(f"[TASKS] invalid-config marker cleared for {dt!r} "
                            f"— selection edited by the user")

    def _discover_task_config(self, devs: list[dict]):
        """Scan devices and initialise task_config with all tasks enabled per type."""
        types_seen = set()
        for d in devs:
            types_seen.add(d.get("device_type", "") or "")
        for row in self.bridge.rows_by_device.values():
            types_seen.add(row.get("device_type", "") or "")
        for dt in types_seen:
            if dt not in self.task_config:
                self.task_config[dt] = []  # FIX 2: no tasks selected by default

    # ══════════════════════════════════════════════════════════════════════════
    # BUILD
    # ══════════════════════════════════════════════════════════════════════════
    def _build(self):
        self.configure(bg=BG_BASE)
        self.rowconfigure(0, weight=0)
        self.rowconfigure(1, weight=1)
        self.rowconfigure(2, weight=0)
        self.columnconfigure(0, weight=1)

        self._build_header()

        style = ttk.Style(self)
        style.theme_use("default")
        style.configure("Dark.TNotebook", background=BG_MID, borderwidth=0, tabmargins=[0, 0, 0, 0])
        style.configure("Dark.TNotebook.Tab",
                        background=BG_MID, foreground=FG_DIM,
                        font=(F, 8, "bold"), padding=[14, 6], borderwidth=0)
        style.map("Dark.TNotebook.Tab",
                  background=[("selected", PRI)],
                  foreground=[("selected", "#FFFFFF")])

        # Treeview style for Sheet tab
        style.configure("Sheet.Treeview",
                        background=BG_CELL, foreground=FG_MAIN, fieldbackground=BG_CELL,
                        font=FMS, rowheight=24, borderwidth=0)
        style.configure("Sheet.Treeview.Heading",
                        background=BG_MID, foreground=PRI, font=FSB, borderwidth=0)
        style.map("Sheet.Treeview",
                  background=[("selected", "#2A2A50")],
                  foreground=[("selected", FG_MAIN)])

        self._nb = ttk.Notebook(self, style="Dark.TNotebook")
        self._nb.grid(row=1, column=0, sticky="nsew")

        self._tab_run       = tk.Frame(self._nb, bg=BG_BASE)
        self._tab_test      = tk.Frame(self._nb, bg=BG_BASE)
        self._tab_taskconf  = tk.Frame(self._nb, bg=BG_BASE)
        self._tab_sheet     = tk.Frame(self._nb, bg=BG_BASE)
        self._tab_sync      = tk.Frame(self._nb, bg=BG_BASE)
        self._tab_vpn       = tk.Frame(self._nb, bg=BG_BASE)
        self._tab_tasksets  = tk.Frame(self._nb, bg=BG_BASE)   # FIX 4
        self._tab_issues    = tk.Frame(self._nb, bg=BG_BASE)   # FIX 7
        self._tab_log_analyzer = tk.Frame(self._nb, bg=BG_BASE)   # Log Analyzer
        self._tab_screenshotor = tk.Frame(self._nb, bg=BG_BASE)   # Screenshotor
        self._tab_data_extractor = tk.Frame(self._nb, bg=BG_BASE)   # Data Extractor

        self._nb.add(self._tab_run,      text=" ▶  Run ")
        self._nb.add(self._tab_test,     text=" ⚙  Test ")
        self._nb.add(self._tab_taskconf, text=" ☰  Task Config ")
        self._nb.add(self._tab_sheet,    text=" ≡  Sheet ")
        self._nb.add(self._tab_sync,     text=" ⟳  Sync Devices ")
        self._nb.add(self._tab_vpn,      text=" 📡  VPN Monitor ")
        self._nb.add(self._tab_tasksets, text=" 📦  Task Sets ")
        self._nb.add(self._tab_issues,   text=" ⚠  Issues ")
        self._nb.add(self._tab_log_analyzer, text=" 📊  Log Analyzer ")
        self._nb.add(self._tab_screenshotor, text=" 📸  Screenshotor ")
        self._nb.add(self._tab_data_extractor, text=" 🧾  Data Extractor ")

        self._build_run_tab()
        self._build_test_tab()
        self._build_task_config_tab()
        self._build_sheet_tab()
        self._build_sync_devices_tab()
        self._build_vpn_monitor_tab()
        self._build_task_sets_tab()   # FIX 4
        self._build_issues_tab()      # FIX 7
        self._build_log_analyzer_tab()   # Log Analyzer
        self._build_screenshotor_tab()   # Screenshotor
        self._build_data_extractor_tab() # Data Extractor
        self._build_log_strip()

    # ── header ─────────────────────────────────────────────────────────────────
    def _build_header(self):
        bar = tk.Frame(self, bg="#0D0D1A", height=50)
        bar.grid(row=0, column=0, sticky="ew")
        bar.pack_propagate(False)

        tk.Label(bar, text="⚓", font=(F, 15, "bold"), bg="#0D0D1A", fg=PRI).pack(side=tk.LEFT, padx=(10, 4))
        tk.Label(bar, text="TARGET APPLICATION  ·  BOT CONTROLLER  v7",
                 font=(F, 11, "bold"), bg="#0D0D1A", fg=FG_MAIN).pack(side=tk.LEFT, padx=(0, 18))

        tk.Frame(bar, bg="#2A2A45", width=1).pack(side=tk.LEFT, fill=tk.Y, padx=(12, 8), pady=8)

        tk.Label(bar, text="RELOAD:", font=(F, 8, "bold"), bg="#0D0D1A", fg=FG_DIM).pack(side=tk.LEFT, padx=(0, 4))
        for lbl, cmd in [("Code", self._reload_code), ("Sheet", self._reload_sheet),
                          ("Devices", self._reload_devices)]:
            tk.Button(bar, text=lbl, command=cmd,
                      bg=BG_CELL, fg=FG_MAIN, font=(F, 8),
                      relief=tk.FLAT, padx=8, pady=4, bd=0,
                      cursor="hand2", activebackground=BG_MID).pack(side=tk.LEFT, padx=2)

        tk.Frame(bar, bg="#2A2A45", width=1).pack(side=tk.LEFT, fill=tk.Y, padx=(8, 4), pady=8)

        tk.Label(bar, text="Bot:", font=(F, 8), bg="#0D0D1A", fg=FG_DIM).pack(side=tk.LEFT, padx=(4, 3))
        tk.Entry(bar, textvariable=self.script_var, font=(FM, 8),
                 bg=BG_CELL, fg=FG_MAIN, insertbackground=FG_MAIN,
                 relief=tk.FLAT, width=30, bd=0).pack(side=tk.LEFT, padx=2)

        # Right side
        # FIX 3: Load Previous State button
        tk.Frame(bar, bg="#2A2A45", width=1).pack(side=tk.RIGHT, fill=tk.Y, padx=(4, 8), pady=8)
        tk.Button(bar, text="⟳ Load State", command=self._load_state,
                  bg=ACC_BLUE, fg="white", font=(F, 8, "bold"),
                  relief=tk.FLAT, padx=8, pady=4, bd=0, cursor="hand2",
                  activebackground=PRI).pack(side=tk.RIGHT, padx=2)

        self._global_status = tk.Label(bar, text="● IDLE", font=(F, 8, "bold"),
                                        bg="#0D0D1A", fg=FG_DIM)
        self._global_status.pack(side=tk.RIGHT, padx=10)

        self._reset_var = tk.StringVar(value="⏱ --:--")
        self._reset_lbl = tk.Label(bar, textvariable=self._reset_var,
                                    font=(F, 8), bg="#0D0D1A", fg=FG_DIM)
        self._reset_lbl.pack(side=tk.RIGHT, padx=8)

    # ══════════════════════════════════════════════════════════════════════════
    # TAB: RUN
    # ══════════════════════════════════════════════════════════════════════════
    def _build_run_tab(self):
        tab = self._tab_run
        tab.rowconfigure(0, weight=1)
        tab.columnconfigure(0, weight=1)
        tab.columnconfigure(1, weight=0)
        tab.columnconfigure(2, weight=1)

        # Left: device list
        left = tk.Frame(tab, bg=BG_PANEL)
        left.grid(row=0, column=0, sticky="nsew", padx=(6, 3), pady=6)
        left.rowconfigure(1, weight=1)
        left.columnconfigure(0, weight=1)

        hdr = tk.Frame(left, bg=BG_MID)
        hdr.grid(row=0, column=0, sticky="ew")
        tk.Label(hdr, text="DEVICES", font=FH, bg=BG_MID, fg=PRI, padx=8, pady=6).pack(side=tk.LEFT)
        _btn(hdr, "Deselect All", lambda: self._run_sel_all(False), bg=BG_CELL, fg=FG_DIM, font=FS, padx=6, pady=2).pack(side=tk.RIGHT, padx=2)
        _btn(hdr, "Select All", lambda: self._run_sel_all(True), bg=BG_CELL, fg=ACC_BLUE, font=FS, padx=6, pady=2).pack(side=tk.RIGHT, padx=2)

        # Scrollable device list
        wrap = tk.Frame(left, bg=BG_PANEL)
        wrap.grid(row=1, column=0, sticky="nsew")
        wrap.rowconfigure(0, weight=1)
        wrap.columnconfigure(0, weight=1)
        self._run_canvas = tk.Canvas(wrap, bg=BG_PANEL, bd=0, highlightthickness=0)
        sb = tk.Scrollbar(wrap, orient=tk.VERTICAL, command=self._run_canvas.yview, bg=BG_MID, troughcolor=BG_MID)
        self._run_canvas.configure(yscrollcommand=sb.set)
        sb.grid(row=0, column=1, sticky="ns")
        self._run_canvas.grid(row=0, column=0, sticky="nsew")
        self._run_inner = tk.Frame(self._run_canvas, bg=BG_PANEL)
        self._run_win_id = self._run_canvas.create_window((0, 0), window=self._run_inner, anchor=tk.NW)
        self._run_inner.bind("<Configure>", lambda e: self._run_canvas.configure(scrollregion=self._run_canvas.bbox("all")))
        self._run_canvas.bind("<Configure>", lambda e: self._run_canvas.itemconfig(self._run_win_id, width=e.width))

        # sep
        tk.Frame(tab, bg="#2A2A40", width=1).grid(row=0, column=1, sticky="ns", pady=4)

        # Right: controls + log
        right = tk.Frame(tab, bg=BG_PANEL)
        right.grid(row=0, column=2, sticky="nsew", padx=(3, 6), pady=6)
        right.rowconfigure(5, weight=1)   # log panel is now row 5
        right.columnconfigure(0, weight=1)

        # Controls row
        ctrl = tk.Frame(right, bg=BG_MID)
        ctrl.grid(row=0, column=0, sticky="ew")
        self._run_btn = _btn(ctrl, "▶ RUN SELECTED", self._run_start_selected, bg=PRI, fg="white", font=FH)
        self._run_btn.pack(side=tk.LEFT, padx=8, pady=8)
        _btn(ctrl, "■ STOP ALL", self._run_stop_all, bg=CLR_FAIL, fg=FG_ERR, font=FNB).pack(side=tk.LEFT, padx=4)

        tk.Frame(ctrl, bg="#2A2A45", width=1).pack(side=tk.LEFT, fill=tk.Y, padx=8, pady=6)

        tk.Label(ctrl, text="Max concurrent:", font=FS, bg=BG_MID, fg=FG_DIM).pack(side=tk.LEFT)
        tk.Spinbox(ctrl, from_=1, to=50, textvariable=self._max_concurrent,
                   width=4, font=FMN, bg=BG_CELL, fg=FG_MAIN, relief=tk.FLAT,
                   buttonbackground=BG_MID).pack(side=tk.LEFT, padx=4)

        tk.Frame(ctrl, bg="#2A2A45", width=1).pack(side=tk.LEFT, fill=tk.Y, padx=8, pady=6)
        tk.Checkbutton(ctrl, text="Skip prepare_target_app", variable=self.skip_var,
                       font=FS, bg=BG_MID, fg=FG_DIM, selectcolor=BG_CELL,
                       activebackground=BG_MID).pack(side=tk.LEFT, padx=4)

        tk.Checkbutton(ctrl, text="Retry", variable=self.retry_var,
                       font=FS, bg=BG_MID, fg=FG_DIM, selectcolor=BG_CELL,
                       activebackground=BG_MID).pack(side=tk.LEFT, padx=4)

        tk.Checkbutton(ctrl, text="Record video", variable=self._record_video,
                       font=FS, bg=BG_MID, fg=FG_DIM, selectcolor=BG_CELL,
                       activebackground=BG_MID).pack(side=tk.LEFT, padx=4)
        _btn(ctrl, "📁 Recordings", lambda: self._open_recordings_folder(),
             bg=BG_CELL, fg=FG_DIM, font=FS).pack(side=tk.LEFT, padx=4)

        # H: Named state panel at row 1
        self._build_named_states_ui(right, row=1)

        # Queue status (row 2)
        self._queue_label = tk.Label(right, text="Queue: idle", font=FS, bg=BG_PANEL, fg=FG_DIM, anchor=tk.W, padx=8)
        self._queue_label.grid(row=2, column=0, sticky="ew")

        tk.Frame(right, bg=BG_CELL, height=1).grid(row=3, column=0, sticky="ew")

        # Sync-cache status (row 4)
        self._sync_status_var = tk.StringVar(value="")
        tk.Label(right, textvariable=self._sync_status_var, font=FS,
                 bg=BG_PANEL, fg=FG_DIM, anchor=tk.W, padx=8).grid(row=4, column=0, sticky="ew")

        # Log panel (row 5)
        self._run_log = scrolledtext.ScrolledText(right, height=20, font=(FM, 8),
                                                    bg="#0A0A14", fg=FG_MAIN,
                                                    state=tk.DISABLED, wrap=tk.WORD,
                                                    relief=tk.FLAT, padx=10, pady=6)
        self._run_log.grid(row=5, column=0, sticky="nsew", padx=4, pady=4)
        for tag, fg in [("ok", "#5CCC5C"), ("warn", "#F9A825"), ("err", FG_ERR), ("dim", FG_DIM), ("info", ACC_BLUE)]:
            self._run_log.tag_config(tag, foreground=fg)

    def _run_session_busy(self) -> bool:
        """
        The ONE authoritative answer to "is a Run in progress?".

        Deliberately broader than `_running_devs`: a device waiting out its 10s
        ADB retry has no worker and is not in the queue, yet the session very
        much still owns it. Treating that gap as idle is what let a rebuild — or
        a second RUN SELECTED — land in the middle of a run.
        """
        return bool(getattr(self, "_run_session_active", False)
                    or self._running_devs
                    or self._run_queue
                    or getattr(self, "_run_retry_after_ids", None)
                    # An expected launch is pending Run work even with no
                    # _running_devs entry: cfg_build_failed and
                    # proc_start_failed both mint one and queue a run_done
                    # without ever registering a worker.
                    or getattr(self, "_run_expected_launch", None)
                    or self._hard_emergency_owns_session())

    def _hard_emergency_owns_session(self) -> bool:
        """
        Is a hard internet emergency still holding this Run open?

        During the outage every worker is killed and the queue cleared, so
        _running_devs, _run_queue and _run_retry_after_ids are all empty — the
        run looks finished. It is not: the wait thread will restore it. Without
        this the session would end mid-outage, re-enable RUN SELECTED, fire the
        "final" sheet sync and let the deferred rebuild destroy the rows the
        restore is about to need.
        """
        owner = getattr(self, "_internet_emergency_owner", None)
        if not owner:
            return False
        return owner.get("session_id") == getattr(self, "_run_session_id", 0)

    def _cancel_hard_internet_emergency(self, reason: str = "") -> bool:
        """
        Intentionally abandon a hard internet emergency.

        Only for routes that genuinely end the run — Stop All, fatal stop,
        controller close, safe reset. Invalidating the owner is what lets the
        session finish; the old wait thread may still enqueue its now-stale
        identity later, which the restore handler will reject as a no-op.
        """
        owner = getattr(self, "_internet_emergency_owner", None)
        if not owner and not getattr(self, "_internet_down_emergency", False):
            return False
        _multi_log.info(
            f"[INTERNET] hard emergency ownership invalidated (was {owner})"
            f"{' — ' + reason if reason else ''}")
        self._internet_emergency_owner = None
        self._internet_down_emergency = False
        self._internet_killed_ids = set()
        self._internet_restart_ids = set()
        self._internet_running_ids = set()
        self._internet_queued_ids = set()
        self._internet_retry_ids = set()
        return True

    def _human_snapshot_pending_retries(self) -> list:
        """
        Devices whose ONLY claim on the run is a pending ADB retry.

        They have no worker, so no run_done will ever arrive for them. Captured
        before _cancel_run_retries empties the dict, so the abandonment routes
        can still finalize their human reports.
        """
        try:
            snap = [a for a in list(getattr(self, "_run_retry_after_ids", {}) or {})
                    if a not in self._running_devs]
        except Exception:
            snap = []
        self._human_pending_retry_snapshot = snap
        return snap


    def _cancel_run_retries(self, reason: str = "") -> int:
        """
        Cancel every pending delayed ADB retry and forget it.

        Called from every route that abandons a session — Stop All, fatal stop,
        controller close, safe reset, and defensively when a new session starts.
        Cancelling the Tk callback is not enough on its own: the id must leave
        _run_retry_after_ids too, or _run_session_busy() reports a session that
        no longer exists and the RUN button never re-enables.
        """
        pending = dict(getattr(self, "_run_retry_after_ids", {}) or {})
        if not pending:
            return 0
        for adb_id, entry in pending.items():
            try:
                self.after_cancel(entry.get("after_id"))
            except Exception:
                pass
        self._run_retry_after_ids.clear()
        _multi_log.info(
            f"[RUN-SESSION] cancelled {len(pending)} pending ADB retry callback(s)"
            f"{' — ' + reason if reason else ''}: {sorted(pending)}")
        return len(pending)

    def _cancel_one_run_retry(self, adb_id: str, reason: str = "") -> bool:
        """
        Cancel a single device's pending ADB retry, if it has one.

        Returns True only when an entry was actually removed — Stop One uses
        that to tell "this device was waiting on a retry" from "this device had
        nothing pending", which is the difference between a stop that completes
        the session and one that does nothing.
        """
        entry = (getattr(self, "_run_retry_after_ids", None) or {}).pop(adb_id, None)
        if entry is None:
            return False
        try:
            self.after_cancel(entry.get("after_id"))
        except Exception:
            # after_cancel can fail; the token check in _run_requeue is what
            # actually makes the orphaned callback harmless.
            pass
        _multi_log.info(
            f"[RUN-SESSION] cancelled pending ADB retry for {adb_id} "
            f"(session={entry.get('session_id')} token={entry.get('token')})"
            f"{' — ' + reason if reason else ''}")
        return True

    def _finish_run_session_if_idle(self) -> bool:
        """
        End the Run session — but only once there is genuinely nothing left.

        `_running_devs` going empty is NOT the end of a run: a device waiting
        out its ADB retry has no worker for those ten seconds. Ending the
        session there would re-enable RUN SELECTED mid-run and let the deferred
        rebuild destroy the rows the retry is about to need.

        Returns True ONLY when this call ended an ACTIVE session — i.e. on the
        active→inactive transition itself. Every idle-but-already-finished call
        returns False, which is what makes it safe to hang the end-of-run sheet
        sync off the return value: exactly one caller can ever see True per
        session, so the sync cannot fire twice, fire between ADB attempts, or
        fire from a duplicate run_done.
        """
        if self._running_devs or self._run_queue \
                or getattr(self, "_run_retry_after_ids", None):
            return False
        # A completion is queued but not yet processed. cfg_build_failed and
        # proc_start_failed never register a worker, so _running_devs is already
        # empty when _run_start_selected asks whether the run is over — ending
        # it here fired the "final" sync and re-enabled RUN SELECTED before the
        # failure had even been handled. The exact accepted run_done consumes
        # its expectation BEFORE calling back here, so this cannot deadlock.
        if getattr(self, "_run_expected_launch", None):
            _multi_log.info(
                f"[RUN-SESSION] session {self._run_session_id} still awaiting "
                f"{len(self._run_expected_launch)} completion(s): "
                f"{sorted(self._run_expected_launch)}")
            return False
        # A live hard emergency owns this run even though all three containers
        # are empty — it emptied them itself and intends to refill them.
        if self._hard_emergency_owns_session():
            _multi_log.info(
                f"[RUN-SESSION] session {self._run_session_id} held open by the "
                f"hard internet emergency {self._internet_emergency_owner}")
            return False
        was_active = getattr(self, "_run_session_active", False)
        self._run_session_active = False
        try:
            self._run_btn.configure(state=tk.NORMAL)
        except Exception:
            pass
        # The rebuild a scan deferred mid-run happens now, exactly once. Terminal
        # badges and last-log lines survive it: the rows are reseeded from
        # _run_display_state.
        if getattr(self, "_run_panel_refresh_pending", False):
            self._run_panel_refresh_pending = False
            _multi_log.info("[RUN-TAB] applying the deferred Run-panel refresh")
            try:
                self._render_run_device_list()
            except Exception as exc:
                _multi_log.warning(f"[RUN-TAB] deferred refresh failed: {exc!r}")
        if not was_active:
            return False
        _multi_log.info(
            f"[RUN-SESSION] session {self._run_session_id} complete — "
            f"no running, queued or retrying devices remain")
        self._start_end_of_run_sync()
        return True

    def _start_end_of_run_sync(self) -> bool:
        """
        The single end-of-run cache→sheet sync, fired on session completion.

        Skipped when another path already owns the final-sync ordering:
        Stop All, the fatal handler, controller close and the safe reset all set
        _shutdown_pending before finishing the session and perform their own
        (sometimes synchronous) flush. A hard internet emergency is not the end
        of a run at all — the restore path resumes it.
        """
        if getattr(self, "demo", False):
            return False
        if getattr(self, "_shutdown_pending", False):
            _multi_log.info(
                "[SYNC] end-of-run sync skipped — the stopping path owns it")
            return False
        if getattr(self, "_internet_down_emergency", False):
            _multi_log.info(
                "[SYNC] end-of-run sync skipped — internet emergency restart pending")
            return False

        def _end_of_run_sync():
            try:
                _multi_log.info("[SYNC] session complete — final cache→sheet sync")
                self._flush_pending_sheet_status()
                _multi_log.info("[SYNC] final sync done ✓")
                # Update sheet grid from cache (no Sheets read — cache is authoritative)
                self.q.put(("sheet_redraw", None))
            except Exception as _se:
                _multi_log.warning(f"[SYNC] final sync failed: {_se}")

        threading.Thread(target=_end_of_run_sync, daemon=True).start()
        return True

    def _render_run_device_list(self):
        # The BooleanVars are about to be destroyed along with their rows. Fold
        # them into the canonical model FIRST — defensively, in case anything
        # ever writes a var without going through _set_run_checked — so a tick
        # cannot be lost by the rebuild that follows. This happens even when the
        # rebuild is then deferred, so no tick is lost either way.
        for _a, _v in self._run_checks.items():
            try:
                self._run_check_selections[_a] = bool(_v.get())
            except Exception:
                pass

        # A rebuild destroys every row — including a running device's per-device
        # Stop button and the dict entry the queue reads — while controller
        # messages for that device are still arriving. Multi-Test already defers
        # for exactly this reason; the Run panel now does the same. The
        # underlying data (conf_devices, _online_adb_ids) is already updated, so
        # nothing is lost by showing it a moment later.
        if self._run_session_busy():
            self._run_panel_refresh_pending = True
            _multi_log.info(
                f"[RUN-TAB] panel refresh deferred — run session busy "
                f"(running={len(self._running_devs)} queued={len(self._run_queue)} "
                f"pending_retries={len(getattr(self, '_run_retry_after_ids', {}))} "
                f"session_active={getattr(self, '_run_session_active', False)})")
            try:
                self._log("Run panel refresh deferred — a Run is in progress", "warn")
            except Exception:
                pass
            # The device list itself may have changed, but online status is the
            # part that actually moves during a run, and it updates in place.
            for _a in list(self._run_rows.keys()):
                try:
                    self._apply_run_online_badge(_a)
                except Exception:
                    pass
            return

        self._run_panel_refresh_pending = False
        for w in self._run_inner.winfo_children():
            w.destroy()
        self._run_rows.clear()
        self._run_checks.clear()

        # The Run list is ALWAYS the configured devices from bluestacks.conf /
        # the sheet. Devices are not expected to be open: selecting a closed one
        # is the normal case, and device_worker launches and connects it before
        # prepare_target_app runs. Online status is shown per row as a badge only.
        source = self.conf_devices

        groups = _group_devices_by_type(source)
        if not groups:
            tk.Label(self._run_inner,
                     text="No devices found. Check bluestacks.conf or the sheet.",
                     font=FN, bg=BG_PANEL, fg=FG_DIM, pady=16,
                     wraplength=520, justify=tk.LEFT).pack()
            return

        for group_name, devs in groups:
            gf = tk.Frame(self._run_inner, bg=BG_PANEL)
            gf.pack(fill=tk.X, pady=(4, 0))
            # group header
            ghdr = tk.Frame(gf, bg="#1A1A30")
            ghdr.pack(fill=tk.X)
            expanded_var = tk.BooleanVar(value=True)
            body = tk.Frame(gf, bg=BG_PANEL)

            def _toggle(b=body, ev=expanded_var, tb=None, gn=group_name, cnt=len(devs)):
                if ev.get():
                    b.pack_forget()
                    ev.set(False)
                    if tb:
                        tb.configure(text=f"▶ {gn} ({cnt})")
                else:
                    b.pack(fill=tk.X)
                    ev.set(True)
                    if tb:
                        tb.configure(text=f"▼ {gn} ({cnt})")

            toggle_btn = tk.Button(ghdr, text=f"▼ {group_name} ({len(devs)})",
                                    font=FNB, bg="#1A1A30", fg=ACC_BLUE,
                                    relief=tk.FLAT, padx=8, pady=4, cursor="hand2",
                                    activebackground=BG_MID, bd=0, anchor=tk.W)
            # Wire command after creation so we can pass the button itself
            toggle_btn.configure(command=lambda b=body, ev=expanded_var, tb=toggle_btn, gn=group_name, cnt=len(devs): _toggle(b, ev, tb, gn, cnt))
            toggle_btn.pack(side=tk.LEFT, fill=tk.X, expand=True)

            _btn(ghdr, "All", lambda ds=devs: self._run_sel_group(ds, True),
                 bg=BG_CELL, fg=ACC_BLUE, font=FS, padx=5, pady=2).pack(side=tk.RIGHT, padx=2)
            _btn(ghdr, "None", lambda ds=devs: self._run_sel_group(ds, False),
                 bg=BG_CELL, fg=FG_DIM, font=FS, padx=5, pady=2).pack(side=tk.RIGHT, padx=2)

            body.pack(fill=tk.X)
            for dev in devs:
                self._build_run_device_row(body, dev)

    def _build_run_device_row(self, parent, dev):
        adb_id = dev["adb_id"]
        row = tk.Frame(parent, bg=BG_PANEL)
        row.pack(fill=tk.X, padx=4, pady=1)

        # Seeded from the canonical model, NEVER from a hardcoded False: this
        # runs on every rebuild, and value=False threw away the user's — or a
        # restored snapshot's — selection each time the list refreshed.
        check_var = tk.BooleanVar(
            value=bool(self._run_check_selections.get(adb_id, False)))
        self._run_checks[adb_id] = check_var

        # `command` fires only on real user interaction, not on var.set(), so
        # _set_run_checked writing check_var back cannot loop.
        cb = tk.Checkbutton(row, variable=check_var, bg=BG_PANEL,
                           activebackground=BG_PANEL, selectcolor=BG_CELL,
                           command=lambda a=adb_id, v=check_var:
                               self._set_run_checked(a, v.get()))
        cb.pack(side=tk.LEFT)

        name = dev.get("name", adb_id)
        tk.Label(row, text=name, font=(F, 8), bg=BG_PANEL, fg=FG_MAIN, anchor=tk.W).pack(side=tk.LEFT, padx=(0, 4))
        tk.Label(row, text=adb_id, font=(FM, 7), bg=BG_PANEL, fg=FG_DIM).pack(side=tk.LEFT, padx=(0, 4))

        # Online indicator — deliberately SEPARATE from the run-status badge so a
        # scan can refresh it without disturbing RUNNING/DONE/FAILED state or the
        # user's checkbox selections. Offline devices stay fully selectable.
        online_var = tk.StringVar(value="")
        online_lbl = tk.Label(row, textvariable=online_var, font=(FM, 7),
                              bg=BG_PANEL, fg=FG_DIM, width=8)
        online_lbl.pack(side=tk.LEFT, padx=(0, 4))

        # Seeded from the canonical display model so a rebuild does not wipe
        # RUNNING, SETUP ONLY, queued (n/m), RETRY n/3, STOPPING…, DONE ✓,
        # FAILED ✗, STOPPED, SKIPPED, INVALID TASKS or NO TASKS — nor the last
        # log line. A genuinely new device gets the IDLE / "—" default.
        _disp = self._run_display(adb_id)
        _badge = _disp.get("badge") or BADGE_IDLE
        status_var = tk.StringVar(value=_disp.get("status", "IDLE"))
        status_lbl = tk.Label(row, textvariable=status_var, font=FSB,
                              bg=_badge[0], fg=_badge[1], width=14)
        status_lbl.pack(side=tk.LEFT, padx=4)

        log_var = tk.StringVar(value=_disp.get("log", "—"))
        tk.Label(row, textvariable=log_var, font=(FM, 7), bg=BG_PANEL,
                 fg=FG_DIM, anchor=tk.W).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=4)

        stop_btn = tk.Button(row, text="■", font=FS, bg=BG_CELL, fg=FG_ERR,
                              relief=tk.FLAT, padx=4, pady=2, cursor="hand2",
                              command=lambda a=adb_id: self._run_stop_one(a))
        stop_btn.pack(side=tk.RIGHT, padx=2)

        self._run_rows[adb_id] = {
            "status_var": status_var,
            "status_lbl": status_lbl,
            "online_var": online_var,
            "online_lbl": online_lbl,
            "log_var":    log_var,
            "stop_btn":   stop_btn,
            "check_var":  check_var,
        }
        self._apply_run_online_badge(adb_id)

    def _find_device_record(self, adb_id: str) -> dict:
        """
        Resolve a device's configuration record (device_type, name, ...).

        Searches conf_devices FIRST because that is the authoritative
        configuration, and a device is not expected to be running. The previous
        `(self.active_devices or self.conf_devices)` pattern searched only the
        online list whenever any device happened to be online, so selecting a
        configured-but-closed device resolved to device_type="" — which silently
        skipped it in retry mode and gave it an empty task list in normal mode.

        Falls back to the online list for anything ADB found that the conf did
        not describe. Returns {} when the id is unknown.
        """
        aid = (adb_id or "").strip()
        for src in (self.conf_devices or [], self.active_devices or []):
            for d in src:
                if d.get("adb_id") == aid:
                    return d
        return {}

    def _apply_run_online_badge(self, adb_id: str) -> None:
        """
        Paint one row's online indicator from self._online_adb_ids.

        Blank until a scan has actually run — an empty set means "unknown", not
        "everything is offline", and claiming devices are offline before anyone
        checked would be misleading.
        """
        row = self._run_rows.get(adb_id)
        if not row or "online_var" not in row:
            return
        try:
            if not self._online_adb_ids:
                row["online_var"].set("")
                row["online_lbl"].configure(fg=FG_DIM, bg=BG_PANEL)
            elif adb_id in self._online_adb_ids:
                row["online_var"].set("● open")
                row["online_lbl"].configure(fg=BADGE_DONE[1], bg=BG_PANEL)
            else:
                row["online_var"].set("○ closed")
                row["online_lbl"].configure(fg=FG_DIM, bg=BG_PANEL)
        except Exception:
            pass

    def _refresh_run_online_badges(self) -> None:
        """
        Update every Run row's online indicator in place after a scan.

        Deliberately NOT a full re-render: rebuilding the rows would wipe the
        user's checkbox selections and reset live run-status badges, and the
        device list itself has not changed — only its status has.
        """
        if not self._run_rows:
            # Nothing rendered yet (e.g. scan finished before startup render).
            self._render_run_device_list()
            return
        for adb_id in list(self._run_rows.keys()):
            self._apply_run_online_badge(adb_id)
        n_open = sum(1 for a in self._run_rows if a in self._online_adb_ids)
        _multi_log.info(
            f"[RUN-TAB] online badges refreshed: {n_open}/{len(self._run_rows)} open "
            f"(list still shows all {len(self.conf_devices)} configured device(s))"
        )

    def _set_run_checked(self, adb_id: str, checked: bool) -> None:
        """
        The ONE way a Run-tab tick changes.

        Model first and unconditionally — the device may have no row (offline
        at load time, or removed from the conf and later restored) — then the
        widget, only if one exists. Mirrors _set_multi_selection exactly.
        """
        checked = bool(checked)
        self._run_check_selections[adb_id] = checked
        var = self._run_checks.get(adb_id)
        if var is not None:
            try:
                var.set(checked)
            except Exception:
                pass

    def _run_sel_all(self, v: bool):
        # The rendered list only: "All" means the devices this button sits
        # above. A stale canonical entry for a device that is no longer
        # configured is not part of "all" and keeps its own value.
        for adb_id in list(self._run_checks):
            self._set_run_checked(adb_id, v)

    def _run_sel_group(self, devs, v: bool):
        for d in devs:
            self._set_run_checked(d["adb_id"], v)

    def _retry_pending_tasks_for_device(
        self, adb_id: str, task_keys: list[str]
    ) -> "tuple[bool, list[str], str]":
        """
        Returns (has_pending, pending_task_list, reason).
        A task is considered already done if EITHER the sheet snapshot OR the local
        controller status cache says it is 'done'.  A task is pending only when
        NEITHER source says it is 'done'.

        No task-specific special cases remain.
        """
        if not task_keys:
            return False, [], "no configured tasks"
        snap = self.bridge.status_snapshot(adb_id)
        with self._status_cache_lock:
            local = dict(self._status_cache.get(adb_id, {}))
        pending = []
        for k in task_keys:
            sheet_val = snap.get(k, "") or ""
            local_val = local.get(k, "") or ""

            # No task-specific special cases remain. Both header=None cases
            # (app_level "always re-run", map_location "any value means done")
            # went with their tasks; a future task needing either can reintroduce
            # its own rule here.
            # Standard tasks: done only when status == "done"
            sheet_done = sheet_val.strip().lower() == "done"
            local_done = local_val.strip().lower() == "done"
            if not sheet_done and not local_done:
                pending.append(k)

        if not pending:
            return False, [], "all selected tasks already done"
        return True, pending, "pending tasks found"

    # ══════════════════════════════════════════════════════════════════════════
    # HUMAN-READABLE PER-DEVICE RUN LOG — controller side
    #
    # Everything here is additive and best-effort. No path in this block may
    # fail a task, change a badge, touch Sheets, alter retry counts, delay the
    # queue, or hold the Run session open. Every entry point is wrapped.
    # ══════════════════════════════════════════════════════════════════════════
    # The controller's own terminal cleanup writes into the DEVICE's raw log,
    # because bot.reset_device_finished_state() resolves _get_device_logger()
    # in whatever process calls it. That means a "final counters before wipe"
    # line inside a device log may have been written by the worker OR by the
    # controller, and nothing in the line itself says which.
    #
    # [WORKER-END] used to be the only boundary, but the bot's _finalize()
    # calls reset_device_finished_state() at step 4 and writes [WORKER-END] at
    # step 5. A worker killed between those two steps leaves a REAL worker
    # snapshot with no [WORKER-END] after it. Attributing that to the
    # controller is wrong, and so is attributing the controller's later one to
    # the worker. Value-based guessing ("zeros must be the controller") is not
    # evidence — a controller snapshot can legitimately be non-zero.
    #
    # So the controller states its own boundary explicitly, in the same file,
    # immediately before it resets.
    HUMAN_CLEANUP_BOUNDARY = "[HUMAN-BOUNDARY] controller cleanup begins"

    @staticmethod
    def _close_disposition_for(result):
        """
        Map a tri-state close result to its disposition code.

        None is UNVERIFIED, not failure and not success — a close ran but its
        outcome could not be confirmed.
        """
        if result is True:
            return "attempted_success"
        if result is False:
            return "attempted_failed"
        return "attempted_unverified"

    def _human_mark_controller_cleanup(self, adb_id: str) -> None:
        """
        Write the controller-cleanup boundary into this device's raw log.

        Uses the bot's own _get_device_logger so the line lands in the same
        file, through the same handler, in the same format the worker uses —
        no second writer, no format drift. Best-effort: a failure here must
        never affect the Run.
        """
        try:
            bot = getattr(getattr(self, "bridge", None), "bot", None)
            getter = getattr(bot, "_get_device_logger", None)
            if getter is None:
                return
            getter(adb_id).info(self.HUMAN_CLEANUP_BOUNDARY)
        except Exception as exc:
            _multi_log.warning(
                f"[HUMAN-LOG] cleanup boundary marker failed for {adb_id}: {exc!r}")

    def _human_raw_log_path(self, adb_id: str) -> str:
        """The bot's per-device log file: logs/<sanitized_device>.log."""
        safe = re.sub(r"[^a-zA-Z0-9._-]+", "_", adb_id or "unknown")
        return os.path.join(LOG_DIR, "logs", f"{safe}.log")

    def _human_friendly_name(self, adb_id: str) -> str:
        """
        Authoritative configured display name — no new Sheets call, and never
        inferred from OCR or arbitrary log text.
        """
        try:
            dev = self._find_device_record(adb_id) or {}
        except Exception:
            dev = {}
        for key in ("name", "friendly_name", "display_name", "instance_name"):
            v = (dev.get(key) or "").strip() if isinstance(dev.get(key), str) else ""
            if v:
                return v
        return adb_id

    def _human_register_device(self, adb_id: str, verdict: dict = None) -> None:
        """
        Open the human-log context for a device selected in this Run session.

        Called when the session is accepted — BEFORE any worker launches — so a
        device that is stopped, skipped or found invalid before it ever launches
        still gets exactly one report. Records the raw log's current size as the
        start offset. Deliberately does NOT count a launch attempt.
        """
        try:
            key = (self._run_session_id, adb_id)
            ctx = self._human_ctx.get(key)
            if ctx is not None:
                if verdict:
                    ctx.resolved_tasks = verdict.get("task_keys") or ctx.resolved_tasks
                    ctx.task_action = verdict.get("action") or ctx.task_action
                return
            path = self._human_raw_log_path(adb_id)
            try:
                offset = os.path.getsize(path) if os.path.exists(path) else 0
            except Exception:
                offset = 0
            v = verdict or {}
            dev = self._find_device_record(adb_id) or {}
            self._human_ctx[key] = HumanDeviceLogContext(
                session_id=self._run_session_id, adb_id=adb_id,
                friendly_name=self._human_friendly_name(adb_id),
                device_type=(dev.get("device_type") or ""),
                requested_tasks=v.get("configured") or [],
                resolved_tasks=v.get("task_keys") or [],
                task_action=v.get("action") or "run",
                raw_log_path=path, raw_start_offset=offset)
            _multi_log.info(
                f"[HUMAN-LOG] context registered adb_id={adb_id} "
                f"session={self._run_session_id} raw_offset={offset}")
        except Exception as exc:
            _multi_log.warning(f"[HUMAN-LOG] register failed for {adb_id}: {exc!r}")

    def _human_note_launch_attempt(self, adb_id: str, launch_token,
                                   verdict: dict = None) -> None:
        """
        Record a REAL launch attempt.

        Called only after _run_launch_one has minted the launch token, so an
        attempt never carries launch_token=None. The context is reused across
        retries inside the session — a retry is not a finished lifecycle.
        """
        try:
            self._human_register_device(adb_id, verdict)
            ctx = self._human_ctx.get((self._run_session_id, adb_id))
            if ctx is None:
                return
            if verdict:
                ctx.resolved_tasks = verdict.get("task_keys") or ctx.resolved_tasks
                ctx.task_action = verdict.get("action") or ctx.task_action
            ctx.note_attempt(launch_token)
        except Exception as exc:
            _multi_log.warning(f"[HUMAN-LOG] attempt note failed for {adb_id}: {exc!r}")

    def _human_finalize_device(self, adb_id: str, result: str = "", ok=None,
                               close_ok=None, session_id=None,
                               badge: str = "", close_disposition: str = "",
                               prior_close_result="no_attempt") -> None:
        """
        The device is TRULY terminal — capture the end offset and queue the
        report. Idempotent: a duplicate or stale completion cannot produce a
        second report.

        Deliberately NOT called for an adb_connect_failed that has another retry
        scheduled: that is mid-lifecycle, and the report must cover both attempts.
        """
        try:
            sid = self._run_session_id if session_id is None else session_id
            ctx = self._human_ctx.get((sid, adb_id))
            if ctx is None:
                return
            if ctx.finalized:
                _multi_log.info(
                    f"[HUMAN-LOG] {adb_id} already finalized for session {sid} "
                    f"— duplicate completion ignored")
                return
            ctx.finalized = True
            try:
                ctx.raw_end_offset = (os.path.getsize(ctx.raw_log_path)
                                      if os.path.exists(ctx.raw_log_path) else
                                      ctx.raw_start_offset)
            except Exception:
                ctx.raw_end_offset = None
            ctx.finished_at = datetime.now()
            ctx.final_result = result or ctx.final_result
            ctx.final_ok = ok if ok is not None else ctx.final_ok
            ctx.close_ok = close_ok if close_ok is not None else ctx.close_ok
            ctx.close_disposition = close_disposition or ctx.close_disposition
            if prior_close_result != "no_attempt":
                ctx.prior_close_result = prior_close_result
            ctx.final_badge = badge or ctx.final_badge
            try:
                ctx.retry_count = int(self._run_retry_counts.get(adb_id, 0))
            except Exception:
                pass
            ctx.close_attempt(result)
            self._human_submit(ctx)
        except Exception as exc:
            _multi_log.warning(f"[HUMAN-LOG] finalize failed for {adb_id}: {exc!r}")

    def _human_submit(self, ctx) -> None:
        """Hand the context to the background worker. Never blocks the Run."""
        try:
            self._human_start_worker()
            self._human_log_jobs.put_nowait(ctx)
        except Exception as exc:
            # A full queue or a dead worker is a diagnostics loss, never a Run
            # problem. Log it and carry on.
            _multi_log.warning(
                f"[HUMAN-LOG] could not queue report for {ctx.adb_id}: {exc!r}")

    def _human_start_worker(self) -> None:
        t = getattr(self, "_human_log_thread", None)
        if t is not None and t.is_alive():
            return
        self._human_log_thread = threading.Thread(
            target=self._human_log_worker, daemon=True, name="human_log_worker")
        self._human_log_thread.start()

    def _set_terminal_override(self, adb_id, session_id, launch_token,
                               result, ok=False) -> None:
        """
        Claim controller ownership of ONE launch's terminal result.

        Bound to the exact (adb_id, session_id, launch_token) triple so it can
        never rewrite an unrelated completion — including a later relaunch of
        the same device.
        """
        self._run_terminal_override[adb_id] = {
            "session_id": session_id, "launch_token": launch_token,
            "result": result, "ok": bool(ok)}
        _multi_log.info(
            f"[TERMINAL-OWN] controller owns terminal result for {adb_id} "
            f"session={session_id} token={launch_token} result={result!r}")

    def _take_terminal_override(self, adb_id, session_id, launch_token):
        """
        The override for THIS exact launch, consumed. None if there is none.

        Consumed on use, so the first accepted completion applies it and a
        later duplicate finds nothing — that duplicate is stale either way.
        """
        ov = (getattr(self, "_run_terminal_override", None) or {}).get(adb_id)
        if not ov:
            return None
        if (ov.get("session_id") != session_id
                or ov.get("launch_token") != launch_token):
            # A different launch of the same device. Not ours to rewrite.
            return None
        self._run_terminal_override.pop(adb_id, None)
        return ov

    def _stop_one_resolve_close(self, adb_id: str):
        """
        Stop One's close contract for a device with NO live worker.

        Stop One means "stop this device and close its window". A device that
        already launched — waiting on a retry, or requeued by `_run_requeue`
        into `_run_queue` — still has a window, so the close must be resolved
        rather than declared "not requested" or "not applicable".

            previous True      already positively confirmed closed; no re-close
            previous False     re-attempt; the new result is authoritative
            previous None      recorded but UNVERIFIED; re-attempt
            no record, launched  attempt one — Stop One's contract
            never launched     genuinely nothing to close

        Returns (close_ok, disposition, prior_close_result).
        """
        has_prev, prev = self._human_close_history(adb_id)
        if not has_prev and not self._human_ever_launched(adb_id):
            return None, "not_applicable_never_launched", "no_attempt"
        prior = prev if has_prev else "no_attempt"
        if prev is True:
            return True, "attempted_success", prior
        _why = ("previous close FAILED" if prev is False
                else "previous close UNVERIFIED" if has_prev
                else "a window was opened but no close was ever recorded")
        _multi_log.info(
            f"[CLOSE_EMU] Stop One on non-running {adb_id}: {_why} — "
            f"attempting a close now")
        try:
            _bot = self.bridge.bot if hasattr(self.bridge, "bot") else None
            ok = self._close_emulator_for_device(adb_id, _bot, timeout=15)
        except Exception as exc:
            # An exception outside the helper proves nothing about the window.
            ok = None
            _multi_log.warning(
                f"[CLOSE_EMU] Stop One close error {adb_id}: {exc} — UNVERIFIED")
        self._run_last_close[adb_id] = ok
        _multi_log.info(
            f"[CLOSE_EMU] Stop One non-running close result adb_id={adb_id} "
            f"ok={ok}")
        # A later positive close supersedes the earlier failure: the window is
        # shut now, so the report must not keep warning about a zombie.
        return ok, self._close_disposition_for(ok), ("no_attempt" if ok is True
                                                     else prior)

    def _human_ever_launched(self, adb_id: str) -> bool:
        """
        Did a worker process EVER start for this device in this Run session?

        `ctx.attempts` is the only honest source: it is appended to solely
        after proc.start()/t.start() returns without raising. Membership of
        `_run_queue`, `_running_devs` or `_run_retry_after_ids` describes where
        the device is scheduled RIGHT NOW, not what has already happened to it.

        This matters because `_run_requeue()` moves a device that already ran —
        attempt 1, adb_connect_failed, retry fired — back into `_run_queue`,
        where it waits for a concurrency slot. Treating "queued" as "never
        launched" erased that attempt from the report and claimed no emulator
        window had ever been opened.
        """
        try:
            ctx = self._human_ctx.get((self._run_session_id, adb_id))
            return bool(ctx is not None and ctx.attempts)
        except Exception:
            return False

    def _human_close_history(self, adb_id: str):
        """
        What this Run already knows about closing this device's window.

        Returns (has_record, result) where result is True / False / None.
        `None` recorded is "a close was attempted and could not be verified";
        no record at all is "no close has been attempted". Collapsing the two
        turned an unverified close into "not applicable".
        """
        hist = getattr(self, "_run_last_close", {}) or {}
        if adb_id in hist:
            return True, hist[adb_id]
        return False, None

    def _human_never_launched_disposition(self, adb_id: str,
                                          route_policy: str) -> str:
        """
        The close disposition for a device an abandonment route is finalizing.

        `not_applicable_never_launched` is a claim that no window was ever
        opened. It may only be made when nothing ever launched AND no close was
        ever attempted; otherwise the route's own policy applies and the
        historical close outcome is preserved separately.
        """
        has_hist, _ = self._human_close_history(adb_id)
        if self._human_ever_launched(adb_id) or has_hist:
            return route_policy
        return "not_applicable_never_launched"

    def _human_snapshot_abandoned_run(self) -> dict:
        """
        WHO the Run still owns, captured BEFORE anything is mutated.

            running    — a live worker in _running_devs
            retry_only — no worker, only a pending ADB retry callback
            queued     — never launched, still in _run_queue

        Abandonment routes cancel retries, clear the queue and clear
        _running_devs. Once they have, there is no way to tell which devices the
        Run owned, so every route takes this snapshot first and then works from
        it. Categories are disjoint, in that priority order.
        """
        try:
            running = list(getattr(self, "_running_devs", {}) or {})
            retry_only = [d for d in (getattr(self, "_run_retry_after_ids", {})
                                      or {}) if d not in running]
            queued = [d for d in (getattr(self, "_run_queue", []) or [])
                      if d not in running and d not in retry_only]
        except Exception as exc:
            _multi_log.warning(f"[HUMAN-LOG] abandonment snapshot failed: {exc!r}")
            running, retry_only, queued = [], [], []
        # "queued" is a scheduling position, NOT a launch history. A device
        # requeued by _run_requeue after a failed first attempt sits here with a
        # real worker attempt behind it.
        queued_fresh = [d for d in queued if not self._human_ever_launched(d)]
        requeued = [d for d in queued if self._human_ever_launched(d)]
        snap = {"running": running, "retry_only": retry_only,
                "queued": queued_fresh, "requeued": requeued}
        _multi_log.info(
            f"[HUMAN-LOG] abandonment snapshot running={len(running)} "
            f"retry_only={len(retry_only)} queued={len(queued_fresh)} "
            f"requeued={len(requeued)}")
        return snap

    def _human_finalize_devices(self, adb_ids, result: str, note: str = "",
                                close_disposition: str = "") -> int:
        """
        Finalize an explicit list of devices. Idempotent per device.

        Deliberately takes a LIST rather than reading live state: the caller
        already knows which category it is finalizing and when that category's
        raw evidence is complete. A device that already reported — including one
        whose run_done landed first — is skipped, so a stale late completion can
        never produce a second report or overwrite the terminal result.
        """
        n = 0
        sid = self._run_session_id
        for adb_id in list(adb_ids or []):
            try:
                ctx = self._human_ctx.get((sid, adb_id))
                if ctx is None or ctx.finalized:
                    continue
                if note:
                    ctx.notes.append(note)
                try:
                    self._run_set_badge(adb_id, "STOPPED",
                                        BADGE_STOPPED[0], BADGE_STOPPED[1])
                except Exception:
                    pass
                _has, _prev = self._human_close_history(adb_id)
                self._human_finalize_device(
                    adb_id, result=result, ok=False, badge="STOPPED",
                    session_id=sid, close_disposition=close_disposition,
                    prior_close_result=_prev if _has else "no_attempt")
                n += 1
            except Exception as exc:
                _multi_log.warning(
                    f"[HUMAN-LOG] finalize failed for {adb_id}: {exc!r}")
        if n:
            _multi_log.info(f"[HUMAN-LOG] finalized {n} device(s) as {result}")
        return n

    def _human_finalize_abandoned_nonrunning(self, snap: dict, result: str,
                                             note: str = "",
                                             close_disposition: str = "") -> int:
        """
        Phase 1: the categories with NO live worker.

        Queued and retry-only devices have nothing still writing to their raw
        logs, so freezing their slice now is correct — and they must be
        finalized before the queue and retry dicts are emptied.

        Genuinely never-launched queued devices get
        `not_applicable_never_launched` — they opened no window. Requeued ones
        DID open a window on an earlier attempt, so they take the route's own
        policy and keep their prior attempt in the narrative.
        """
        n = 0
        for adb_id in list(snap.get("queued") or []):
            n += self._human_finalize_devices(
                [adb_id], result, note=note,
                close_disposition=self._human_never_launched_disposition(
                    adb_id, close_disposition))
        for adb_id in (list(snap.get("requeued") or [])
                       + list(snap.get("retry_only") or [])):
            n += self._human_finalize_devices(
                [adb_id], result, note=note,
                close_disposition=self._human_never_launched_disposition(
                    adb_id, close_disposition))
        return n

    def _human_finalize_abandoned_running(self, snap: dict, result: str,
                                          note: str = "",
                                          close_disposition: str = "") -> int:
        """
        Phase 2: devices that had a LIVE worker.

        Called only after the workers have been signalled, waited for, killed if
        necessary, and their queues drained both sides. `_human_finalize_device`
        freezes ctx.raw_end_offset at the current log size, so calling this
        earlier would cut the slice before a gracefully-stopping worker writes
        its `recording stopped —`, its final counter snapshot and `[WORKER-END]`
        — evidence that genuinely exists and belongs in the report. A worker
        force-killed before writing them still reports their absence truthfully,
        because the slice is taken from the file as it actually is.
        """
        return self._human_finalize_devices(
            snap.get("running"), result, note=note,
            close_disposition=close_disposition)

    def _human_flush_jobs(self, timeout: float = 8.0) -> bool:
        """
        Wait, boundedly, for already-queued reports to be written.

        The writer is a daemon thread: at interpreter exit it is killed wherever
        it happens to be, so queueing a report immediately before destroy() is
        not the same as saving it. This gives it a deterministic chance and then
        gives up — a diagnostics product must never hold the application open.
        """
        q = getattr(self, "_human_log_jobs", None)
        if q is None:
            return True
        deadline = time.time() + max(0.0, timeout)
        try:
            while time.time() < deadline:
                if q.unfinished_tasks == 0:
                    _multi_log.info("[HUMAN-LOG] all queued reports written")
                    return True
                time.sleep(0.05)
            _multi_log.warning(
                f"[HUMAN-LOG] {q.unfinished_tasks} report(s) still pending after "
                f"{timeout:.0f}s — continuing shutdown anyway")
        except Exception as exc:
            _multi_log.warning(f"[HUMAN-LOG] flush wait failed: {exc!r}")
        return False

    def _human_prune_contexts(self, keep_session=None) -> None:
        """
        Drop finalized contexts from older sessions.

        Called only AFTER the background job holds its own reference, so nothing
        is pruned out from under a pending report. The current session is kept
        so duplicate/stale completions still hit the `finalized` latch rather
        than finding an empty dict and silently re-creating anything.
        """
        try:
            for key in [k for k, c in list(self._human_ctx.items())
                        if c.finalized and k[0] != keep_session]:
                self._human_ctx.pop(key, None)
        except Exception as exc:
            _multi_log.warning(f"[HUMAN-LOG] prune failed: {exc!r}")

    def _human_log_worker(self) -> None:
        """
        One daemon consumer. Catches every exception: a report that cannot be
        rendered must not take anything else with it, and a slow one must not
        stop the next device launching.
        """
        while True:
            try:
                ctx = self._human_log_jobs.get()
            except Exception:
                return
            try:
                gen = HumanDeviceLogGenerator(
                    ctx, task_defs=TASK_DEFS, renderers=HUMAN_TASK_RENDERERS)
                path = gen.write(os.path.join(LOG_DIR, "logs"))
                # The job owns `ctx` now, so the controller's copy can go. Only
                # FINALIZED entries are pruned, and only for sessions that are
                # over — a stale message can then find nothing to re-finalize.
                self._human_prune_contexts(keep_session=self._run_session_id)
                _multi_log.info(
                    f"[HUMAN-LOG] saved adb_id={ctx.adb_id} path={path}")
                try:
                    self.q.put(("run_log", ctx.adb_id,
                                f"Human log saved: {os.path.basename(path)}", "dim"))
                except Exception:
                    pass
            except Exception as exc:
                _multi_log.warning(
                    f"[HUMAN-LOG] generation failed for {ctx.adb_id}: {exc!r}")
            finally:
                try:
                    self._human_log_jobs.task_done()
                except Exception:
                    pass

    def _run_display(self, adb_id: str) -> dict:
        """Canonical per-device Run display state. Never holds live handles."""
        return self._run_display_state.setdefault(
            adb_id, {"status": "IDLE", "badge": BADGE_IDLE, "log": "—"})

    def _run_set_badge(self, adb_id, text, bg, fg):
        # Record FIRST and unconditionally. A rebuild recreates the row, and
        # without this the RUNNING / queued / RETRY / DONE ✓ it is showing would
        # be reset to IDLE the moment the panel refreshes — and a badge set for
        # a device with no row (one that was offline when the list was built)
        # would be dropped entirely.
        d = self._run_display(adb_id)
        d["status"], d["badge"] = text, (bg, fg)
        row = self._run_rows.get(adb_id)
        if not row:
            return
        row["status_var"].set(text)
        try:
            row["status_lbl"].configure(bg=bg, fg=fg)
        except tk.TclError:
            pass

    def _run_set_log(self, adb_id: str, msg: str) -> None:
        """Record a device's last Run log line, then show it if it is rendered."""
        text = (msg or "")[:50]
        self._run_display(adb_id)["log"] = text
        row = self._run_rows.get(adb_id)
        if row:
            try:
                row["log_var"].set(text)
            except Exception:
                pass

    def _run_start_selected(self):
        # ── One Run session at a time ────────────────────────────────────────
        # Before ANYTHING is read or written. A second start used to overwrite
        # _run_queue, _retry_task_keys_by_device, _run_retry_counts and the
        # _current_run_selected_* metadata underneath a live run, and could
        # queue a device that was already running. Nothing below this guard may
        # execute while a lifecycle is in flight.
        if self._run_session_busy():
            _multi_log.warning(
                f"[RUN-SESSION] RUN SELECTED rejected — session "
                f"{self._run_session_id} still active "
                f"(running={sorted(self._running_devs)} "
                f"queued={list(self._run_queue)} "
                f"pending_retries={sorted(getattr(self, '_run_retry_after_ids', {}))})")
            self._run_log_msg(
                "⚠ A Run is already active — stop it before starting another.",
                "warn")
            messagebox.showwarning(
                "Run in progress",
                "A Run is already active.\n\n"
                "Wait for it to finish, or press STOP ALL first.",
                parent=self)
            return

        chosen = [a for a, v in self._run_checks.items() if v.get()]
        if not chosen:
            messagebox.showwarning("Nothing selected", "Tick at least one device.")
            return
        # Order by sheet order
        sheet_order = list(self.bridge.rows_by_device.keys())
        chosen.sort(key=lambda a: sheet_order.index(a) if a in sheet_order else 999)

        # ── Retry mode: filter before queue assignment ────────────────────────
        retry_on = False
        try:
            retry_on = self.retry_var.get()
        except Exception:
            pass

        # A: explicit enabled log for both states
        _multi_log.info(f"[RETRY] enabled={retry_on}")
        # 2: Do NOT call refresh_sheet here — the controller cache is the source
        # of truth during/after a run.  _retry_pending_tasks_for_device reads
        # _status_cache (seeded at startup/reset).

        queued: list[str] = []
        retry_skipped: list[str] = []
        # Retry-mode devices that were SELECTED but have nothing to do. They are
        # terminal for this Run, so each still gets one report.
        self._human_retry_skipped: list = []
        # 1: Only populated in retry mode.  In normal mode this dict stays empty
        # so _run_launch_one falls through to task_config for every device.
        _pending_tasks_by_device: dict[str, list[str]] = {}

        for adb_id in chosen:
            dev = self._find_device_record(adb_id)
            dt = (dev or {}).get("device_type", "") or ""

            if retry_on:
                # A: Retry must use Task Config by DeviceType — no SUBTASK_ORDER
                # fallback.  If the DeviceType has NO Task Config, skip + log.
                if dt not in self.task_config:
                    _multi_log.info(
                        f"No Task Config found for DeviceType '{dt}' on {adb_id}; "
                        f"skipping device."
                    )
                    _multi_log.info(f"[RETRY] device={adb_id} configured_tasks=[<NO_TASK_CONFIG>]")
                    _multi_log.info(f"[RETRY] device={adb_id} skipped_no_pending")
                    self._run_log_msg(
                        f"⏭ {adb_id}: Retry — No Task Config for DeviceType '{dt}'",
                        "warn"
                    )
                    retry_skipped.append(adb_id)
                    # Structured record. configured_tasks is [] and NOT None
                    # because this branch proved there is no Task Config at all
                    # — the report must not fabricate task names it never saw.
                    self._human_retry_skipped.append({
                        "adb_id": adb_id,
                        "note": f"Retry mode — no Task Config for DeviceType '{dt}'",
                        "reason": "no_task_config",
                        "detail": dt,
                        "configured_tasks": [],
                    })
                    continue

                task_keys = list(self.task_config.get(dt, []))
                try:
                    task_keys = self._task_sets.expand_keys(task_keys)
                except Exception:
                    pass
                # Remove invalid/unknown task keys
                task_keys = [k for k in task_keys if k in TASK_DEFS]
                _multi_log.info(f"[RETRY] device={adb_id} configured_tasks={task_keys}")

                has_pending, pending, reason = self._retry_pending_tasks_for_device(
                    adb_id, task_keys
                )
                if not has_pending:
                    _multi_log.info(f"[RETRY] device={adb_id} skipped_no_pending ({reason})")
                    self._run_log_msg(f"⏭ {adb_id}: Retry mode — {reason}", "warn")
                    retry_skipped.append(adb_id)
                    # _retry_pending_tasks_for_device distinguishes these two:
                    #   "no configured tasks"           -> empty_task_list
                    #   "all selected tasks already done" -> all_tasks_done
                    _code = ("empty_task_list" if "no configured tasks" in reason
                             else ("all_tasks_done" if "already done" in reason
                                   else ""))
                    # Carry the ACTUAL configured task keys through to the human
                    # log. Without them the "all tasks already done" report had
                    # nothing to name and rendered "Task(s): [None pending]" —
                    # which reads as "nothing was configured", the opposite of
                    # what happened. task_keys is the expanded, TASK_DEFS-valid
                    # list this decision was actually made from.
                    # empty_task_list keeps its empty list: it must never claim
                    # completion of tasks that were never configured.
                    self._human_retry_skipped.append({
                        "adb_id": adb_id,
                        "note": f"Retry mode — {reason}",
                        "reason": _code,
                        "detail": dt,
                        "configured_tasks": (list(task_keys)
                                             if _code == "all_tasks_done" else []),
                    })
                    continue

                # Ensure pending list contains only valid task keys
                pending = [k for k in pending if k in TASK_DEFS]
                _multi_log.info(f"[RETRY] device={adb_id} pending_tasks={pending}")
                # 1: Only assign in retry mode — normal mode must NOT populate this dict
                _pending_tasks_by_device[adb_id] = pending
            # else: normal mode — do not add to _pending_tasks_by_device;
            #        _run_launch_one will use task_config directly.

            queued.append(adb_id)

        # NOTE: the "nothing to run" exit is deliberately NOT here any more. It
        # used to return before the session was accepted, so an all-Retry-
        # skipped run registered no human contexts and produced no reports for
        # devices the user had selected. Acceptance + registration happen first;
        # the empty-queue exit is below, after every selected device has a
        # terminal report.

        # Order-preserving de-duplication. A device must never appear twice in
        # the queue: the second entry would launch a worker on top of the first
        # one's, and _run_launch_one would overwrite its Process and stop_event.
        _seen: set = set()
        _deduped = [a for a in queued if not (a in _seen or _seen.add(a))]
        if len(_deduped) != len(queued):
            _dupes = sorted({a for a in queued if queued.count(a) > 1})
            _multi_log.warning(
                f"[RUN-START] dropped {len(queued) - len(_deduped)} duplicate "
                f"queue entr(ies): {_dupes}")
            self._run_log_msg(
                f"⚠ Ignored duplicate selection for {', '.join(_dupes)}", "warn")
        queued = _deduped

        # ── Session accepted ─────────────────────────────────────────────────
        # Defensive: nothing should be pending here (the guard above returned if
        # anything was), but a cancelled-then-recreated session must not inherit
        # a stray callback.
        self._cancel_run_retries(reason="new session")
        # ── Defensive: no pause may be owned by an older Run ─────────────────
        # The busy guard above has already returned if anything was still in
        # flight, so a pause surviving here belongs to a Run that is over. Left
        # alone, a stale `_internet_pause_active = True` makes
        # _run_process_queue() answer "queue pump blocked" forever and the
        # freshly accepted queue never starts. Ownership only — worker
        # pause_events are not touched, so nothing is resumed into a dead
        # network by this cleanup.
        if (getattr(self, "_internet_pause_active", False)
                or getattr(self, "_internet_pause_owner", None) is not None
                or getattr(self, "_internet_pause_thread", None) is not None):
            _multi_log.warning(
                f"[INTERNET-PAUSE] stale pause state found at RUN SELECTED "
                f"(active={getattr(self, '_internet_pause_active', False)} "
                f"owner={getattr(self, '_internet_pause_owner', None)} "
                f"monitor={getattr(self, '_internet_pause_thread', None)!r}) "
                f"— clearing it so the new queue is not blocked")
            self._cancel_internet_pause(reason="stale pause before a new Run")
            self._internet_pause_thread = None

        # Expectations from the previous session cannot be satisfied any more;
        # leaving them would let an old worker's completion be accepted here.
        if self._run_expected_launch:
            _multi_log.info(
                f"[IDENTITY] discarding {len(self._run_expected_launch)} stale "
                f"launch expectation(s): {sorted(self._run_expected_launch)}")
            self._run_expected_launch.clear()
        self._run_recent_completion.clear()
        self._run_recent_recording_identity.clear()
        # The fatal latch is per-RUN, not per-controller. It was set True by the
        # fatal handler and never reset, so once a FatalAPKError happened every
        # later run in that controller silently refused to retry a genuine
        # adb_connect_failed. The user has had the chance to fix the APK; a new
        # Run starts with a clean slate.
        if getattr(self, "_fatal_run_stop", False):
            _multi_log.info(
                "[RUN-SESSION] clearing the fatal-stop latch for the new run")
            self._fatal_run_stop = False
        self._run_session_id += 1
        # Close history belongs to ONE Run. The report says "an earlier close
        # attempt in THIS Run", so carrying Run 1's failure into Run 2 would be
        # a false claim about a device that has not even launched yet. Cleared
        # HERE — as the session id advances and before any context for the new
        # Run is registered — and deliberately NOT cleared by _run_requeue, an
        # ADB retry or an in-session recovery, which it exists to survive.
        self._run_last_close.clear()
        # A controller-owned terminal result belongs to one launch in one Run.
        self._run_terminal_override.clear()
        self._run_session_active = True
        try:
            self._run_btn.configure(state=tk.DISABLED)
        except Exception:
            pass
        _multi_log.info(
            f"[RUN-SESSION] session {self._run_session_id} started with "
            f"{len(queued)} device(s)")

        self._run_queue = list(queued)
        self._retry_task_keys_by_device = _pending_tasks_by_device
        self._run_retry_counts.clear()
        self._shutdown_pending = False   # fresh run — lift any prior shutdown block
        self._current_run_selected_ids   = set(queued)
        self._current_run_selected_order = list(queued)

        # Every selected device gets a human-log context now, before anything
        # launches — so a device stopped or skipped before its worker ever
        # starts still produces exactly one report.
        for _hid in queued:
            try:
                self._human_register_device(_hid, self._resolve_run_task_keys(_hid))
            except Exception:
                self._human_register_device(_hid)
        for _rs in getattr(self, "_human_retry_skipped", []):
            _sid_dev = _rs["adb_id"]
            _code = _rs.get("reason") or ""
            _tasks = list(_rs.get("configured_tasks") or [])
            # Register WITH the task keys so the report can name what was
            # skipped. Only all_tasks_done supplies any, so no other branch can
            # claim tasks were complete.
            self._human_register_device(
                _sid_dev, {"task_keys": _tasks, "configured": _tasks,
                           "action": "retry_skipped"})
            _hc = self._human_ctx.get((self._run_session_id, _sid_dev))
            if _hc is not None:
                _hc.task_action = "retry_skipped"
                _hc.retry_skip_reason = _code
                _hc.retry_skip_detail = _rs.get("detail") or ""
                if _tasks:
                    _hc.resolved_tasks = _tasks
                    _hc.requested_tasks = _tasks
                _hc.notes.append(_rs.get("note") or "")
            self._run_set_badge(_sid_dev, "SKIPPED", BADGE_IDLE[0], BADGE_IDLE[1])
            self._human_finalize_device(_sid_dev, result="retry_skipped",
                                        ok=False, badge="SKIPPED")

        # ── Zero work to do ──────────────────────────────────────────────────
        # Every selected device already has its terminal report, so the session
        # can close immediately. No worker is launched to produce a report, and
        # no worker timestamps are invented for these devices.
        if not queued:
            _multi_log.info(
                f"[RUN-SESSION] session {self._run_session_id} has no runnable "
                f"device(s); {len(getattr(self, '_human_retry_skipped', []))} "
                f"were skipped by Retry logic — closing immediately")
            self._run_log_msg(
                "⏭ Retry mode: all selected devices have no pending tasks — nothing to run.",
                "warn")
            self._finish_run_session_if_idle()
            return

        self._run_log_msg(f"▶ Queued {len(queued)} device(s)", "info")

        # ── Proof logs ─────────────────────────────────────────────────────────
        try:
            mc = self._max_concurrent.get()
        except Exception:
            mc = -1
        try:
            skip_before = self.skip_var.get()
        except Exception:
            skip_before = False

        # Build a diagnostic map of actual configured task lists (regardless of
        # Retry mode) so the log shows what tasks are selected, not [] placeholders.
        task_keys_by_device_log: dict[str, list[str]] = {}
        for adb_id in queued:
            dev = self._find_device_record(adb_id)
            dt_log = (dev or {}).get("device_type", "") or ""
            # A: do NOT fall back to SUBTASK_ORDER in diagnostics.  If the
            # DeviceType has no Task Config, show a clear placeholder so the log
            # never implies tasks that won't actually run.
            if dt_log in self.task_config:
                tk_log = list(self.task_config.get(dt_log, []))
                try:
                    tk_log = self._task_sets.expand_keys(tk_log)
                except Exception:
                    pass
                tk_log = [k for k in tk_log if k in TASK_DEFS]
                if not tk_log:
                    tk_log = ["<EMPTY_TASK_CONFIG>"]
            else:
                tk_log = ["<NO_TASK_CONFIG>"]
            task_keys_by_device_log[adb_id] = tk_log

        _multi_log.info(
            f"[RUN-START] selected_count={len(chosen)} "
            f"max_concurrent={mc} queued_count={len(self._run_queue)} "
            f"skip_before={skip_before} retry_on={retry_on}"
        )
        _multi_log.info(f"[RUN-START] selected_ids={chosen}")
        _multi_log.info(f"[RUN-START] queued_ids={queued}")
        _multi_log.info(f"[RUN-START] retry_skipped={retry_skipped}")
        _multi_log.info(f"[RUN-START] task_keys_by_device={task_keys_by_device_log}")
        _multi_log.info(f"[RUN-START] retry_task_keys_by_device={_pending_tasks_by_device}")
        _multi_log.info(f"[RUN] selected_count={len(chosen)}")
        _multi_log.info(f"[RUN] selected_ids={chosen}")
        _multi_log.info(f"[RUN] max_concurrent={mc}")
        _multi_log.info(f"[RUN] queued_count={len(self._run_queue)}")

        # Start internet-down monitor for this run
        self._start_internet_monitor()
        self._run_process_queue()
        # A Run where every device was SKIPPED / NO TASKS / INVALID TASKS
        # launches no worker at all, so no run_done ever arrives. Without this
        # the session would stay active and RUN SELECTED disabled forever.
        self._finish_run_session_if_idle()

    # ── FIX 6: orphan BlueStacks cleanup ─────────────────────────────────────
    def _cleanup_orphan_bluestacks(self):
        """Close extra HD-Player.exe processes beyond max_concurrent limit,
        never touching instances that are currently active."""
        import subprocess as _sp
        import re as _re
        try:
            max_inst = self._max_concurrent.get()
            r = _sp.run(
                ["tasklist", "/fi", "IMAGENAME eq HD-Player.exe", "/fo", "CSV", "/nh"],
                capture_output=True, text=True, timeout=8
            )
            pids = [int(m.group(1)) for m in
                    (_re.search(r'"HD-Player\.exe","(\d+)"', line) for line in r.stdout.splitlines())
                    if m]
            if len(pids) <= max_inst:
                return
            # Map PID -> port via netstat
            nr = _sp.run(["netstat", "-ano", "-p", "tcp"],
                         capture_output=True, text=True, timeout=8)
            pid_port = {}
            for line in nr.stdout.splitlines():
                lm = _re.search(r"0\.0\.0\.0:(\d+)\s+.*LISTENING\s+(\d+)", line)
                if lm:
                    pid_port[int(lm.group(2))] = int(lm.group(1))
            protected = set()
            for aid in list(self._running_devs.keys()) + self._run_queue:
                try: protected.add(int(aid.split(":")[-1]))
                except Exception: pass
            extras = len(pids) - max_inst
            killed = 0
            for pid in pids:
                if killed >= extras: break
                port = pid_port.get(pid)
                if port and port in protected:
                    continue
                try:
                    _sp.run(["taskkill", "/PID", str(pid), "/F"],
                            capture_output=True, timeout=5)
                    _multi_log.info(
                        f"[DIAG] cleanup_orphan ── killed PID {pid} port={port}")
                    killed += 1
                except Exception as ex:
                    _multi_log.warning(f"[DIAG] cleanup_orphan ── kill {pid} failed: {ex}")
            if killed:
                import time as _t; _t.sleep(1.0)
        except Exception as ex:
            _multi_log.debug(f"[DIAG] cleanup_orphan ── skipped: {ex}")

    def _run_pump(self):
        """Alias for _run_process_queue — used by internet_restored_restart handler."""
        self._run_process_queue()

    def _run_process_queue(self):
        if getattr(self, "_shutdown_pending", False):
            _multi_log.info("[QUEUE] shutdown pending — queue pump blocked")
            return
        # Host internet is down: hold the queue exactly where it is.  Devices
        # already running stay running (they pause themselves); nothing new is
        # launched, and nothing is dropped from the queue.
        if getattr(self, "_internet_pause_active", False):
            _multi_log.info(
                f"[INTERNET-PAUSE] queue pump blocked — "
                f"{len(self._run_queue)} device(s) held in place"
            )
            return
        # Hard emergency: every worker has been killed and the emulators closed.
        # Launching anything now would fight the teardown; the restore handler
        # rebuilds the queue and pumps it once the internet is back.
        if getattr(self, "_internet_down_emergency", False):
            _multi_log.info(
                f"[INTERNET] queue pump blocked — hard emergency in progress "
                f"({len(self._run_queue)} device(s) queued)")
            return
        max_c = self._max_concurrent.get()
        # Count ALL active entries (running + stopping) — both consume a device slot
        active_count = len(self._running_devs)
        # NOTE: zombie detection removed — the bridge thread already emits process_died
        # when mp_q.get() times out and proc.is_alive() is False. The old zombie check
        # here fired while run_done messages were still in self.q (unprocessed), causing
        # false positives for devices that had actually succeeded.
        while self._run_queue and active_count < max_c:
            adb_id = self._run_queue.pop(0)
            self._run_launch_one(adb_id)
            # 7: Only count the slot if the device was actually started.
            # Skipped devices (empty task list, no dev_row, etc.) must not
            # consume a concurrency slot — otherwise max_concurrent would be
            # reached prematurely after a run of all-empty-task devices.
            if adb_id in self._running_devs:
                active_count += 1
        # Update queue positions
        for i, qid in enumerate(self._run_queue):
            self._run_set_badge(qid, f"queued ({i+1}/{len(self._run_queue)})", BADGE_QUEUED[0], BADGE_QUEUED[1])
        total_r = sum(1 for v in self._running_devs.values() if v.get("status") == "running")
        total_q = len(self._run_queue)
        self._queue_label.configure(text=f"Queue: {total_r} running, {total_q} waiting")
        if total_r > 0:
            self._set_status(f"● RUNNING  {total_r} device(s)", PRI)
        else:
            self._set_status("● IDLE", FG_DIM)

    def _resolve_run_task_keys(self, adb_id: str) -> dict:
        """
        Decide what a Run-tab launch would do for this device. NO side effects.

        The single source of truth for Run task resolution. The internet-restore
        path used to carry its own copy that simply skipped any DeviceType with
        no Task Config — so a device that a normal Run would have restarted as a
        legitimate prepare_target_app-only setup run was silently dropped from the
        restoration. One resolver, one matrix:

            Retry-mode prefiltered list       -> run (exactly that list)
            Task Config with runnable tasks   -> run
            explicit empty config, skip OFF   -> setup_only  (task_keys = [])
            no config at all, skip OFF        -> setup_only  (task_keys = [])
            empty / no config, skip ON        -> skip
            configured entries, none runnable -> invalid     (never setup_only)

        Returns {"action", "task_keys", "configured", "device_type", "reason"}
        where action is one of run | setup_only | skip | invalid, and for
        `invalid` "badge" carries INVALID TASKS or NO TASKS.
        """
        dev = self._find_device_record(adb_id)
        dt = (dev or {}).get("device_type", "") or ""
        try:
            skip_before = bool(self.skip_var.get())
        except Exception:
            skip_before = False

        def _verdict(action, task_keys=(), configured=(), reason="", badge=None):
            return {"action": action, "task_keys": list(task_keys),
                    "configured": list(configured), "device_type": dt,
                    "reason": reason, "badge": badge}

        # A/L/S10: Normal Run uses Task Config by DeviceType. Never a silent
        # SUBTASK_ORDER fallback. Retry mode's prefiltered list wins outright.
        _retry_override = getattr(self, "_retry_task_keys_by_device", {}) or {}
        if adb_id in _retry_override:
            configured = list(_retry_override[adb_id])
        elif dt in self.task_config:
            configured = list(self.task_config.get(dt, []))
        elif skip_before:
            return _verdict("skip", reason=(
                f"No Task Config for DeviceType '{dt}' and skip_before on"),
                badge="SKIPPED")
        else:
            # No Task Config but skip_before OFF -> valid setup-only run.
            return _verdict("setup_only", reason=(
                f"No Task Config for DeviceType '{dt}', skip_before off — "
                f"prepare_target_app only"))

        # Cheap pre-expansion exit for the skip_before-ON case.
        if not configured and skip_before:
            return _verdict("skip", configured=configured,
                            reason="no tasks and skip_before on", badge="SKIPPED")

        # A stored selection that HAD entries but validated to nothing arrives
        # here already empty, so emptiness alone cannot tell it from a
        # deliberately empty config. The marker recorded at load time can.
        # (Run mode reads task_config[DeviceType]; the Test Multi panel's marker
        # is a different thing and must not affect a Run-tab launch.)
        _invalid = self._invalid_task_config.get(dt)
        if _invalid and not configured:
            return _verdict("invalid", configured=_invalid, reason=(
                f"stored task selection had entries but none are runnable: "
                f"{_invalid}"), badge="INVALID TASKS")

        task_keys = self._task_sets.expand_keys(list(configured))

        # "Configured nothing" and "configured something that turned out to be
        # invalid" must not share an outcome. The second used to fall through as
        # a setup-only run, so a Task Config naming a deleted task quietly ran
        # preparation and reported success.
        if configured and not task_keys:
            return _verdict("invalid", configured=configured, reason=(
                f"every configured task was invalid or missing after "
                f"sanitization/expansion: {configured}"), badge="NO TASKS")

        if not task_keys:
            if skip_before:
                return _verdict("skip", configured=configured, reason=(
                    "no tasks after set expansion and skip_before on"),
                    badge="SKIPPED")
            return _verdict("setup_only", configured=configured, reason=(
                "no tasks configured — running prepare_target_app only"))

        return _verdict("run", task_keys=task_keys, configured=configured,
                        reason=f"{len(task_keys)} runnable task(s)")

    def _run_launch_one(self, adb_id):
        # ── Invariant: one worker per device, ever ────────────────────────────
        # The UI guard and the queue de-duplication should both prevent this, so
        # reaching here means something upstream is wrong — but the cost of
        # continuing is severe: `self._running_devs[adb_id] = info` would replace
        # the live Process, stop_event, pause_event and mp_q of a worker that is
        # still running, orphaning it beyond the reach of Stop One and Stop All.
        # Refuse, loudly, and leave the existing entry exactly as it is.
        if adb_id in self._running_devs:
            _multi_log.error(
                f"[INVARIANT] _run_launch_one({adb_id}) called while a worker is "
                f"already running for that device — refusing to launch a second "
                f"one; the existing worker is untouched")
            try:
                self._run_log_msg(
                    f"⚠ {adb_id}: already running — duplicate launch ignored", "warn")
            except Exception:
                pass
            return

        dev_row = self._run_rows.get(adb_id)
        if not dev_row:
            return

        # One shared resolver — the restore path uses the same one, so the two
        # can no longer disagree about setup-only, skip_before or INVALID TASKS.
        _v = self._resolve_run_task_keys(adb_id)
        _action = _v["action"]
        task_keys = _v["task_keys"]

        # Human-log context: registered (not "attempted") here — the launch
        # token does not exist yet, and the three verdicts below never launch.
        self._human_register_device(adb_id, _v)

        if _action == "skip":
            _multi_log.info(f"[LAUNCH] {adb_id} skipped — {_v['reason']}")
            self._run_log_msg(f"\u23ed {adb_id}: skipped — {_v['reason']}", "warn")
            self._run_set_badge(adb_id, "SKIPPED", BADGE_IDLE[0], BADGE_IDLE[1])
            # Terminal: nothing will ever launch or complete for this device.
            self._human_finalize_device(adb_id, result="skipped", ok=False,
                                        badge="SKIPPED")
            # Note: _running_devs was never populated for this device.
            return

        if _action == "invalid":
            _multi_log.error(f"[LAUNCH] {adb_id} SKIPPED — {_v['reason']}")
            self._run_log_msg(
                f"\u23ed {adb_id}: configured tasks are invalid or missing "
                f"({', '.join(map(str, _v['configured']))}) — nothing runnable",
                "err")
            self._run_set_badge(adb_id, _v["badge"] or "NO TASKS",
                                BADGE_IDLE[0], BADGE_IDLE[1])
            self._human_finalize_device(adb_id, result="invalid_tasks", ok=False,
                                        badge=_v["badge"] or "NO TASKS")
            return

        if _action == "setup_only":
            _multi_log.info(f"[LAUNCH] {adb_id} {_v['reason']} (setup-only run)")
            self._run_log_msg(
                f"\u25b6 {adb_id}: no tasks configured — running prepare_target_app only",
                "info")
            self._run_set_badge(adb_id, "SETUP ONLY",
                                BADGE_RUNNING[0], BADGE_RUNNING[1])
            # Falls through and spawns the worker with task_keys=[].

        # ── Proof log: pre-launch state ───────────────────────────────────────
        try:
            _mc = self._max_concurrent.get()
        except Exception:
            _mc = -1
        _multi_log.info(
            f"[LAUNCH] open_worker_count={len(self._running_devs)} "
            f"queued_remaining={len(self._run_queue)} "
            f"starting_adb_id={adb_id} max_concurrent={_mc}"
        )
        # Keep "SETUP ONLY" visible for a prepare_target_app-only run so it is obvious at
        # a glance that no tasks were configured for this device.
        if task_keys:
            self._run_set_badge(adb_id, "RUNNING", BADGE_RUNNING[0], BADGE_RUNNING[1])
        else:
            self._run_set_badge(adb_id, "SETUP ONLY", BADGE_RUNNING[0], BADGE_RUNNING[1])
        _multi_log.info(
            f"RUN START  {adb_id}  tasks={task_keys}"
            + ("  (setup-only: prepare_target_app, no tasks)" if not task_keys else "")
        )

        stop_ev  = multiprocessing.Event()
        # Separate from stop_ev on purpose — see _mp_worker_entry.  Pausing must
        # never look like stopping to the worker.
        pause_ev = multiprocessing.Event()
        mp_q     = multiprocessing.Queue()

        # ── Launch identity ──────────────────────────────────────────────────
        # Minted HERE, before any path below can emit a completion: the demo
        # thread, cfg_build_failed, proc_start_failed, process_died, the normal
        # all_done, and the two manual stop routes all quote it back. Every
        # early return above this point emits no run_done, so no expected entry
        # is left behind for a device that never launched.
        self._run_launch_token_seq += 1
        _sid = self._run_session_id
        _ltok = self._run_launch_token_seq
        self._run_expected_launch[adb_id] = {
            "session_id": _sid, "launch_token": _ltok}
        # A newer launch supersedes the previous one entirely: its trailing
        # recording_done must no longer be accepted for this device — including
        # one preserved from a launch the emergency killed.
        self._run_recent_completion.pop(adb_id, None)
        self._run_recent_recording_identity.pop(adb_id, None)
        _multi_log.info(
            f"[LAUNCH] {adb_id} identity session={_sid} launch_token={_ltok}")
        # NOT the place to record a human launch attempt. Minting a token is
        # bookkeeping for stale-message protection, not a worker launch: the
        # cfg build and Process.start() below can both still fail, and counting
        # those as attempts made a device that never ran look like it had — and
        # made a later real launch look like a *relaunch*. The attempt is
        # recorded after the actual start() call returns without raising.

        info = {
            "stop_event":  stop_ev,
            "pause_event": pause_ev,
            "mp_q":        mp_q,
            "process":     None,
            "bridge":      None,
            "status":      "running",
            # Carried so a stop route can quote the identity of the worker it is
            # actually stopping, rather than whatever is current when it runs.
            "session_id":   _sid,
            "launch_token": _ltok,
        }

        if self.demo:
            self._running_devs[adb_id] = info
            def _demo():
                for tk_key in task_keys:
                    if stop_ev.is_set():
                        break
                    time.sleep(0.5)
                    self.q.put(("run_log", adb_id, f"✓ {TASK_DEFS[tk_key]['label']}", "ok"))
                    self.q.put(("run_task_done", adb_id, tk_key))
                ok = not stop_ev.is_set()
                self.q.put(("run_done", _sid, _ltok, adb_id, ok,
                            "done" if ok else "stopped"))
            t = threading.Thread(target=_demo, daemon=True)
            info["bridge"] = t
            t.start()
            # The thread is running — only now is this a real launch attempt.
            self._human_note_launch_attempt(adb_id, _ltok)
            return

        # L/S11: Build cfg_data BEFORE adding the device to _running_devs.  If the
        # cfg build fails the device must NOT be left stuck in _running_devs (that
        # would block max-concurrency forever).  Badge FAILED + pump the queue.
        try:
            # Use cached config data — do NOT re-read sheet mid-run
            # Hand the checkbox value to the bridge so _build_cfg_data can carry
            # it to the worker without adding another Process argument.
            self.bridge._record_video_flag = bool(self._record_video.get())
            cfg_data = self.bridge._build_cfg_data()
        except Exception as exc:
            self.q.put(("run_log", adb_id, f"cfg build failed: {exc}", "err"))
            self._run_set_badge(adb_id, "FAILED ✗", BADGE_FAILED[0], BADGE_FAILED[1])
            _multi_log.error(f"[LAUNCH] {adb_id} cfg build failed: {exc} — device NOT queued")
            # Device was never added to _running_devs; emit run_done so the queue
            # pump continues (also clears any retry bookkeeping for this device).
            self.q.put(("run_done", _sid, _ltok, adb_id, False, "cfg_build_failed"))
            return

        # Metadata only — never functions. The worker resolves callables through
        # bot.get_task_callable().
        task_defs_slice = {
            k: {"header": v["header"], "status_attr": v["status_attr"],
                "sub_attr": v.get("sub_attr")}
            for k, v in TASK_DEFS.items()
        }
        # Last line of defence: a stale key — or a "set:" reference that escaped
        # expansion — still must not reach a worker. allow_sets=False, because
        # by this point every key must be something get_task_callable() knows.
        task_keys = sanitize_task_keys(task_keys, where=f"run args for {adb_id}",
                                       allow_sets=False)
        leaked = [k for k in task_keys if k not in TASK_DEFS]
        if leaked:
            _multi_log.error(
                f"[TASKS] {adb_id}: dropping {len(leaked)} key(s) that reached "
                f"the worker arguments despite sanitization: {leaked}")
            task_keys = [k for k in task_keys if k in TASK_DEFS]

        proc = multiprocessing.Process(
            target=_mp_worker_entry,
            args=(adb_id, task_keys, task_defs_slice,
                  cfg_data, self.skip_var.get(), mp_q, stop_ev, pause_ev),
            daemon=True,
        )

        # L/S11: Only register in _running_devs once cfg succeeded and we're about
        # to start the process.  Wrap proc.start() so a start failure cannot leave
        # the device stuck in _running_devs.
        self._running_devs[adb_id] = info
        try:
            proc.start()
        except Exception as exc:
            self._running_devs.pop(adb_id, None)
            self.q.put(("run_log", adb_id, f"proc start failed: {exc}", "err"))
            self._run_set_badge(adb_id, "FAILED ✗", BADGE_FAILED[0], BADGE_FAILED[1])
            _multi_log.error(f"[LAUNCH] {adb_id} proc.start() failed: {exc}")
            self.q.put(("run_done", _sid, _ltok, adb_id, False, "proc_start_failed"))
            return
        info["process"] = proc
        # proc.start() returned without raising, so a worker process really
        # exists. THIS is a launch attempt. Everything above — cfg build,
        # Process construction, a start() that threw — is a failure to launch
        # and must leave the attempt count at 0.
        self._human_note_launch_attempt(adb_id, _ltok)

        def _bridge(_sid=_sid, _ltok=_ltok):
            # The identity is CAPTURED here, as a default argument, not read
            # from the controller when a message arrives. This thread can
            # outlive its launch by seconds; reading self._run_session_id later
            # would let a dead worker's message impersonate the current one.
            while True:
                # If stop was requested, drain remaining messages then exit
                if stop_ev.is_set() and not proc.is_alive():
                    break
                try:
                    msg = mp_q.get(timeout=2.0)
                except Exception:
                    if not proc.is_alive():
                        # Only emit process_died if we weren't the ones who stopped it
                        if not stop_ev.is_set():
                            self.q.put(("run_done", _sid, _ltok, adb_id,
                                        False, "process_died"))
                        break
                    continue
                msg_type = msg.get("type")
                if msg_type == "log":
                    self.q.put(("run_log", adb_id, msg.get("msg", ""), msg.get("tag", "dim")))
                elif msg_type == "task_done":
                    self.q.put(("run_task_done", adb_id, msg.get("task_key", "")))
                elif msg_type == "task_skipped":
                    # J: worker explicitly signals skipped — log only, no dirty write
                    self.q.put(("run_task_skipped", adb_id, msg.get("task_key", "")))
                elif msg_type == "status_update":
                    # D: worker's monkey-patched update_status sends here immediately
                    self.q.put(("run_status_update", adb_id,
                                msg.get("header", ""), msg.get("value", "")))
                elif msg_type == "run_fatal_stop":
                    # C: FatalAPKError — forward immediately before all_done.
                    # Identity-bound: a fatal from a dead attempt must not tear
                    # down a newer Run.
                    self.q.put(("run_fatal_stop", adb_id, msg.get("reason", ""),
                                _sid, _ltok))
                elif msg_type == "recording_done":
                    self.q.put(("recording_done", adb_id, {
                        "folder":     msg.get("folder", ""),
                        "segments":   msg.get("segments", 0),
                        "events":     msg.get("events", 0),
                        "report":     msg.get("report", ""),
                        "duration_s": msg.get("duration_s", 0),
                        # `incomplete` must be forwarded too — dropping it here
                        # collapsed a partial recording into a failed one.
                        "failed":     bool(msg.get("failed")),
                        "incomplete": bool(msg.get("incomplete")),
                    }, _sid, _ltok))
                elif msg_type == "host_internet_pause":
                    # PRIMARY path for host internet down — pause, do not kill.
                    _multi_log.warning(
                        f"[INTERNET-PAUSE] Worker {adb_id} reported host internet down "
                        f"(reason={msg.get('reason')})"
                    )
                    self.q.put(("host_internet_pause", adb_id, _sid, _ltok))
                elif msg_type == "host_internet_back":
                    _multi_log.info(
                        f"[INTERNET-PAUSE] Worker {adb_id} reported host internet back"
                    )
                    self.q.put(("host_internet_back", adb_id, _sid, _ltok))
                elif msg_type == "internet_down_emergency":
                    # Legacy signal. Routed to the pause tier as well: the old
                    # kill/close behaviour is now reserved for manual Stop,
                    # shutdown and user-requested hard reset.
                    _multi_log.warning(
                        f"[INTERNET-PAUSE] Worker {adb_id} signalled legacy "
                        f"internet_down_emergency (reason={msg.get('reason')}) "
                        f"— handling as pause, not emergency stop"
                    )
                    self.q.put(("host_internet_pause", adb_id, _sid, _ltok))
                elif msg_type == "all_done":
                    self.q.put(("run_done", _sid, _ltok, adb_id,
                                msg.get("ok", False), msg.get("result", "")))
                    break

        bt = threading.Thread(target=_bridge, daemon=True)
        info["bridge"] = bt
        bt.start()

    def _apply_worker_msg_to_cache(self, adb_id: str, msg: dict) -> None:
        """
        D/S1: Apply a single worker message DIRECTLY to the controller cache.

        This is the canonical cache-mutation path.  It is shared by:
          - _drain_worker_queue()  (reads raw mp_q dicts)
          - _drain_controller_queue_cache_messages() (re-wraps self.q tuples)

        Handled message types:
          status_update:
            * read header / value; ignore only if header is empty
            * _pending_sheet_status[adb_id][header] = value ; _cache_dirty = True
            * map header → task_key (TASK_DEFS headers + RAW_STATUS_HEADER_TO_TASK)
            * _status_cache[adb_id][task_key] = value
            * rows_by_device update via TASK_DEFS status_attr +
              RAW_STATUS_HEADER_TO_ROW_FIELD
            * persist cache
          task_done:
            * _record_task_done(adb_id, task_key)
          task_skipped:
            * log only — never mark done, never dirty the cache
        """
        msg_type = msg.get("type", "")

        if msg_type == "status_update":
            header = msg.get("header", "")
            value  = msg.get("value", "")
            if not header:
                _multi_log.debug(
                    f"[CACHE] _apply status_update {adb_id} null header "
                    f"value={value!r} — ignored (no column to write)"
                )
                return
            # header → task_key (TASK_DEFS non-None headers first, then raw map)
            _h2t = {v["header"]: k for k, v in TASK_DEFS.items() if v.get("header")}
            task_key = _h2t.get(header) or RAW_STATUS_HEADER_TO_TASK.get(header)
            with self._status_cache_lock:
                self._pending_sheet_status.setdefault(adb_id, {})[header] = value
                if task_key:
                    self._status_cache.setdefault(adb_id, {})[task_key] = value
                self._cache_dirty = True
            # rows_by_device: prefer TASK_DEFS status_attr, fall back to raw map
            row_field = None
            if task_key:
                _sa = TASK_DEFS.get(task_key, {}).get("status_attr")
                if _sa:
                    row_field = _sa.lstrip("_")
            if not row_field:
                row_field = RAW_STATUS_HEADER_TO_ROW_FIELD.get(header)
            if row_field:
                try:
                    row = self.bridge._lookup_row(adb_id)
                    if row:
                        row[row_field] = value
                except Exception:
                    pass
            self._persist_status_cache()
            _multi_log.debug(
                f"[CACHE] _apply status_update {adb_id} header={header!r} "
                f"value={value!r} task_key={task_key!r} → dirty + persisted"
            )

        elif msg_type == "task_done":
            task_key = msg.get("task_key", "")
            if task_key:
                self._record_task_done(adb_id, task_key, "done")

        elif msg_type == "task_skipped":
            # J: log only — already done; no dirty cache write, never mark done
            task_key = msg.get("task_key", "")
            _multi_log.info(
                f"[CACHE] _apply task_skipped {adb_id} {task_key!r} — "
                f"log only, not marked done"
            )
        # All other message types (log, all_done, run_fatal_stop, internet…) are
        # NOT cache-affecting and are intentionally ignored here.

    def _drain_controller_queue_cache_messages(self, reason: str = "") -> int:
        """
        D/S3: Drain self.q and apply cache-affecting messages DIRECTLY.

        The per-device bridge thread continuously moves messages from each
        worker's mp_q into self.q.  By the time Stop All / Close / Fatal /
        Internet-emergency run, some in-flight status updates may already have
        been forwarded into self.q and not yet processed by _poll().  Those must
        be applied to the cache BEFORE any final cache→sheet sync, or they are
        lost.

        Behaviour:
          * directly apply run_status_update / run_task_done / run_task_skipped
          * preserve ALL non-cache messages by re-queuing them into self.q in
            their original relative order (so _poll still handles run_done,
            run_fatal_stop, run_log, etc.)
          * returns count of cache messages applied
        """
        preserved: list = []
        applied = 0
        while True:
            try:
                item = self.q.get_nowait()
            except Empty:
                break
            except Exception:
                break
            kind = item[0] if item else None
            if kind == "run_status_update":
                _, adb_id, header, value = item
                self._apply_worker_msg_to_cache(
                    adb_id, {"type": "status_update", "header": header, "value": value}
                )
                applied += 1
            elif kind == "run_task_done":
                _, adb_id, task_key = item
                self._apply_worker_msg_to_cache(
                    adb_id, {"type": "task_done", "task_key": task_key}
                )
                applied += 1
            elif kind == "run_task_skipped":
                _, adb_id, task_key = item
                self._apply_worker_msg_to_cache(
                    adb_id, {"type": "task_skipped", "task_key": task_key}
                )
                applied += 1
            else:
                preserved.append(item)
        # Re-queue preserved (non-cache) messages in original order
        for item in preserved:
            try:
                self.q.put(item)
            except Exception:
                pass
        if applied:
            _multi_log.info(
                f"[DRAIN-Q] applied {applied} cache message(s) from controller "
                f"queue (reason={reason or 'n/a'}); "
                f"preserved {len(preserved)} non-cache message(s)"
            )
        return applied

    def _drain_worker_queue(self, adb_id: str, mp_q, reason: str = "",
                            session_id=None, launch_token=None) -> int:
        """
        D/S2: Drain a worker's mp_q and apply cache-affecting messages DIRECTLY
        via _apply_worker_msg_to_cache() — NOT merely forward them to self.q.

        Applying directly guarantees that status_update / task_done updates are
        committed to the controller cache before a final sync, even if the
        bridge thread is mid-shutdown and would never deliver them to self.q.

        Non-cache messages (log, all_done, run_fatal_stop, internet_*) are
        intentionally dropped here because this drain is only used on the
        force-stop / shutdown / emergency paths where those are no longer
        actionable.  Returns count of cache messages applied.
        """
        applied = 0
        while True:
            try:
                msg = mp_q.get_nowait()
            except Exception:
                break
            msg_type = msg.get("type", "")
            if msg_type in ("status_update", "task_done", "task_skipped"):
                # DELIBERATELY NOT identity-bound. These are idempotent cache
                # writes: they record "device X finished task T", which is true
                # regardless of which attempt produced it, and re-applying one is
                # a no-op. Attaching an identity here would make a late-but-
                # correct status update from a killed worker get discarded, and
                # losing a completed task is worse than recording it twice.
                self._apply_worker_msg_to_cache(adb_id, msg)
                applied += 1
            elif msg_type == "recording_done":
                # Must NOT be dropped: it carries the recording folder and report
                # paths, and on the shutdown/grace paths this drain is the only
                # thing still reading the worker queue. Identity taken from the
                # worker's own info dict — this drain runs for a specific worker.
                # Identity comes from the CALLER when it has one. Looking it
                # up in _running_devs was wrong on the most important path: the
                # grace drain runs after _on_run_done popped the entry, so the
                # lookup returned {} and the recording was forwarded with
                # None/None — then rejected, losing the folder/report paths.
                _d_sid, _d_tok = session_id, launch_token
                if _d_sid is None and _d_tok is None:
                    _d_info = (self._running_devs.get(adb_id) or {})
                    _d_sid = _d_info.get("session_id")
                    _d_tok = _d_info.get("launch_token")
                self.q.put(("recording_done", adb_id, {
                    "folder":     msg.get("folder", ""),
                    "segments":   msg.get("segments", 0),
                    "events":     msg.get("events", 0),
                    "report":     msg.get("report", ""),
                    "duration_s": msg.get("duration_s", 0),
                    "failed":     bool(msg.get("failed")),
                    "incomplete": bool(msg.get("incomplete")),
                }, _d_sid, _d_tok))
                applied += 1
            # Ignore log / all_done / run_fatal_stop / internet_* on forced
            # stop. Dropping all_done is correct here because every route that
            # reaches this function OWNS the terminal result it will emit:
            # Stop All, Safe Reset, controller close and the fatal abort all
            # pass an explicit `terminal_result`. No caller relies on the
            # worker's own all_done surviving this drain — see the fatal
            # handler, which states its ownership model explicitly.
        if applied:
            _multi_log.info(
                f"[STOP] drained+applied {applied} cache message(s) from "
                f"{adb_id} mp_q (reason={reason or 'n/a'})"
            )
        return applied

    def _force_stop_worker_process(self, adb_id: str, reason: str = "stop_all",
                                   terminal_result: str = "stopped",
                                   grace_s: float = 0.0) -> None:
        """
        E: Kill a worker process without closing the emulator window.
        Drains the worker queue before AND after kill to capture in-flight updates.
        Emits run_done(terminal_result) so _on_run_done cleans up _running_devs.

        `terminal_result` exists because the synthetic result is only correct
        when the CONTROLLER owns the reason for stopping. On the fatal-abort
        route the worker's own terminal result carries the FatalAPKError cause,
        and `_drain_worker_queue` discards all_done — so a plain "stopped"
        would overwrite the only record of why the Run died.

        `grace_s` lets a worker that is already inside its own `_finalize()`
        finish writing `recording stopped —`, its counter snapshot and
        `[WORKER-END]` before it is killed. Bounded; never waits indefinitely.
        """
        info = self._running_devs.get(adb_id)
        if not info:
            return

        # 1. Signal stop
        ev = info.get("stop_event")
        if ev:
            ev.set()
        info["status"] = "stopping"
        self._run_set_badge(adb_id, "STOPPING…", BADGE_STOPPING[0], BADGE_STOPPING[1])

        # 2. Drain queue BEFORE kill — catch any in-flight updates already sent.
        #    Drain BOTH the worker mp_q (raw messages) AND the controller self.q
        #    (messages the bridge thread already forwarded) so nothing is lost.
        mp_q = info.get("mp_q")
        if mp_q is not None:
            self._drain_worker_queue(adb_id, mp_q, reason=reason,
                                     session_id=info.get("session_id"),
                                     launch_token=info.get("launch_token"))
        self._drain_controller_queue_cache_messages(reason=f"{reason}:pre-kill")

        # 2b. Bounded grace: a worker already running its own _finalize() is
        # about to write its real terminal evidence. Killing it now would
        # discard records that genuinely exist.
        proc = info.get("process")
        if grace_s > 0 and proc is not None and proc.is_alive():
            _deadline = time.time() + grace_s
            while time.time() < _deadline and proc.is_alive():
                time.sleep(0.1)
            _multi_log.info(
                f"[STOP] {reason} ── {adb_id} grace {grace_s:.1f}s: "
                f"{'exited on its own' if not proc.is_alive() else 'still alive'}")
            if mp_q is not None:
                self._drain_worker_queue(
                    adb_id, mp_q, reason=f"{reason}:post-grace",
                    session_id=info.get("session_id"),
                    launch_token=info.get("launch_token"))

        # 3. Terminate / kill process
        if proc is not None and proc.is_alive():
            _multi_log.info(f"[STOP] {reason} ── {adb_id} terminating subprocess")
            try:
                proc.terminate()
                proc.join(timeout=3)
            except Exception:
                pass
            if proc.is_alive():
                _multi_log.warning(f"[STOP] {reason} ── {adb_id} force-killing subprocess")
                try:
                    proc.kill()
                except Exception:
                    pass

        # 4. Drain queue AFTER kill — catch any last messages sent before death.
        if mp_q is not None:
            self._drain_worker_queue(adb_id, mp_q, reason=reason,
                                     session_id=info.get("session_id"),
                                     launch_token=info.get("launch_token"))
        self._drain_controller_queue_cache_messages(reason=f"{reason}:post-kill")

        # 5. Update badge
        self._run_set_badge(adb_id, "STOPPED", BADGE_STOPPED[0], BADGE_STOPPED[1])
        # This route deliberately leaves the emulator window open. Recording
        # that as an unknown close would let the report imply a close failed.
        info["close_disposition"] = "not_requested_stop_all"

        # 6. Emit run_done so _on_run_done can pop from _running_devs.
        #    result="stopped" causes _on_run_done to skip emulator close.
        #    Quote the identity of the worker actually being stopped, taken from
        #    its own info dict — not whatever is current when this runs.
        # Carry any close outcome this Run already recorded for the device, so
        # a Stop All that requests no close still reports attempt 1's failed or
        # unverified close.
        _fhas, _fprev = self._human_close_history(adb_id)
        if _fhas:
            info["prior_close_result"] = _fprev
        self.q.put(("run_done", info.get("session_id"), info.get("launch_token"),
                    adb_id, False, terminal_result))
        _multi_log.info(
            f"[STOP] {reason} ── {adb_id} process killed, no emulator close, "
            f"terminal_result={terminal_result!r}")

    def _run_stop_one(self, adb_id, close_emulator: bool = True):
        """
        Stop one device immediately.
        close_emulator=True (default): terminate process AND close emulator window.
        close_emulator=False: terminate process only (used by Stop All).
        """
        if close_emulator:
            # Original behaviour: kill process + close emulator
            info = self._running_devs.get(adb_id)
            if info:
                self._persist_status_cache()
                info["stop_event"].set()
                info["status"] = "stopping"
            self._run_set_badge(adb_id, "STOPPING…", BADGE_STOPPING[0], BADGE_STOPPING[1])
            # Whichever state it was in, this device is no longer retrying.
            _retry_cancelled = self._cancel_one_run_retry(adb_id, reason="stop_one")
            _was_queued = adb_id in self._run_queue
            if _was_queued:
                self._run_queue.remove(adb_id)
                # STOPPED, not IDLE: the user stopped this device. IDLE claimed
                # it was simply never asked to run, which is wrong and made a
                # deliberate stop indistinguishable from a fresh row.
                self._run_set_badge(adb_id, "STOPPED", BADGE_STOPPED[0], BADGE_STOPPED[1])
                # Removing the last queued device can end the session, and no
                # run_done follows for a device that never started. A generic
                # "stopped" read as though a worker had been killed, and left
                # the close disposition blank for a device that never opened a
                # window.
                # `_run_queue` membership is a scheduling position, not a
                # launch history: _run_requeue puts a device that already ran
                # back here to wait for a concurrency slot. Only a device with
                # no recorded attempt is genuinely pre-launch.
                if self._human_ever_launched(adb_id):
                    # Stop One must resolve the window, never report Stop All's
                    # policy — the user pressed Stop One on a device that
                    # already opened one.
                    _qok, _qdisp, _qprior = self._stop_one_resolve_close(adb_id)
                    self._human_finalize_device(
                        adb_id, result="stopped", ok=False, badge="STOPPED",
                        close_ok=_qok, close_disposition=_qdisp,
                        prior_close_result=_qprior)
                else:
                    self._human_finalize_device(
                        adb_id, result="stopped_before_launch", ok=False,
                        badge="STOPPED",
                        close_disposition="not_applicable_never_launched")
                self._finish_run_session_if_idle()

            # ── Retry-only stop ──────────────────────────────────────────────
            # No worker, not queued, but a delayed retry was pending: cancelling
            # the callback is the whole stop. Nothing else will ever emit
            # run_done for this device, so without this the badge stays
            # STOPPING… forever and the session never completes.
            if _retry_cancelled and info is None and not _was_queued:
                _multi_log.info(
                    f"[STOP] _run_stop_one ── {adb_id} was waiting on an ADB retry; "
                    f"callback cancelled — no process to kill")
                try:
                    self._run_log_msg(
                        f"■ {adb_id.split(':')[-1]}: pending ADB retry cancelled", "warn")
                except Exception:
                    pass
                self._run_set_badge(adb_id, "STOPPED", BADGE_STOPPED[0], BADGE_STOPPED[1])
                # There IS no live worker, but that does not prove there is no
                # window. This device reached the retry state through
                # adb_connect_failed, which already ran a close — and that close
                # may have FAILED. Claiming "no emulator to close" would then
                # silently abandon a known zombie.
                # Identical contract to the requeued case above.
                _rc_ok, _rc_disp, _rc_prior = self._stop_one_resolve_close(adb_id)
                self._human_finalize_device(
                    adb_id, result="stopped", ok=False, badge="STOPPED",
                    close_ok=_rc_ok, close_disposition=_rc_disp,
                    prior_close_result=_rc_prior)
                self._finish_run_session_if_idle()
                return

            if info:
                proc = info.get("process")
                if proc is not None and proc.is_alive():
                    _multi_log.info(f"[STOP] _run_stop_one ── {adb_id} terminating subprocess immediately")
                    try:
                        proc.terminate()
                        proc.join(timeout=3)
                    except Exception:
                        pass
                    if proc.is_alive():
                        _multi_log.warning(f"[STOP] _run_stop_one ── {adb_id} force-killing subprocess")
                        try:
                            proc.kill()
                        except Exception:
                            pass

                _multi_log.info(f"[CLOSE_EMU] manual stop close start adb_id={adb_id}")
                try:
                    bot = self.bridge.bot if hasattr(self.bridge, "bot") else None
                    ok = self._close_emulator_for_device(adb_id, bot, timeout=15)
                except Exception as ex:
                    # An exception OUTSIDE the helper proves nothing about the
                    # window. False would claim it is confirmed still open.
                    ok = None
                    _multi_log.warning(
                        f"[CLOSE_EMU] manual stop close error adb_id={adb_id}: "
                        f"{ex} — closure UNVERIFIED")
                _multi_log.info(f"[CLOSE_EMU] manual stop close result adb_id={adb_id} ok={ok}")
                # Stop One really does close the window, and that result is a
                # controller outcome worth reporting. run_done's `ok` means "the
                # RUN succeeded", so overloading it would say the close failed
                # whenever a user pressed Stop. The result rides on the live
                # launch's own info dict instead, which _on_run_done pops.
                # NOT bool(ok): the helper is tri-state, and None means the
                # close could not be verified — reporting that as a confirmed
                # failure would be as wrong as reporting it as success.
                info["manual_close_ok"] = ok
                info["close_disposition"] = self._close_disposition_for(ok)
                self._run_last_close[adb_id] = ok

                # Identity of the worker this stop actually killed.
                self.q.put(("run_done", info.get("session_id"),
                            info.get("launch_token"), adb_id, False, "stopped"))
        else:
            self._force_stop_worker_process(adb_id, reason="stop_one_no_close")

    def _run_stop_all(self, final_sync: bool = True, exclude=None,
                      terminal_result: str = "stopped"):
        """
        E: Stop all running devices immediately.
        Kills worker processes but does NOT close emulator windows.
        Drains each worker queue before/after kill to preserve in-flight updates.

        final_sync:
          True  (normal Stop All) — schedule the final cache→sheet sync here.
          False (fatal-stop path) — skip the sync here so the caller can perform
                exactly one controlled SYNCHRONOUS final sync before its popup,
                avoiding the double-sync race where a background sync holds the
                non-blocking sync lock and the caller's synchronous flush skips.
        """
        # 7: ensure future runs are not blocked
        self._shutdown_pending = True
        self._persist_status_cache()

        # 0. Cancel every pending ADB retry. A device sitting in its ten-second
        # retry window has no worker to kill, so without this it would quietly
        # re-queue itself after the user pressed Stop All.
        self._human_snapshot_pending_retries()
        self._cancel_run_retries(reason="stop_all")
        # Stop All is an intentional abandonment: invalidate any hard-emergency
        # ownership so the session can finish. The old wait thread may still
        # enqueue its now-stale identity, which the handler rejects.
        self._cancel_hard_internet_emergency(reason="stop_all")
        # The pause tier too: otherwise the next Run's queue is still held by a
        # pause whose monitor has already gone away.
        self._cancel_internet_pause(reason="stop_all")

        # 1. Clear queue so no new devices start
        # Devices that were only WAITING on an ADB retry have no worker to kill,
        # so no run_done will ever arrive for them: they are terminal here.
        _retry_only = list(getattr(self, "_human_pending_retry_snapshot", []) or [])
        discarded = list(self._run_queue)
        self._run_queue.clear()
        if discarded:
            _multi_log.info(f"[STOP-ALL] discarded {len(discarded)} queued device(s): {discarded}")
            for qid in discarded:
                self._run_set_badge(qid, "STOPPED", BADGE_STOPPED[0], BADGE_STOPPED[1])
                # Queued and never launched — nothing else will report it.
                # Same distinction as Stop One — a requeued device already
                # ran, and already had a window.
                if self._human_ever_launched(qid):
                    _qhas, _qprev = self._human_close_history(qid)
                    self._human_finalize_device(
                        qid, result="stopped", ok=False, badge="STOPPED",
                        close_disposition="not_requested_stop_all",
                        prior_close_result=_qprev if _qhas else "no_attempt")
                else:
                    self._human_finalize_device(
                        qid, result="stopped_before_launch", ok=False,
                        badge="STOPPED",
                        close_disposition="not_applicable_never_launched")
        for _rid in _retry_only:
            self._run_set_badge(_rid, "STOPPED", BADGE_STOPPED[0], BADGE_STOPPED[1])
            # Stop All's close policy applies to these too. Leaving the
            # disposition blank made the report silent about the window, which
            # reads as "no information" rather than "deliberately left open".
            # The PRIOR close outcome travels separately: Stop All requesting
            # no close does not un-know a failed close from attempt 1.
            _rhas, _rprev = self._human_close_history(_rid)
            self._human_finalize_device(
                _rid, result="stopped", ok=False, badge="STOPPED",
                close_disposition="not_requested_stop_all",
                prior_close_result=_rprev if _rhas else "no_attempt")

        _skip = set(exclude or ())
        running_ids = [d for d in self._running_devs if d not in _skip]
        _multi_log.info(
            f"[STOP-ALL] stopping {len(running_ids)} running device(s) "
            f"(no emulator close)"
            + (f"; {len(_skip)} excluded: {sorted(_skip)}" if _skip else ""))

        # 2. Kill each process (drain + kill + drain), no emulator close
        for adb_id in running_ids:
            self._force_stop_worker_process(adb_id, reason="stop_all",
                                            terminal_result=terminal_result)

        # 3. Final controller-queue drain — apply anything the bridge threads
        #    forwarded into self.q during the kill loop BEFORE the final sync.
        self._drain_controller_queue_cache_messages(reason="stop_all:final")

        # 4. Final cache→sheet sync (in background so UI stays responsive).
        #    Skipped when final_sync=False — the fatal handler does its own
        #    single synchronous flush instead.
        if not final_sync:
            _multi_log.info("[STOP-ALL] final_sync=False — caller will perform final sync")
            return
        if self._cache_dirty:
            _multi_log.info("[STOP-ALL] dirty cache detected — scheduling final sheet sync")
            threading.Thread(target=self._flush_pending_sheet_status, daemon=True).start()
        else:
            _multi_log.info("[STOP-ALL] cache clean — no final sync needed")

        # Stop All is a terminal route: if the kills already drained
        # _running_devs the session is over now. If run_done messages are still
        # in flight, _on_run_done finishes it instead.
        self._finish_run_session_if_idle()



    # ── Status cache ──────────────────────────────────────────────────────────

    def _load_status_cache(self) -> None:
        """Load persisted status cache from disk on startup.
        JSON shape: {"completed": {...}, "pending_sheet": {...}}
        Backward-compat: also accepts old {"status": {...}} shape.

        Fix 2: sets _cache_dirty = True whenever pending_sheet_status is
        non-empty, so _flush_pending_sheet_status() does not skip them.
        """
        try:
            p = Path(STATUS_CACHE_FILE)
            if p.exists():
                data = json.loads(p.read_text(encoding="utf-8"))
                completed = data.get("completed", data.get("status", {})) or {}
                pending   = data.get("pending_sheet", {}) or {}

                # ── Sanitize a cache written by an older, 39-task build ──────
                # Left alone, it would put deleted task keys back into
                # _status_cache and — worse — flush their pending headers to
                # Sheets, where _find_or_create_status_col() would recreate the
                # obsolete columns. The old columns may stay in the spreadsheet;
                # this build simply never writes them again.
                dropped_tasks = dropped_headers = 0
                clean_completed = {}
                for dev, entries in completed.items():
                    if not isinstance(entries, dict):
                        continue
                    keep = {k: v for k, v in entries.items() if k in TASK_DEFS}
                    dropped_tasks += len(entries) - len(keep)
                    if keep:
                        clean_completed[dev] = keep

                clean_pending = {}
                for dev, headers in pending.items():
                    if not isinstance(headers, dict):
                        continue
                    keep = {h: v for h, v in headers.items()
                            if h not in DELETED_TASK_HEADERS}
                    dropped_headers += len(headers) - len(keep)
                    if keep:
                        clean_pending[dev] = keep

                with self._status_cache_lock:
                    self._status_cache = clean_completed
                    self._pending_sheet_status = clean_pending
                    # Fix 2: pending writes from a previous crash must be flushed;
                    # mark dirty so _flush_pending_sheet_status will not exit early.
                    # Computed from the CLEANED data, so a cache holding nothing
                    # but deleted headers no longer forces a pointless flush.
                    self._cache_dirty = bool(self._pending_sheet_status)

                if dropped_tasks or dropped_headers:
                    _multi_log.warning(
                        f"[CACHE] discarded stale entries from "
                        f"{STATUS_CACHE_FILE}: {dropped_tasks} completed task "
                        f"entry(ies), {dropped_headers} pending sheet header(s) "
                        f"belonging to removed tasks")
                    self._persist_status_cache()

                pending_count = sum(len(v) for v in self._pending_sheet_status.values())
                _multi_log.info(
                    f"[CACHE] Loaded status cache: "
                    f"{sum(len(v) for v in self._status_cache.values())} entries, "
                    f"{pending_count} pending sheet writes"
                    + (" (dirty=True — will flush)" if self._cache_dirty else "")
                )
        except Exception as e:
            _multi_log.warning(f"[CACHE] Could not load status cache: {e}")

    def _persist_status_cache(self) -> None:
        """Persist status cache to disk immediately. Never raises."""
        try:
            with self._status_cache_lock:
                data = {
                    "completed": self._status_cache,
                    "pending_sheet": self._pending_sheet_status,
                    "saved_at": datetime.now().isoformat(),
                }
            Path(STATUS_CACHE_FILE).write_text(
                json.dumps(data, indent=2), encoding="utf-8"
            )
        except Exception as e:
            _multi_log.warning(f"[CACHE] persist_status_cache failed: {e}")

    def _rebuild_status_cache_from_sheet(self) -> None:
        """
        Fix 1: Build _status_cache[adb_id][task_key] from bridge.rows_by_device.
        Called after run_daily_reset() so cache reflects the post-reset sheet.
        Does not touch _pending_sheet_status or _cache_dirty.
        Uses the same task_key → row_field mapping as status_snapshot().
        """
        # Mapping: task_key → row dict field name (mirrors status_snapshot)
        _TASK_KEY_TO_ROW_FIELD: dict[str, str] = {
            "vip_collect":       "vip_collect_status",
        }
        rebuilt: dict[str, dict[str, str]] = {}
        try:
            for adb_id, row in self.bridge.rows_by_device.items():
                device_cache: dict[str, str] = {}
                for task_key, row_field in _TASK_KEY_TO_ROW_FIELD.items():
                    val = (row.get(row_field) or "").strip()
                    if val:
                        device_cache[task_key] = val
                if device_cache:
                    rebuilt[adb_id] = device_cache
        except Exception as exc:
            _multi_log.warning(f"[CACHE] _rebuild_status_cache_from_sheet failed: {exc}")
            return

        with self._status_cache_lock:
            # Replace only the completed-task entries; leave pending_sheet untouched
            self._status_cache = rebuilt
        self._persist_status_cache()
        total = sum(len(v) for v in rebuilt.values())
        _multi_log.info(
            f"[CACHE] _rebuild_status_cache_from_sheet: {total} entries "
            f"across {len(rebuilt)} device(s)"
        )

    def _apply_pending_sheet_status_to_local_cache(self) -> None:
        """
        Overlay _pending_sheet_status onto _status_cache and rows_by_device.

        Called immediately after _rebuild_status_cache_from_sheet() in the
        did_reset=False path.  Without this, a controller crash before the
        first sync could leave _status_cache seeded from a stale sheet, making
        Retry believe a task is pending even though a newer 'done' value is
        sitting in _pending_sheet_status (not yet flushed to Sheets).

        header_to_task is built from TASK_DEFS (non-None headers) plus
        RAW_STATUS_HEADER_TO_TASK so header=None tasks are covered too (that map
        is currently empty — no live task uses a raw header).

        header_to_row_field is derived from TASK_DEFS status_attr names plus
        RAW_STATUS_HEADER_TO_ROW_FIELD; no hardcoded duplicates.

        Safe to call when _pending_sheet_status is empty (no-op).
        Must NOT be called after did_reset=True because _pending_sheet_status
        was intentionally cleared and would have no entries to overlay.
        """
        # Build header → task_key (covers all non-None TASK_DEFS headers + raw-header tasks)
        header_to_task: dict[str, str] = {
            v["header"]: k for k, v in TASK_DEFS.items() if v.get("header")
        }
        header_to_task.update(RAW_STATUS_HEADER_TO_TASK)   # currently empty

        # Build header → row_field dynamically from TASK_DEFS status_attr values
        # (status_attr = "_vip_collect_status" → row_field = "vip_collect_status")
        header_to_row_field: dict[str, str] = {
            v["header"]: v["status_attr"].lstrip("_")
            for k, v in TASK_DEFS.items()
            if v.get("header") and v.get("status_attr")
        }
        header_to_row_field.update(RAW_STATUS_HEADER_TO_ROW_FIELD)  # currently empty

        with self._status_cache_lock:
            pending_snapshot = {
                dev_id: dict(updates)
                for dev_id, updates in self._pending_sheet_status.items()
            }

        if not pending_snapshot:
            return

        overlay_count = 0
        for adb_id, updates in pending_snapshot.items():
            for header, value in updates.items():
                # Overlay into _status_cache by task_key
                task_key = header_to_task.get(header)
                if task_key:
                    with self._status_cache_lock:
                        self._status_cache.setdefault(adb_id, {})[task_key] = value
                    overlay_count += 1

                # Overlay into rows_by_device so status_snapshot() sees the newer value
                row_field = header_to_row_field.get(header)
                if row_field:
                    try:
                        row = self.bridge._lookup_row(adb_id)
                        if row:
                            row[row_field] = value
                    except Exception:
                        pass

        self._persist_status_cache()
        _multi_log.info(
            f"[CACHE] _apply_pending_sheet_status_to_local_cache: "
            f"overlaid {overlay_count} newer value(s) from pending writes "
            f"onto _status_cache / rows_by_device for {len(pending_snapshot)} device(s)"
        )

    def _record_task_done(self, adb_id: str, task_key: str, status: str = "done") -> None:
        """
        Record a completed task in the in-memory cache and persist to disk.
        Also populates pending_sheet_status for deferred Sheets flush.
        Called immediately when a worker signals task_done.

        M/S12: Also writes the value into bridge.rows_by_device so that
        status_snapshot() and the Sheet tab reflect the cache without a Sheets
        read.  row_field is derived from TASK_DEFS status_attr (stripped of the
        leading underscore), with RAW_STATUS_HEADER_TO_ROW_FIELD covering the
        header=None tasks (none at present).
        """
        td = TASK_DEFS.get(task_key, {})
        header = td.get("header") or None   # None for tasks with no direct sheet column
        with self._status_cache_lock:
            # 1. Local task-key cache (always — even if no sheet header)
            self._status_cache.setdefault(adb_id, {})[task_key] = status
            # 2. Pending sheet write (only when header exists and is non-None)
            if header:
                self._pending_sheet_status.setdefault(adb_id, {})[header] = status
                self._cache_dirty = True   # D: mark dirty for next sync

        # 3. M/S12: write into rows_by_device so status_snapshot() is cache-accurate
        row_field = None
        status_attr = td.get("status_attr")
        if status_attr:
            row_field = status_attr.lstrip("_")
        if not row_field and header:
            row_field = RAW_STATUS_HEADER_TO_ROW_FIELD.get(header)
        if row_field:
            try:
                row = self.bridge._lookup_row(adb_id)
                if row:
                    row[row_field] = status
            except Exception:
                pass

        self._persist_status_cache()
        _multi_log.info(
            f"[CACHE] {adb_id} → task={task_key!r} header={header!r} "
            f"status={status!r} row_field={row_field!r} persisted "
            f"(pending_sheet={header is not None})"
        )

    def _flush_pending_sheet_status(self) -> None:
        """
        E: Public entry point — acquires _sheet_sync_lock so overlapping sync
        threads never run concurrently.  If a flush is already running this call
        is skipped (the in-flight flush will write everything currently pending).
        The real work is done in _flush_pending_sheet_status_impl().
        """
        if not self._sheet_sync_lock.acquire(blocking=False):
            _multi_log.info("[SYNC] flush already running — skipping duplicate")
            return
        try:
            self._flush_pending_sheet_status_impl()
        finally:
            self._sheet_sync_lock.release()

    def _flush_pending_sheet_status_impl(self) -> None:
        """
        D: Cache → Google Sheets batch sync.
        Assembles all pending header/value writes across all devices into a single
        ws.batch_update() call.  Falls back to per-device bot.update_status +
        flush_status only if the batch path raises an exception.

        Fix 3: Only clears (dev_id, header) pairs that were actually included in
        the batch payload.  Pairs skipped due to missing row, missing column, or
        null header are kept in _pending_sheet_status for the next sync attempt.

        Called via _flush_pending_sheet_status() (which holds _sheet_sync_lock)
        from: _schedule_sheet_sync (60s tick), _on_run_done (end of run),
        _on_close, _run_stop_all, fatal-stop handler, internet-restored handler.
        """
        with self._status_cache_lock:
            pending = {k: dict(v) for k, v in self._pending_sheet_status.items()}

        if not pending:
            _multi_log.debug("[SYNC] _flush_pending_sheet_status — nothing pending, skipping")
            return
        if not self._cache_dirty:
            _multi_log.debug("[SYNC] _flush_pending_sheet_status — cache not dirty, skipping")
            return

        total_cells = sum(len(v) for v in pending.values())
        _multi_log.info(
            f"[SYNC] starting batch flush: {total_cells} cell(s) "
            f"across {len(pending)} device(s)"
        )

        try:
            bot = self.bridge.bot
            if bot is None:
                raise RuntimeError("bot module not loaded")

            ws = bot._get_control_ws()
            batch_data = []

            # 3: Track exactly which (dev_id, header) pairs make it into batch_data
            written_pairs: list[tuple[str, str]] = []

            for dev_id, updates in pending.items():
                key = dev_id.strip().lower()
                device_row = bot._DEVICE_ROW_CACHE.get(key)

                if device_row is None:
                    _multi_log.warning(
                        f"[SYNC] {dev_id} not in _DEVICE_ROW_CACHE — "
                        f"falling back to col scan"
                    )
                    try:
                        colA = bot._sheets_call(ws.col_values, 1)
                        colB = bot._sheets_call(ws.col_values, 2)
                        last = max(len(colA), len(colB))
                        for row in range(bot.DATA_START_ROW, last + 1):
                            a = (colA[row - 1] if row - 1 < len(colA) else "").strip().lower()
                            b = (colB[row - 1] if row - 1 < len(colB) else "").strip().lower()
                            if key == a or key == b:
                                device_row = row
                                bot._DEVICE_ROW_CACHE[key] = row
                                break
                    except Exception as scan_err:
                        _multi_log.warning(
                            f"[SYNC] row scan failed for {dev_id}: {scan_err}"
                        )

                if device_row is None:
                    # 3: Row not found — keep all updates for this device pending
                    _multi_log.warning(
                        f"[SYNC] {dev_id}: no sheet row found — "
                        f"{len(updates)} update(s) kept pending for next sync"
                    )
                    continue

                for header_name, status_value in updates.items():
                    if not header_name:
                        # Null-header — cannot write, skip silently
                        _multi_log.debug(
                            f"[SYNC] {dev_id}: skipping null-header update value={status_value!r}"
                        )
                        continue
                    try:
                        col_idx = bot._find_or_create_status_col(
                            ws, header_name,
                            start_col_idx=bot.STATUS_FIRST_COL,
                        )
                        a1 = f"{bot._col_index_to_a1(col_idx)}{device_row}"
                        batch_data.append({"range": a1, "values": [[status_value]]})
                        # 3: Record that this pair made it into the batch
                        written_pairs.append((dev_id, header_name))
                        _multi_log.debug(
                            f"[SYNC] {dev_id} {header_name}={status_value!r} → {a1}"
                        )
                    except Exception as col_err:
                        # 3: Col lookup failed — keep this pair pending
                        _multi_log.warning(
                            f"[SYNC] col lookup failed {dev_id}/{header_name}: {col_err} "
                            f"— kept pending"
                        )

            if batch_data:
                bot._sheets_call(
                    ws.batch_update, batch_data, value_input_option="USER_ENTERED"
                )
                _multi_log.info(f"[SYNC] batch_update wrote {len(batch_data)} cell(s) ✓")
            else:
                _multi_log.info("[SYNC] batch assembled 0 writable cells — nothing to write")

            # 3: Clear ONLY the (dev_id, header) pairs that were successfully written
            if written_pairs:
                with self._status_cache_lock:
                    for dev_id, header_name in written_pairs:
                        dev_pending = self._pending_sheet_status.get(dev_id)
                        if dev_pending is not None:
                            dev_pending.pop(header_name, None)
                            if not dev_pending:
                                self._pending_sheet_status.pop(dev_id, None)

            # Mark clean only if everything was written (no skipped rows/cols remain)
            with self._status_cache_lock:
                still_pending = bool(self._pending_sheet_status)
            if not still_pending:
                self._cache_dirty = False

            self._persist_status_cache()
            skipped = total_cells - len(written_pairs)
            _multi_log.info(
                f"[SYNC] done — wrote {len(written_pairs)}, "
                f"kept pending {skipped} (row/col not found)"
            )

        except Exception as exc:
            _multi_log.warning(
                f"[SYNC] batch update failed: {exc} — falling back to per-device flush"
            )
            # Fallback: use bot.update_status + flush_status per device.
            # NOTE: this path calls Sheets directly from the controller process,
            # which is intentional for the fallback case.
            try:
                bot = self.bridge.bot
                if bot is not None:
                    fallback_written: list[tuple[str, str]] = []
                    for dev_id, updates in pending.items():
                        for header, value in updates.items():
                            if header:
                                bot.update_status(dev_id, header, value)
                                fallback_written.append((dev_id, header))
                        bot.flush_status(dev_id)
                    # 3: Clear only written pairs in fallback too
                    with self._status_cache_lock:
                        for dev_id, header_name in fallback_written:
                            dev_pending = self._pending_sheet_status.get(dev_id)
                            if dev_pending is not None:
                                dev_pending.pop(header_name, None)
                                if not dev_pending:
                                    self._pending_sheet_status.pop(dev_id, None)
                    with self._status_cache_lock:
                        still_pending = bool(self._pending_sheet_status)
                    if not still_pending:
                        self._cache_dirty = False
                    self._persist_status_cache()
                    _multi_log.info(
                        f"[SYNC] fallback flush completed: {len(fallback_written)} pair(s)"
                    )
            except Exception as exc2:
                _multi_log.warning(f"[SYNC] fallback flush also failed: {exc2}")

    # ── Internet-down emergency monitor ───────────────────────────────────────

    def _start_internet_monitor(self) -> None:
        """
        Start a background thread that watches _GLOBAL_INTERNET_DOWN_EVENT
        (set by guard inside the bot subprocess when internet has been down >40s).
        When triggered: save cache → kill all subprocesses → close all emulators
        → wait for internet → restart.
        """
        if (self._internet_monitor_thread is not None
                and self._internet_monitor_thread.is_alive()):
            return
        self._internet_monitor_stop.clear()
        t = threading.Thread(target=self._internet_monitor_loop, daemon=True,
                             name="internet_monitor")
        self._internet_monitor_thread = t
        t.start()
        _multi_log.info("[INTERNET] Internet monitor started")

    def _stop_internet_monitor(self) -> None:
        self._internet_monitor_stop.set()

    def _internet_monitor_loop(self) -> None:
        # NOTE: We no longer watch bot._GLOBAL_INTERNET_DOWN_EVENT here because
        # in multiprocessing mode each worker has its own bot module copy — the
        # threading.Event set by the worker is invisible to the controller process.
        # Instead, workers push {"type": "internet_down_emergency"} to status_q,
        # and the bridge thread forwards it as ("run_log"/"internet_down_emergency")
        # to self.q. This loop is now a no-op placeholder; internet-down is
        # handled entirely via the queue in _handle_bridge_message().
        while not self._internet_monitor_stop.is_set():
            time.sleep(2.0)

    # Port-verification outcomes. UNKNOWN is NOT "free": a netstat that could
    # not run tells us nothing, and treating silence as proof of closure was
    # exactly the bug that let an unverified close be reported as SUCCESS.
    PORT_LISTENING = "listening"
    PORT_FREE = "free"
    PORT_UNKNOWN = "unknown"

    def _close_emulator_for_device(self, adb_id: str, bot=None,
                                   timeout: int = 10):
        """
        Close a BlueStacks emulator for the given adb_id.

        Returns TRI-STATE, never a bare bool:
            True  — confirmed closed (netstat positively shows the port free)
            False — confirmed still open after normal close AND taskkill
            None  — a close was attempted but closure could not be VERIFIED
                    (no port to check, or netstat unavailable/erroring)

        `True` may only come from positive evidence. Callers must not coerce
        the result with bool(): that turns "unverified" into "failed", and the
        previous version's exception-to-False mapping turned it into "closed".
        """
        import re as _re
        port = adb_id.split(":")[-1] if ":" in adb_id else ""
        bot_ = bot or (self.bridge.bot if hasattr(self.bridge, "bot") else None)

        _multi_log.info(f"[CLOSE_EMU] close start adb_id={adb_id}")

        # Resolve window name via bot helper or conf_devices fallback
        wn = None
        try:
            if bot_:
                wn = bot_.get_window_name_from_shortcut(adb_id)
            if not wn:
                wn = self._find_device_record(adb_id).get("name", "")
        except Exception:
            pass

        _multi_log.info(f"[CLOSE_EMU] window name={wn!r} adb_id={adb_id}")

        if wn:
            try:
                bot_.close_window_by_title(wn)
                _multi_log.info(f"[CLOSE_EMU] normal close attempted adb_id={adb_id} window={wn!r}")
            except Exception as e:
                _multi_log.warning(f"[CLOSE_EMU] close_window_by_title failed adb_id={adb_id}: {e}")
        else:
            _multi_log.warning(f"[CLOSE_EMU] no window name resolved — skipping title-close adb_id={adb_id}")

        def _port_state() -> str:
            """LISTENING / FREE / UNKNOWN — never guesses."""
            if not port:
                # Nothing to check against. That is not evidence of closure.
                return self.PORT_UNKNOWN
            try:
                r = subprocess.run(
                    ["netstat", "-ano", "-p", "tcp"],
                    capture_output=True, text=True, timeout=5
                )
            except Exception as _pe:
                _multi_log.warning(
                    f"[CLOSE_EMU] port verification unavailable adb_id={adb_id}: "
                    f"{_pe!r} — closure NOT verified")
                return self.PORT_UNKNOWN
            if getattr(r, "returncode", 0) not in (0, None):
                _multi_log.warning(
                    f"[CLOSE_EMU] netstat returned {r.returncode} adb_id={adb_id} "
                    f"— closure NOT verified")
                return self.PORT_UNKNOWN
            out = getattr(r, "stdout", None)
            if out is None:
                _multi_log.warning(
                    f"[CLOSE_EMU] netstat produced no output adb_id={adb_id} "
                    f"— closure NOT verified")
                return self.PORT_UNKNOWN
            for line in out.splitlines():
                if f":{port}" in line and "LISTENING" in line:
                    return self.PORT_LISTENING
            return self.PORT_FREE

        t0 = time.time()
        state = self.PORT_UNKNOWN
        while time.time() - t0 < timeout:
            state = _port_state()
            if state == self.PORT_FREE:
                _multi_log.info(f"[CLOSE_EMU] verified closed adb_id={adb_id} ok=True")
                _multi_log.info(f"[CLOSE_EMU] close result adb_id={adb_id} ok=True")
                return True
            # LISTENING and UNKNOWN both keep polling: netstat may recover, and
            # a still-listening port may yet close within the timeout.
            time.sleep(0.5)

        if state == self.PORT_UNKNOWN:
            # Never once got a usable reading, so the fallback cannot even find
            # a PID. Claiming success or failure here would both be invented.
            _multi_log.warning(
                f"[CLOSE_EMU] close result adb_id={adb_id} ok=UNVERIFIED "
                f"(port state never determined after {timeout}s)")
            return None

        # Still alive — find HD-Player PID by port and taskkill (device-specific only)
        _multi_log.warning(
            f"[CLOSE_EMU] verified closed adb_id={adb_id} ok=False "
            f"(port {port} still LISTENING after {timeout}s) — attempting taskkill"
        )
        final_ok = False
        try:
            ns = subprocess.run(
                ["netstat", "-ano", "-p", "tcp"],
                capture_output=True, text=True, timeout=5
            ).stdout
            pid = None
            for line in (ns or "").splitlines():
                if f":{port}" in line and "LISTENING" in line:
                    m = _re.search(r"(\d+)\s*$", line.strip())
                    if m:
                        pid = m.group(1)
                        break
            if pid:
                _multi_log.info(f"[CLOSE_EMU] fallback taskkill pid={pid} adb_id={adb_id}")
                subprocess.run(["taskkill", "/F", "/PID", pid], capture_output=True, timeout=5)
                time.sleep(1.0)
                # Re-verify. If verification is unavailable NOW, the result is
                # unverified — the taskkill may well have worked.
                after = _port_state()
                if after == self.PORT_UNKNOWN:
                    _multi_log.warning(
                        f"[CLOSE_EMU] close result adb_id={adb_id} ok=UNVERIFIED "
                        f"(post-taskkill verification unavailable)")
                    return None
                final_ok = (after == self.PORT_FREE)
            else:
                _multi_log.warning(f"[CLOSE_EMU] fallback taskkill — no PID found for port {port} adb_id={adb_id}")
        except Exception as e:
            _multi_log.warning(f"[CLOSE_EMU] fallback taskkill error adb_id={adb_id}: {e}")
            # The fallback itself failed, so the emulator's state is unknown.
            _multi_log.warning(
                f"[CLOSE_EMU] close result adb_id={adb_id} ok=UNVERIFIED "
                f"(fallback raised)")
            return None
        _multi_log.info(f"[CLOSE_EMU] close result adb_id={adb_id} ok={final_ok}")
        return final_ok

    def _current_run_device_ids(self) -> set:
        """
        Returns the union of all device IDs that belong to the current run:
          - explicitly selected at run-start (_current_run_selected_ids)
          - currently running (_running_devs)
          - queued but not yet started (_run_queue)
        Used by _handle_internet_down_emergency to limit close/restart scope
        to only the devices the user selected, not every scanned device.
        """
        ids = set(self._current_run_selected_ids)
        ids.update(self._running_devs.keys())
        ids.update(self._run_queue)
        return ids

    # ==========================================================================
    # RECORDING RESULTS
    # ==========================================================================

    def _on_recording_done(self, adb_id: str, info: dict) -> None:
        """
        A device finished and reported where its recording landed.

        Surfaces the folder in the Run log and remembers it so the Log Analyzer
        can point at the matching recording later.
        """
        folder = (info or {}).get("folder", "")
        if not folder:
            return

        # Keep the WHOLE dict: Log Analyzer and later UI work read both flags.
        self._recording_paths[adb_id] = dict(info or {})
        segs   = info.get("segments", 0)
        evts   = info.get("events", 0)
        secs   = info.get("duration_s", 0)
        # Three distinct outcomes, not two. A device that kept most of its video
        # but lost one segment used to be shown as "recording failed", which read
        # as though nothing had been captured.
        failed     = bool(info.get("failed"))
        incomplete = bool(info.get("incomplete"))

        _multi_log.info(
            f"[RECORD] {adb_id} recording saved: {folder} "
            f"segments={segs} events={evts} duration={secs}s "
            f"failed={failed} incomplete={incomplete}"
        )
        tag = "warn" if (failed or incomplete) else "ok"
        self.q.put(("run_log", adb_id, f"Recording saved: {folder}", tag))
        if failed:
            note = "  [video recording failed — event timeline may still be available]"
        elif incomplete:
            note = "  [video partially incomplete — valid segments were saved]"
        else:
            note = ""
        self.q.put(("run_log", adb_id,
                    f"   {segs} segment(s), {evts} event(s), {secs}s" + note,
                    "dim"))
        report = info.get("report", "")
        if report:
            self.q.put(("run_log", adb_id, f"   report: {report}", "dim"))
        # One-click access; harmless no-op if the platform has no opener.
        self.q.put(("run_log", adb_id,
                    "   (double-click this line's folder path to open it, "
                    "or use Open recordings folder below)", "dim"))

    def _open_recordings_folder(self, adb_id: str = "") -> None:
        """Open a recording folder in the OS file browser. Best-effort only."""
        target = ""
        if adb_id and adb_id in self._recording_paths:
            target = self._recording_paths[adb_id].get("folder", "")
        if not target:
            for info in self._recording_paths.values():
                if info.get("folder"):
                    target = os.path.dirname(info["folder"])
                    break
        if not target:
            target = "recordings"
        try:
            target = os.path.abspath(target)
            if not os.path.exists(target):
                self._log(f"No recordings folder yet ({target})", "warn")
                return
            if sys.platform.startswith("win"):
                os.startfile(target)                       # noqa: S606
            elif sys.platform == "darwin":
                subprocess.Popen(["open", target])
            else:
                subprocess.Popen(["xdg-open", target])
            self._log(f"Opened {target}", "dim")
        except Exception as exc:
            self._log(f"Could not open recordings folder: {exc}", "warn")

    # ==========================================================================
    # HOST-INTERNET PAUSE TIER  (primary response to host internet down)
    # ==========================================================================
    # This is what runs when the PC loses internet.  It holds every device in
    # place and touches nothing else.  The emergency stop below it — which kills
    # subprocesses and closes emulators — is retained but is NO LONGER used for
    # this condition; it is reserved for manual Stop, controller shutdown, and
    # user-requested hard reset.
    #
    # Why pause rather than kill: a host outage says nothing about any device.
    # Killing workers throws away a partially-completed run, closing emulators
    # costs minutes of boot time on the way back, and both would have to be
    # redone the moment the router comes back.  Nothing about the outage is
    # improved by destroying state.

    def _enter_internet_pause(self, dev_id=None) -> None:
        """
        Enter the global host-internet pause.

        Deliberately does NOT: terminate subprocesses, close emulators, clear
        the run queue, or touch any recovery counter.  Running workers detect
        the outage themselves and pause in place; this method's job is to stop
        the controller starting anything new while that is true.
        """
        if dev_id:
            self._internet_pause_devices.add(dev_id)

        if self._internet_pause_active:
            # ── Is the pause actually being watched? ─────────────────────────
            # `active=True` with a dead monitor and no owner is a permanent
            # latch: nothing will ever post a resume, so the queue never pumps
            # again. Returning early on the flag alone is what made that
            # unrecoverable. Detect it and rebuild the pause instead.
            _t = self._internet_pause_thread
            _alive = bool(_t is not None and _t.is_alive())
            if _alive and self._internet_pause_owner is not None:
                _multi_log.info(
                    f"[INTERNET-PAUSE] already active "
                    f"({time.time() - self._internet_pause_started_at:.0f}s) — "
                    f"device {dev_id} joined the wait"
                )
                return
            _multi_log.error(
                f"[INTERNET-PAUSE] stale pause detected (monitor_alive={_alive}, "
                f"owner={self._internet_pause_owner}) — rotating ownership so a "
                f"resume can still arrive")
            # Ownership rotation ONLY. _cancel_internet_pause no longer touches
            # pause_event, so the workers stay paused continuously across the
            # repair — there is no clear→set window in which a worker could
            # resume into a network that is still down. The reported devices are
            # kept because the outage they reported has not ended.
            _keep = set(self._internet_pause_devices)
            self._cancel_internet_pause(reason="stale monitor — re-entering")
            self._internet_pause_devices |= _keep

        self._internet_pause_active     = True
        self._internet_pause_started_at = time.time()
        # Mint the owner BEFORE the monitor starts, so the thread can capture it.
        self._internet_pause_token_seq += 1
        _pause_sid = getattr(self, "_run_session_id", 0)
        _pause_tok = self._internet_pause_token_seq
        self._internet_pause_owner = {
            "session_id": _pause_sid, "token": _pause_tok}
        _multi_log.info(
            f"[INTERNET-PAUSE] pause owner session={_pause_sid} token={_pause_tok}")

        running = sorted(self._running_devs.keys())
        queued  = list(self._run_queue)
        _multi_log.warning("[INTERNET-PAUSE] HOST INTERNET DOWN — pausing in place")
        _multi_log.warning(
            f"[INTERNET-PAUSE] holding running={running} queued={queued} "
            f"(no kills, no emulator closes, no counter changes)"
        )

        # ── Actively signal every running worker to hold ──────────────────────
        # Holding the launch queue alone is not enough: devices already mid-run
        # would keep clicking, recovering and reinstalling into a dead network.
        # pause_event is checked at every action/checkpoint path in the bot.
        signalled = []
        for adb_id, info in list(self._running_devs.items()):
            ev = info.get("pause_event")
            if ev is not None:
                try:
                    ev.set()
                    signalled.append(adb_id)
                except Exception as exc:
                    _multi_log.warning(
                        f"[INTERNET-PAUSE] could not set pause_event for {adb_id}: {exc}"
                    )
            else:
                _multi_log.warning(
                    f"[INTERNET-PAUSE] {adb_id} has no pause_event (older worker) "
                    f"— it will still self-pause on its own host check"
                )
        _multi_log.warning(f"[INTERNET-PAUSE] pause_event set for {signalled}")
        self.q.put(("run_log", "",
                    "[INTERNET] Host internet down — all devices paused in place "
                    "(nothing closed, nothing killed)", "warn"))
        self._set_status("● PAUSED  host internet down", BADGE_RETRY[1])

        # Persist what we know now so a later hard stop cannot lose it.
        try:
            self._persist_status_cache()
        except Exception as exc:
            _multi_log.warning(f"[INTERNET-PAUSE] status cache persist failed: {exc}")

        # Unconditional: a newly minted owner ALWAYS gets its own monitor. The
        # liveness of a superseded thread must never decide this.
        self._start_internet_pause_monitor(_pause_sid, _pause_tok)

    def _internet_pause_poll_loop(self, session_id=None, token=None) -> None:
        """
        Poll host internet once a second until it returns, then resume.

        Passive, like the hard-emergency wait thread: it polls and enqueues an
        IDENTITY, and changes no controller state itself. `session_id`/`token`
        are the pause this loop was started for — it may only resume that one.
        """
        while self._internet_pause_active:
            time.sleep(1.0)
            if getattr(self, "_shutdown_pending", False):
                _multi_log.info(
                    f"[INTERNET-PAUSE] shutdown pending — abandoning pause loop "
                    f"(session={session_id} token={token})")
                return
            # A newer pause (or a cancellation) has taken ownership; this loop
            # is obsolete and must not post a resume for someone else's pause.
            # Exact ownership — session AND token, matching the queue handler.
            # Tokens are monotonic so token alone happens to work today, but the
            # owner contract is a pair and an asymmetric check is a trap waiting
            # for the first non-monotonic change.
            _own = getattr(self, "_internet_pause_owner", None)
            if (_own is None
                    or _own.get("session_id") != session_id
                    or _own.get("token") != token):
                # It may log and leave. It may NOT clear the pause, clear worker
                # events, pump, flush, or overwrite _internet_pause_thread —
                # that reference belongs to whoever owns the pause now.
                _multi_log.info(
                    f"[INTERNET-PAUSE] poll loop (session={session_id} "
                    f"token={token}) superseded by {_own} — exiting")
                return
            if _host_internet_ok():
                break
        if self._internet_pause_active:
            self.q.put(("host_internet_resume", session_id, token))

    def _start_internet_pause_monitor(self, session_id, token) -> None:
        """
        Start THIS owner's monitor and store it as the current one.

        Deliberately unconditional. Deciding by `_internet_pause_thread.is_alive()`
        was the bug: a superseded monitor can report alive for several seconds
        while it sits inside a ping/HTTPS timeout, so a freshly minted owner
        would skip creating its own. The old thread then noticed the new token,
        exited as stale, and the NEW pause was left active with no monitor and
        no way to ever resume.

        The old thread is never joined — it is a daemon, and its captured token
        already makes it harmless.
        """
        t = threading.Thread(
            target=self._internet_pause_poll_loop,
            args=(session_id, token), daemon=True,
            name=f"internet_pause_poll_{token}",
        )
        self._internet_pause_thread = t
        t.start()
        _multi_log.info(
            f"[INTERNET-PAUSE] monitor started for session={session_id} "
            f"token={token}")

    def _cancel_internet_pause(self, reason: str = "") -> bool:
        """
        Invalidate CONTROLLER pause ownership. Does not resume any worker.

        This is deliberately NOT a resume. It used to clear every running
        worker's pause_event, which inverted the stop ordering: Stop All called
        this first and only then set stop_event, so a paused worker was released
        back into a dead network for a moment before being told to stop.

        It does not need to release anyone. The bot's wait_while_paused() polls
        stop_event every 0.5s while pause_event stays set, so a stop is honoured
        from inside the pause gate. Leaving pause_event set is strictly safer:
        the worker performs no clicks, no reinstalls and no recovery while it
        waits for the stop it is about to receive.

        _exit_internet_pause() is the ONLY path that clears worker pause_events,
        because that is the only one that means host internet genuinely returned.

        Also does not pump the queue: every caller is stopping.
        """
        _own = getattr(self, "_internet_pause_owner", None)
        _was_active = getattr(self, "_internet_pause_active", False)
        if not _own and not _was_active:
            return False
        self._internet_pause_owner = None
        self._internet_pause_active = False
        self._internet_pause_devices.clear()
        # Detach the monitor reference so the next owner always gets its own,
        # regardless of whether this one is still physically alive.
        self._internet_pause_thread = None
        _multi_log.info(
            f"[INTERNET-PAUSE] pause ownership invalidated (was {_own}); "
            f"worker pause_events deliberately LEFT SET — stop_event is what "
            f"releases them{' — ' + reason if reason else ''}")
        return True

    def _exit_internet_pause(self) -> None:
        """
        Leave the pause and let the queue flow again.

        Workers resume from their own safe checkpoints without being told:
          setup phases  -> restart_prepare_target_app
          task runtime  -> back to main screen, restart the current task
          Loading()     -> click OK if the popup is up, continue Loading
        """
        if not self._internet_pause_active:
            return
        waited = time.time() - self._internet_pause_started_at
        self._internet_pause_active = False
        self._internet_pause_owner = None
        self._internet_pause_devices.clear()
        # Detach: this monitor's work is done, and the next pause must not be
        # talked out of creating its own by a thread that is still winding down.
        self._internet_pause_thread = None

        # ── Release every running worker ──────────────────────────────────────
        # Cleared BEFORE anything else: each worker is sitting in its own pause
        # gate waiting on this event, and each resumes from its own safe
        # checkpoint (setup -> restart_prepare_target_app, Loading -> continue Loading,
        # task runtime -> back to main screen and restart the current task).
        released = []
        for adb_id, info in list(self._running_devs.items()):
            ev = info.get("pause_event")
            if ev is not None:
                try:
                    ev.clear()
                    released.append(adb_id)
                except Exception as exc:
                    _multi_log.warning(
                        f"[INTERNET-PAUSE] could not clear pause_event for {adb_id}: {exc}"
                    )
        _multi_log.info(f"[INTERNET-PAUSE] pause_event cleared for {released}")

        _multi_log.info(
            f"[INTERNET-PAUSE] host internet restored after {waited:.0f}s — resuming"
        )
        self.q.put(("run_log", "",
                    f"[INTERNET] Host internet restored after {waited:.0f}s — resuming",
                    "ok"))
        try:
            self._flush_pending_sheet_status()
        except Exception as exc:
            _multi_log.warning(f"[INTERNET-PAUSE] sheet flush on resume failed: {exc}")
        # Devices still running never stopped; only the launcher was held.
        self._run_process_queue()

    def _handle_internet_down_emergency(self) -> None:
        """
        HARD internet-down emergency: kill every subprocess and close emulators.

        RETAINED BUT NO LONGER THE DEFAULT for host internet loss — see
        _enter_internet_pause() above, which is the primary path.  Keep this for:
          * manual Stop
          * controller shutdown
          * user-requested hard reset
          * an explicit pause-timeout escalation, if one is added later

        Steps:
          1. Log the event.
          2. Save status cache.
          3. Terminate all bot subprocesses immediately.
          4. Close emulator windows for current-run devices only.
          5. Poll host internet every 1s.
          6. When internet returns, restart unfinished current-run devices.
        """
        if self._internet_down_emergency:
            return   # already handling

        # ── There must be a live Run to protect ──────────────────────────────
        # Creating an owner with no Run made the controller permanently busy:
        # _hard_emergency_owns_session() held the session open, and the eventual
        # restore was then rejected for "session no longer active" — leaving the
        # owner latched with nothing able to clear it. Decide BEFORE touching a
        # single emergency field, starting a thread, or closing an emulator.
        _owned = (self._running_devs or self._run_queue
                  or getattr(self, "_run_retry_after_ids", None)
                  or getattr(self, "_run_expected_launch", None))
        if not getattr(self, "_run_session_active", False) or not _owned:
            _multi_log.warning(
                f"[INTERNET] hard emergency requested with no live Run "
                f"(session_active={getattr(self, '_run_session_active', False)} "
                f"running={len(self._running_devs)} queued={len(self._run_queue)} "
                f"retries={len(getattr(self, '_run_retry_after_ids', {}))} "
                f"expected={len(getattr(self, '_run_expected_launch', {}))}) "
                f"— nothing to stop; ignoring")
            return

        self._internet_down_emergency = True
        # The emergency belongs to THIS session AND to a unique token. The wait
        # thread can outlive it by minutes; when it finally posts the restore
        # message the run may have been stopped, replaced by a different one, or
        # a SECOND emergency may already be in progress — which a session id
        # alone cannot distinguish.
        _emergency_sid = self._run_session_id
        self._internet_emergency_token_seq += 1
        _emergency_tok = self._internet_emergency_token_seq
        self._internet_emergency_owner = {
            "session_id": _emergency_sid, "token": _emergency_tok}
        _multi_log.info(
            f"[INTERNET] emergency owner session={_emergency_sid} "
            f"token={_emergency_tok}")
        _multi_log.error("[INTERNET] GLOBAL INTERNET DOWN confirmed")
        _multi_log.error("[INTERNET] GLOBAL INTERNET DOWN — emergency stop triggered")
        self.q.put(("run_log", "", "[INTERNET] GLOBAL INTERNET DOWN — stopping all devices", "err"))

        # 1. Save cache
        self._persist_status_cache()

        # 2. Collect current-run device IDs BEFORE clearing state
        run_ids = self._current_run_device_ids()
        _multi_log.info(f"[INTERNET] current_run_ids={sorted(run_ids)}")

        # 3. Kill all subprocesses immediately.
        # I: drain each worker mp_q AND the controller self.q BEFORE killing so
        # in-flight status updates are committed to the cache, then again AFTER.
        running_ids = list(self._running_devs.keys())
        for adb_id in running_ids:
            info = self._running_devs.get(adb_id)
            if info:
                # I: drain BEFORE kill
                mp_q = info.get("mp_q")
                if mp_q is not None:
                    self._drain_worker_queue(
                        adb_id, mp_q, reason="internet:pre-kill",
                        session_id=info.get("session_id"),
                        launch_token=info.get("launch_token"))
                try: info.get("stop_event") and info["stop_event"].set()
                except Exception: pass
                proc = info.get("process")
                if proc and proc.is_alive():
                    _multi_log.warning(f"[INTERNET] killing subprocess adb_id={adb_id}")
                    try: proc.terminate()
                    except Exception: pass
                    try: proc.join(timeout=2)
                    except Exception: pass
                    try:
                        if proc.is_alive(): proc.kill()
                    except Exception: pass
                # I: drain AFTER kill
                if mp_q is not None:
                    self._drain_worker_queue(
                        adb_id, mp_q, reason="internet:post-kill",
                        session_id=info.get("session_id"),
                        launch_token=info.get("launch_token"))
                info["status"] = "internet_killed"
                # This launch is over — the emergency killed it deliberately.
                # Leaving its expectation armed meant that if restoration then
                # decided the device was complete/skipped/invalid and never
                # relaunched it, the identity outlived the session and a late
                # completion from the killed worker was accepted. Only the
                # EXACT matching expectation is removed.
                _exp = self._run_expected_launch.get(adb_id)
                if _exp and _exp.get("session_id") == info.get("session_id") \
                        and _exp.get("launch_token") == info.get("launch_token"):
                    self._run_expected_launch.pop(adb_id, None)
                    self._run_recent_completion.pop(adb_id, None)
                    # Recording metadata from this exact launch stays admissible
                    # — and only recording metadata.
                    self._run_recent_recording_identity[adb_id] = dict(_exp)
                    _multi_log.info(
                        f"[IDENTITY] emergency invalidated the launch expectation "
                        f"for {adb_id} ({_exp}) — run_done/fatal/pause from that "
                        f"launch are now stale; its recording_done is still "
                        f"accepted")
        # I: drain controller queue cache messages after all kills
        self._drain_controller_queue_cache_messages(reason="internet:post-kill")
        # Keep snapshot of what was running; clear running/queue state
        queued_ids = list(self._run_queue)
        # Devices whose only claim on this session is a pending ADB retry. They
        # have no worker and are not queued, so without collecting them here
        # they would be dropped from the run entirely — and their callbacks,
        # cancelled a line below, would never restart them.
        retry_ids = list(getattr(self, "_run_retry_after_ids", {}) or {})
        if retry_ids:
            _multi_log.info(
                f"[INTERNET] absorbing {len(retry_ids)} retry-only device(s) into "
                f"the restart set: {sorted(retry_ids)}")
        self._cancel_run_retries(reason="internet emergency")
        self._internet_killed_ids = set(running_ids)
        # The three CATEGORIES are kept apart, not merged. Restoration needs to
        # know which a device was in: a device that was only QUEUED never ran
        # prepare_target_app at all, so "its tasks all look done" says nothing about
        # whether it still needs to run — the old single union made it
        # indistinguishable from a device that genuinely finished.
        self._internet_running_ids = set(running_ids)
        self._internet_queued_ids = set(queued_ids)
        self._internet_retry_ids = set(retry_ids)
        # Retained as the union for anything that just needs "was in this run".
        self._internet_restart_ids = (
            set(running_ids) | set(queued_ids) | set(retry_ids))
        _multi_log.info(f"[INTERNET] restart_ids={sorted(self._internet_restart_ids)}")
        self._running_devs.clear()
        self._run_queue.clear()

        # 4. Close emulator windows for current-run devices ONLY
        # (not every device in active_devices — user may have others open)
        try:
            bot = self.bridge.bot
            for adb_id in sorted(run_ids):
                _multi_log.info(f"[INTERNET] closing emulator adb_id={adb_id}")
                try:
                    ok = self._close_emulator_for_device(adb_id, bot, timeout=10)
                except Exception as _cex:
                    # Outside the helper's own tri-state handling, so the
                    # window's state is unknown — not a confirmed failure.
                    ok = None
                    _multi_log.warning(
                        f"[INTERNET] close_emulator raised adb_id={adb_id}: "
                        f"{_cex} — UNVERIFIED")
                # Tri-state: truthiness alone would report an UNVERIFIED close
                # as a confirmed FAILED one.
                status_str = ("OK" if ok is True
                              else "FAILED" if ok is False else "UNVERIFIED")
                # Same-Run close evidence. Hard-internet recovery deliberately
                # relaunches unfinished devices INSIDE this Run, so a failed or
                # unverified close here is exactly the history a later Stop
                # All / Safe Reset report must still be able to state. The
                # tri-state is stored raw — bool() would turn UNVERIFIED into a
                # confirmed failure. A NEW Run clears it in _run_start_selected.
                self._run_last_close[adb_id] = ok
                _multi_log.info(f"[INTERNET] close_emulator adb_id={adb_id} result={status_str}")
        except Exception as e:
            _multi_log.warning(f"[INTERNET] Error closing emulators: {e}")

        _multi_log.info("[INTERNET] all running emulators close attempts complete")
        self.q.put(("run_log", "", "[INTERNET] All processes killed + emulators closed — waiting for internet", "warn"))
        _multi_log.info("[INTERNET] waiting for host internet to return")

        # 5. Poll for internet return.
        #
        # This thread is deliberately PASSIVE. It may poll and enqueue, nothing
        # else. It used to clear _internet_down_emergency and flush Sheets from
        # off the Tk thread — so an old thread could unlatch a NEWER emergency
        # and race the UI. Every controller-state change now happens in the
        # queue handler, after ownership is validated.
        def _wait_and_restart(_sid=_emergency_sid, _tok=_emergency_tok):
            while True:
                time.sleep(1.0)
                if _host_internet_ok():
                    break

            _multi_log.info(
                f"[INTERNET] host internet returned (emergency session={_sid} "
                f"token={_tok})")
            # IDENTITY ONLY. The old unconditional "restarting unfinished
            # devices" line was written here, before ownership was proven — so a
            # run the user had already stopped still announced a restart that
            # never happened. The handler logs it after validating.
            self.q.put(("internet_restored_restart", _sid, _tok))

        threading.Thread(target=_wait_and_restart, daemon=True).start()

    # Grace period before force-terminating a worker that has announced it is
    # done. The worker now sends all_done only AFTER cleanup, so in practice it
    # is already on its way out — but a slow final `adb pull` of the last video
    # segment can still be in flight, and killing it there loses the segment and
    # can leave the manifest/report unwritten.
    RUN_DONE_GRACE_SECONDS = 20

    def _run_identity_matches(self, adb_id, session_id, launch_token,
                              what: str = "completion") -> bool:
        """
        Does this message belong to the launch this controller is waiting on?

        The expected entry is the single source of truth: `_run_expected_launch`
        is rewritten by every launch attempt, so attempt 1's late message cannot
        satisfy attempt 2's expectation even though both share a session id.
        When a running info dict exists its stored identity must agree too —
        that catches a message whose expectation was already consumed.
        """
        # An identity-less message can never be attributed to a launch, and
        # acting on one closes emulators and rewrites badges. This controller
        # only ever emits the six-element form, so anything without an identity
        # is malformed or from a build that no longer exists: parse it
        # defensively so _poll cannot crash, then discard it.
        if session_id is None and launch_token is None:
            _multi_log.warning(
                f"[IDENTITY] identity-less {what} for {adb_id} discarded — "
                f"it cannot be attributed to a launch (expected="
                f"{(getattr(self, '_run_expected_launch', None) or {}).get(adb_id)})")
            return False
        expected = (getattr(self, "_run_expected_launch", None) or {}).get(adb_id)
        if expected is None:
            _multi_log.info(
                f"[IDENTITY] stale {what} for {adb_id} "
                f"(session={session_id} token={launch_token}) — nothing expected; ignored")
            return False
        if (expected.get("session_id") != session_id
                or expected.get("launch_token") != launch_token):
            _multi_log.warning(
                f"[IDENTITY] stale {what} for {adb_id} "
                f"(session={session_id} token={launch_token}) does not match the "
                f"expected launch {expected} — ignored entirely")
            return False
        info = self._running_devs.get(adb_id)
        if info is not None and (
                info.get("session_id") != session_id
                or info.get("launch_token") != launch_token):
            _multi_log.warning(
                f"[IDENTITY] {what} for {adb_id} matches the expectation but not "
                f"the live worker (worker session={info.get('session_id')} "
                f"token={info.get('launch_token')}) — ignored entirely")
            return False
        return True

    def _run_control_identity_matches(self, adb_id, session_id, launch_token,
                                      what: str = "control") -> bool:
        """
        Stricter gate for DESTRUCTIVE control messages.

        Launch identity alone is not enough for these. A fatal or a pause can
        match its launch perfectly and still be obsolete: Stop One may already
        have marked the worker "stopping", Stop All may have set
        _shutdown_pending, or the run may be being abandoned. Acting then shows
        a fatal popup for a run the user already stopped, or starts a global
        pause with nothing left to pause.

        Deliberately NOT used for run_done — a stopping worker's completion is
        exactly what the cleanup path is waiting for.
        """
        if not self._run_identity_matches(adb_id, session_id, launch_token,
                                          what=what):
            return False
        if not getattr(self, "_run_session_active", False):
            _multi_log.warning(
                f"[IDENTITY] {what} for {adb_id} ignored — the Run session is "
                f"no longer active")
            return False
        if getattr(self, "_shutdown_pending", False):
            _multi_log.warning(
                f"[IDENTITY] {what} for {adb_id} ignored — a stop/shutdown is "
                f"already in progress")
            return False
        info = self._running_devs.get(adb_id)
        if info is None:
            _multi_log.warning(
                f"[IDENTITY] {what} for {adb_id} ignored — no live worker")
            return False
        if info.get("status") != "running":
            _multi_log.warning(
                f"[IDENTITY] {what} for {adb_id} ignored — worker status is "
                f"{info.get('status')!r}, not 'running'")
            return False
        return True

    def _note_recent_completion(self, adb_id, session_id, launch_token) -> None:
        """Remember the exact launch whose run_done was just accepted."""
        self._run_recent_completion[adb_id] = {
            "session_id": session_id, "launch_token": launch_token}

    def _recording_identity_matches(self, adb_id, session_id, launch_token) -> bool:
        """
        recording_done needs its own rule.

        It legitimately arrives AFTER run_done: the grace thread drains the
        worker queue once the process has exited, and that drain is often the
        only thing that ever sees the folder/report paths. By then the
        expectation has been consumed, so the ordinary gate would reject it and
        the recording metadata would be lost.

        Accept a match against either the currently expected launch OR the exact
        completion just accepted for that device — and nothing else, so attempt
        1's recording can never overwrite attempt 2's.
        """
        if session_id is None and launch_token is None:
            _multi_log.warning(
                f"[IDENTITY] identity-less recording_done for {adb_id} discarded")
            return False
        want = {"session_id": session_id, "launch_token": launch_token}
        expected = (getattr(self, "_run_expected_launch", None) or {}).get(adb_id)
        if expected is not None and expected == want:
            return True
        recent = (getattr(self, "_run_recent_completion", None) or {}).get(adb_id)
        if recent is not None and recent == want:
            return True
        killed = (getattr(self, "_run_recent_recording_identity", None)
                  or {}).get(adb_id)
        if killed is not None and killed == want:
            _multi_log.info(
                f"[IDENTITY] recording_done for {adb_id} accepted from the "
                f"emergency-killed launch {killed} — metadata only")
            return True
        _multi_log.warning(
            f"[IDENTITY] stale recording_done for {adb_id} "
            f"(session={session_id} token={launch_token}) matches neither the "
            f"expected launch {expected}, the recent completion {recent}, nor "
            f"the emergency-killed launch {killed} — ignored")
        return False

    def _on_run_done(self, adb_id, ok, result,
                     session_id=None, launch_token=None):
        # ── Identity gate: BEFORE any side effect, INCLUDING logging ─────────
        # The very first statement used to be `self._running_devs.pop(adb_id)`,
        # so a completion from a dead attempt removed the live worker for the
        # same device — orphaning its process beyond Stop One and Stop All, and
        # then closing its emulator, mangling its retries and pumping the queue.
        #
        # The caller used to write the ✓/✗ result line and the [RUN-DONE] file
        # record BEFORE calling in here, so a completion this method then
        # ignored still appeared to the user — and to LogAnalyzer — as a real
        # result. Both logs now live here, after acceptance.
        if not self._run_identity_matches(adb_id, session_id, launch_token,
                                          what="run_done"):
            return
        # Accepted: consume the expectation so a duplicate of THIS message is
        # rejected by the same gate on its second pass, and remember the exact
        # identity so its trailing recording_done is still recognised.
        self._run_expected_launch.pop(adb_id, None)
        self._note_recent_completion(adb_id, session_id, launch_token)

        # ── controller-owned terminal result ─────────────────────────────
        # Applied AFTER identity validation and BEFORE result logging, the
        # badge decision, retry logic, close logic and human finalization —
        # so every downstream decision sees the same value whether this
        # run_done came from the worker's own all_done (possibly already
        # bridged before the fatal handler ran) or from the controller's
        # synthetic one.
        _ov = self._take_terminal_override(adb_id, session_id, launch_token)
        if _ov is not None:
            _multi_log.info(
                f"[TERMINAL-OWN] normalising {adb_id} completion "
                f"{result!r} -> {_ov['result']!r} (controller-owned)")
            result = _ov["result"]
            ok = _ov["ok"]

        _tag = "ok" if ok else ("warn" if result == "stopped" else "err")
        self._run_log_msg(f"{'✓' if ok else '✗'} {adb_id} → {result}", _tag)
        # Reliable FILE log of the final run result (the UI line above is
        # screen-only). Stable format consumed by LogAnalyzer:
        #   [RUN-DONE] adb_id=<id> ok=<True|False> result=<text>
        _multi_log.info(f"[RUN-DONE] adb_id={adb_id} ok={ok} result={result}")

        info = self._running_devs.pop(adb_id, None)

        # Let a still-alive worker exit on its own before resorting to terminate.
        #
        # Deliberately OFF the Tk main thread: _on_run_done runs in the queue
        # handler, so joining here would freeze the whole UI for the grace
        # period. The rest of this method does not depend on the process being
        # gone — the worker sends all_done only after its own cleanup, so by now
        # recording is stopped and the files are written.
        if info:
            proc  = info.get("process")
            mp_q  = info.get("mp_q")
            grace = self.RUN_DONE_GRACE_SECONDS
            if proc and proc.is_alive():
                expecting_recording = (
                    bool(getattr(self, "_record_video", None) and self._record_video.get())
                    and adb_id not in (self._recording_paths or {})
                )
                _multi_log.info(
                    f"[DIAG] _on_run_done ── {adb_id} proc still alive — allowing up to "
                    f"{grace}s to exit cleanly "
                    f"(expecting_recording_done={expecting_recording})"
                )

                # Captured now, while `info` is still in hand: by the time this
                # thread runs, _running_devs no longer has the entry.
                def _grace_exit(p=proc, q=mp_q, a=adb_id, g=grace,
                                expect_rec=expecting_recording,
                                _gs=info.get("session_id"),
                                _gt=info.get("launch_token")):
                    t0 = time.time()
                    try:
                        p.join(timeout=g)
                    except Exception:
                        pass
                    waited = time.time() - t0
                    # Pick up anything sent during the wait — recording_done in
                    # particular, which carries the folder/report paths.
                    if q is not None:
                        try:
                            self._drain_worker_queue(
                                a, q, reason="run_done:grace",
                                session_id=_gs, launch_token=_gt)
                        except Exception:
                            pass
                    if p.is_alive():
                        _multi_log.warning(
                            f"[DIAG] grace ── {a} still alive after {waited:.1f}s "
                            f"(expecting_recording_done={expect_rec}) — terminating")
                        try: p.terminate(); p.join(timeout=5)
                        except Exception: pass
                        if p.is_alive():
                            _multi_log.error(f"[DIAG] grace ── {a} ignored terminate — killing")
                            try: p.kill()
                            except Exception: pass
                    else:
                        _multi_log.info(
                            f"[DIAG] grace ── {a} exited cleanly after {waited:.1f}s "
                            f"(no terminate needed)")

                threading.Thread(target=_grace_exit, daemon=True,
                                 name=f"grace_exit_{adb_id}").start()
            elif mp_q is not None:
                # Already exited — still drain, in case the last messages landed
                # between all_done and the process ending.
                try:
                    self._drain_worker_queue(
                        adb_id, mp_q, reason="run_done:post-exit",
                        session_id=info.get("session_id"),
                        launch_token=info.get("launch_token"))
                except Exception:
                    pass

        # Full state reset when device is done or failed.
        # The boundary marker goes FIRST: everything after it in this device's
        # raw log is controller-side cleanup, not worker evidence.
        self._human_mark_controller_cleanup(adb_id)
        try:
            if hasattr(self.bridge, "bot") and self.bridge.bot:
                self.bridge.bot.reset_device_finished_state(adb_id)
                _multi_log.info(f"[DIAG] _on_run_done ── reset_device_finished_state({adb_id}) ✓")
        except Exception as _rdf_e:
            _multi_log.warning(f"[DIAG] _on_run_done ── reset_device_finished_state failed: {_rdf_e}")

        # The human report's terminal result and badge. Declared BEFORE the
        # branch chain so every path has a definite value, and so no branch is
        # tempted to finalize the report itself — the close result does not
        # exist yet at this point.
        _human_result = result
        _human_badge = ""

        if ok:
            self._run_set_badge(adb_id, "DONE ✓", BADGE_DONE[0], BADGE_DONE[1])
            threading.Thread(target=_beep, daemon=True).start()
        elif result in ("stopped", "stopped_by_fatal_run",
                        "stopped_by_safe_reset", "stopped_by_controller_close"):
            # A collateral device stopped because ANOTHER device hit a fatal
            # error was not itself a failure. The generic FAILED badge
            # contradicted "STOPPED — RUN ABORTED BY FATAL ERROR" in its own
            # report. The triggering device keeps its FatalAPKError result.
            self._run_set_badge(adb_id, "STOPPED", BADGE_STOPPED[0], BADGE_STOPPED[1])
        elif result == "adb_connect_failed":
            # The human report's terminal result for THIS device. The two
            # branches below used to call _human_finalize_device directly, which
            # latched ctx.finalized/raw_end_offset/finished_at before the
            # emulator close ran — so the close result, the zombie warning and
            # the Overall qualifier could never reach the report. They now only
            # record what the result IS; the single finalization at the bottom
            # of _on_run_done does the finalizing, once the close is known.
            _MAX_ADB_RETRIES = 3
            # ── Is this session still entitled to retry at all? ──────────────
            # A late or duplicate adb_connect_failed can be processed after the
            # run was abandoned. Scheduling then resurrects a device the user
            # stopped, and overwrites the STOPPED badge with RETRY. Decide
            # BEFORE consuming a retry attempt or touching any state.
            _abandoned = None
            if not getattr(self, "_run_session_active", False):
                _abandoned = "session inactive"
            elif getattr(self, "_shutdown_pending", False):
                _abandoned = "shutdown pending"
            elif getattr(self, "_fatal_run_stop", False):
                _abandoned = "fatal run stop"
            elif getattr(self, "_internet_down_emergency", False):
                _abandoned = "internet emergency"
            elif adb_id in self._run_retry_after_ids:
                # A duplicate run_done for a device that is already waiting.
                # Two callbacks would requeue it twice and burn a second
                # attempt for one failure.
                _abandoned = "a retry is already pending for this device"
            if _abandoned is not None:
                _multi_log.warning(
                    f"[QUEUE] late/duplicate adb_connect_failed for {adb_id} "
                    f"discarded — {_abandoned} (session {self._run_session_id}); "
                    f"no retry scheduled, retry count unchanged")
                try:
                    self._run_log_msg(
                        f"⏭ {adb_id.split(':')[-1]}: late ADB failure ignored "
                        f"({_abandoned})", "warn")
                except Exception:
                    pass
                # Leave the badge exactly as it is: a manual stop must keep
                # STOPPED, and no device may show RETRY without a live callback.
                self._finish_run_session_if_idle()
                return

            retry_n = self._run_retry_counts.get(adb_id, 0) + 1
            self._run_retry_counts[adb_id] = retry_n
            if retry_n <= _MAX_ADB_RETRIES:
                _multi_log.warning(
                    f"[DIAG] _on_run_done ── {adb_id} adb_connect_failed "
                    f"(retry {retry_n}/{_MAX_ADB_RETRIES}) — re-queuing in 10s"
                )
                self._run_log_msg(
                    f"⟳ {adb_id.split(':')[-1]} ADB failed — retry {retry_n}/{_MAX_ADB_RETRIES}",
                    "warn"
                )
                # The RETRY badge is deliberately NOT set here — it is set below,
                # only after self.after() has actually returned a callback id.
                # Bind the callback to THIS session AND to a unique token, so a
                # callback can prove it is the one currently tracked. Session id
                # alone is not enough: two sessions can both have a retry
                # pending for the same adb_id.
                _sid = self._run_session_id
                self._run_retry_token_seq += 1
                _tok = self._run_retry_token_seq
                try:
                    _after_id = self.after(
                        10_000,
                        lambda a=adb_id, s=_sid, t=_tok: self._run_requeue(a, s, t))
                except Exception as _re:
                    # No callback exists, so the device is NOT retrying. Showing
                    # RETRY here would strand it forever: nothing would ever fire
                    # and nothing would ever complete it.
                    self._run_retry_after_ids.pop(adb_id, None)
                    _multi_log.error(
                        f"[QUEUE] retry_schedule_failed adb_id={adb_id} "
                        f"session={_sid} token={_tok}: {_re!r} — marking FAILED")
                    try:
                        self._run_log_msg(
                            f"✗ {adb_id.split(':')[-1]}: could not schedule the ADB "
                            f"retry ({type(_re).__name__}) — marked failed", "err")
                    except Exception:
                        pass
                    self._run_set_badge(adb_id, "FAILED ✗",
                                        BADGE_FAILED[0], BADGE_FAILED[1])
                    # Terminal, but do NOT finalize yet — see above.
                    _human_result = "retry_schedule_failed"
                    _human_badge = "FAILED ✗"
                else:
                    self._run_retry_after_ids[adb_id] = {
                        "session_id": _sid, "token": _tok, "after_id": _after_id}
                    # Badge only once a live, tracked callback really exists.
                    self._run_set_badge(
                        adb_id,
                        f"RETRY {retry_n}/{_MAX_ADB_RETRIES}",
                        BADGE_RETRY[0], BADGE_RETRY[1]
                    )
            else:
                _multi_log.error(
                    f"[DIAG] _on_run_done ── {adb_id} adb_connect_failed "
                    f"after {_MAX_ADB_RETRIES} retries — permanently failed"
                )
                self._run_log_msg(
                    f"✗ {adb_id.split(':')[-1]} ADB failed after {_MAX_ADB_RETRIES} retries",
                    "err"
                )
                # Retries exhausted: this device is done for good, and nothing
                # is scheduled for it. If it was the last one, end the session.
                self._run_set_badge(adb_id, "FAILED ✗", BADGE_FAILED[0], BADGE_FAILED[1])
                self._run_retry_after_ids.pop(adb_id, None)
                # Terminal, but do NOT finalize yet — see above.
                _human_result = "adb_connect_failed"
                _human_badge = "FAILED ✗"
        else:
            self._run_set_badge(adb_id, "FAILED ✗", BADGE_FAILED[0], BADGE_FAILED[1])

        # ── Close the emulator window for this adb_id BEFORE pumping the queue.
        # This enforces max_concurrent at the window level: a queued device only
        # starts after the completed/failed/stopped device's window has been
        # closed (or close attempt completed). Skip for demo and for the
        # "stopped" path because _run_stop_one already closed it.  Also skip for
        # L: never-launched results (cfg_build_failed / proc_start_failed) — there
        # is no emulator window to close for a device that never started.
        # WHETHER to close is decided by the launch's stored DISPOSITION, not
        # by matching the result string. A route that already resolved the
        # window — Stop One — or that deliberately leaves it open — Stop All,
        # Safe Reset, controller close, fatal abort — records that on the info
        # dict. Matching result strings meant every new route-specific result
        # ("stopped_by_fatal_run", "fatal: <reason>") silently fell through to
        # a real close, so the report said "NOT REQUESTED" while production
        # closed the emulator.
        _NO_CLOSE_DISPOSITIONS = ("not_requested_stop_all",
                                  "not_requested_safe_reset",
                                  "not_requested_controller_close",
                                  "not_applicable_never_launched")
        close_ok = None
        _close_disp = (info or {}).get("close_disposition", "") or ""
        _already_resolved = _close_disp in ("attempted_success",
                                            "attempted_failed",
                                            "attempted_unverified")
        if _already_resolved:
            close_ok = (info or {}).get("manual_close_ok")
            _multi_log.info(
                f"[CLOSE_EMU] run_done reusing close result adb_id={adb_id} "
                f"ok={close_ok} disp={_close_disp} (no second close attempted)")
        _explicit_no_close = _close_disp in _NO_CLOSE_DISPOSITIONS
        if _explicit_no_close:
            _multi_log.info(
                f"[CLOSE_EMU] run_done skipping close adb_id={adb_id} — "
                f"route policy {_close_disp}")
        if not _close_disp and result in ("cfg_build_failed",
                                          "proc_start_failed"):
            # Nothing was ever launched, so there is no window this run opened.
            _close_disp = "not_applicable_never_launched"
            _explicit_no_close = True
        # Legacy results with no disposition at all keep the old skip list.
        _legacy_skip = (not _close_disp
                        and result in ("stopped", "cfg_build_failed",
                                       "proc_start_failed"))
        if (not self.demo and not _already_resolved and not _explicit_no_close
                and not _legacy_skip):
            _multi_log.info(f"[CLOSE_EMU] run_done close start adb_id={adb_id}")
            try:
                bot = self.bridge.bot if hasattr(self.bridge, "bot") else None
                close_ok = self._close_emulator_for_device(adb_id, bot, timeout=15)
            except Exception as ex:
                # The attempt raised, so the window's state is unknown — not a
                # confirmed failure.
                close_ok = None
                _multi_log.warning(f"[CLOSE_EMU] run_done close error adb_id={adb_id}: {ex}")
            _multi_log.info(f"[CLOSE_EMU] run_done close result adb_id={adb_id} ok={close_ok}")
            # Preserve None. bool() here would record an unverified close as a
            # confirmed failure, and a later Stop One would then re-close a
            # window that may already be shut.
            self._run_last_close[adb_id] = close_ok
            _close_disp = self._close_disposition_for(close_ok)
            if close_ok is False:
                _multi_log.error(
                    f"[CLOSE_FAILED] emulator close failed for adb_id={adb_id} — "
                    f"zombie process may still be running; queue will still pump"
                )
                # Q: record the close failure THROUGH the controller cache instead
                # of calling bot.update_status()+flush_status() directly.  This
                # keeps the cache the single source of truth and lets the next
                # cache→sheet sync write it.
                _issue_val = (
                    "close_failed: emulator window did not close — zombie may be running"
                )
                try:
                    with self._status_cache_lock:
                        self._pending_sheet_status.setdefault(adb_id, {})["Issues"] = _issue_val
                        self._cache_dirty = True
                    # Note: there is no canonical "Issues" field in rows_by_device
                    # (it is not a tracked task column), so we only queue the
                    # pending sheet write — the next cache→sheet sync writes the
                    # "Issues" column.
                    self._persist_status_cache()
                    _multi_log.info(
                        f"[CLOSE_FAILED] {adb_id} Issues queued in controller cache "
                        f"(will sync to Sheets)"
                    )
                except Exception as _ci_e:
                    _multi_log.warning(
                        f"[CLOSE_FAILED] could not cache Issues for {adb_id}: {_ci_e}"
                    )

        _multi_log.info(
            f"[QUEUE] closing_adb_id={adb_id} close_result={close_ok} "
            f"queue_pump_after_close=True"
        )
        _multi_log.info("[QUEUE] close complete, pumping next queued device")

        self._run_process_queue()

        # ── Human-readable report ────────────────────────────────────────────
        # Only when the device is TRULY terminal. An adb_connect_failed with a
        # retry still scheduled is mid-lifecycle: the report must span both
        # attempts, so it is deliberately not generated here.
        if adb_id not in (getattr(self, "_run_retry_after_ids", None) or {}):
            self._human_finalize_device(
                adb_id, result=_human_result, ok=bool(ok), close_ok=close_ok,
                session_id=session_id, close_disposition=_close_disp,
                prior_close_result=(info or {}).get("prior_close_result",
                                                    "no_attempt"),
                badge=(_human_badge
                       or (self._run_display(adb_id) or {}).get("status", "")))

        # One authoritative completion check, which also owns the end-of-run
        # sheet sync. Deliberately AFTER the pump, and deliberately not the old
        # `not _running_devs and not _run_queue` test: that ignored pending ADB
        # retries, so a device waiting its ten seconds triggered a "final" sync
        # in the middle of its own run — once per attempt.
        self._finish_run_session_if_idle()

    def _run_requeue(self, adb_id: str, session_id: int = None, token: int = None):
        """
        Re-append adb_id to the end of the run queue after an adb_connect_failed retry.
        Called via self.after() so it runs on the UI thread with a delay.

        `session_id` and `token` identify the exact callback that was scheduled.
        A callback that is not the currently tracked one must be a TOTAL no-op:
        it may not pop tracking, touch the queue, or decide whether the current
        session is finished. Deciding completion on behalf of a newer session is
        just as damaging as requeueing into it — an old callback could re-enable
        RUN SELECTED and fire the deferred panel rebuild mid-run.
        """
        _entry = (getattr(self, "_run_retry_after_ids", None) or {}).get(adb_id)
        _mine = (_entry is not None
                 and _entry.get("session_id") == session_id
                 and _entry.get("token") == token)
        if not _mine:
            # Either it was cancelled (after_cancel can fail and let an orphan
            # fire anyway), or a NEWER session has since scheduled its own retry
            # for this same device. Popping here would destroy that live entry.
            _multi_log.info(
                f"[QUEUE] stale ADB retry callback for {adb_id} "
                f"(session={session_id} token={token}) is not the tracked entry "
                f"{_entry!r} — ignored entirely")
            return

        _cur = getattr(self, "_run_session_id", 0)
        if session_id is not None and session_id != _cur:
            # Tracked, but the session moved on without cancelling it. Remove
            # only this entry; still do not judge the newer session.
            self._run_retry_after_ids.pop(adb_id, None)
            _multi_log.info(
                f"[QUEUE] stale ADB retry for {adb_id} from session {session_id} "
                f"(current {_cur}) — dropped, current session untouched")
            return

        # From here on the callback owns the entry and the current session.
        self._run_retry_after_ids.pop(adb_id, None)

        if not getattr(self, "_run_session_active", False):
            _multi_log.info(
                f"[QUEUE] ADB retry for {adb_id} arrived after the session ended "
                f"— ignored")
            self._finish_run_session_if_idle()
            return
        if getattr(self, "_internet_down_emergency", False):
            _multi_log.info(
                f"[QUEUE] ADB retry for {adb_id} suppressed — internet emergency "
                f"in progress; the restore path owns the restart")
            return
        if getattr(self, "_shutdown_pending", False):
            _multi_log.info(f"[QUEUE] shutdown pending — requeue blocked for {adb_id}")
            self._finish_run_session_if_idle()
            return
        # Don't re-queue if the device is already running again or stop was hit
        if adb_id in self._running_devs:
            self._finish_run_session_if_idle()
            return
        if adb_id in self._run_queue:
            _multi_log.info(f"[QUEUE] {adb_id} already queued — retry not duplicated")
            self._finish_run_session_if_idle()
            return
        if not self._run_rows.get(adb_id):
            self._finish_run_session_if_idle()
            return
        _multi_log.info(f"[DIAG] _run_requeue ── re-queuing {adb_id}")
        self._run_queue.append(adb_id)
        self._run_process_queue()
        # A requeue that launched nothing (queue capped, or the device skipped)
        # can still leave the session with no work at all.
        self._finish_run_session_if_idle()

    def _run_log_msg(self, msg, tag="dim"):
        self._run_log.configure(state=tk.NORMAL)
        self._run_log.insert(tk.END, f"[{_ts()}]  {msg}\n", tag)
        self._run_log.see(tk.END)
        self._run_log.configure(state=tk.DISABLED)

    # ══════════════════════════════════════════════════════════════════════════
    # TAB: TEST
    # ══════════════════════════════════════════════════════════════════════════
    def _build_test_tab(self):
        tab = self._tab_test
        tab.rowconfigure(1, weight=1)
        tab.columnconfigure(0, weight=1)

        # Mode toggle
        hdr = tk.Frame(tab, bg=BG_MID)
        hdr.grid(row=0, column=0, sticky="ew")
        tk.Label(hdr, text="TEST MODE:", font=FH, bg=BG_MID, fg=PRI, padx=8, pady=6).pack(side=tk.LEFT)
        for mode, lbl in (("single", "Single"), ("multi", "Multi")):
            tk.Radiobutton(hdr, text=lbl, variable=self._test_mode, value=mode,
                           font=FNB, bg=BG_MID, fg=FG_MAIN,
                           selectcolor=PRI, activebackground=BG_MID,
                           indicatoron=False, padx=10, pady=4,
                           relief=tk.FLAT, cursor="hand2",
                           command=self._on_test_mode_change).pack(side=tk.LEFT, padx=2)

        self._test_body = tk.Frame(tab, bg=BG_BASE)
        self._test_body.grid(row=1, column=0, sticky="nsew")
        self._test_body.rowconfigure(0, weight=1)
        self._test_body.columnconfigure(0, weight=1)

        self._test_single_frame = tk.Frame(self._test_body, bg=BG_BASE)
        self._test_multi_frame  = tk.Frame(self._test_body, bg=BG_BASE)

        self._build_test_single()
        self._build_test_multi()

        self._test_single_frame.grid(row=0, column=0, sticky="nsew")

    def _on_test_mode_change(self):
        self._test_single_frame.grid_remove()
        self._test_multi_frame.grid_remove()
        if self._test_mode.get() == "single":
            self._test_single_frame.grid(row=0, column=0, sticky="nsew")
        else:
            self._test_multi_frame.grid(row=0, column=0, sticky="nsew")

    def _build_test_single(self):
        f = self._test_single_frame
        f.rowconfigure(0, weight=1)
        f.columnconfigure(0, weight=0)
        f.columnconfigure(1, weight=0)
        f.columnconfigure(2, weight=1)

        # ── Device picker ─────────────────────────────────────────────────
        col1 = tk.Frame(f, bg=BG_PANEL, width=220)
        col1.grid(row=0, column=0, sticky="nsew", padx=6, pady=6)
        col1.pack_propagate(False)
        col1.rowconfigure(1, weight=1)
        col1.columnconfigure(0, weight=1)

        dev_hdr = tk.Frame(col1, bg=BG_PANEL)
        dev_hdr.grid(row=0, column=0, sticky="ew")
        _sec_label(dev_hdr, "DEVICE")
        self._test_full_scan_btn = _btn(
            dev_hdr, "⟳⟳ Full", lambda: self._test_scan_devices(deep=True),
            bg=BG_CELL, fg=FG_DIM, font=FS)
        self._test_full_scan_btn.pack(side=tk.RIGHT, padx=2, pady=4)
        self._test_scan_btn = _btn(dev_hdr, "⟳ Scan", self._test_scan_devices,
                                   bg=BG_CELL, fg=ACC_BLUE, font=FS, padx=6, pady=2)
        self._test_scan_btn.pack(side=tk.RIGHT, padx=4, pady=4)

        lb_wrap = tk.Frame(col1, bg=BG_PANEL)
        lb_wrap.grid(row=1, column=0, sticky="nsew")
        self._single_lb = tk.Listbox(lb_wrap, font=FMN, bg=BG_CELL, fg=FG_MAIN,
                                      selectbackground=PRI, selectforeground="white",
                                      bd=0, highlightthickness=0, activestyle="none",
                                      relief=tk.FLAT)
        self._single_lb.pack(fill=tk.BOTH, expand=True, padx=6, pady=4)
        self._single_lb.bind("<<ListboxSelect>>", self._on_single_sel)

        # ── Task picker ───────────────────────────────────────────────────
        col2 = tk.Frame(f, bg=BG_PANEL, width=260)
        col2.grid(row=0, column=1, sticky="nsew", padx=3, pady=6)
        col2.pack_propagate(False)
        self._task_sel = TaskSelector(col2, task_sets_mgr=self._task_sets)
        self._task_sel.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)
        tk.Checkbutton(col2, text="Skip prepare_target_app", variable=self.skip_var,
                       font=FS, bg=BG_PANEL, fg=FG_DIM, selectcolor=BG_CELL,
                       activebackground=BG_PANEL).pack(fill=tk.X, padx=6)
        self._test_run_btn = _btn(col2, "▶  RUN  [Ctrl+R]", self._single_run, bg=PRI, fg="white", font=FH)
        self._test_run_btn.pack(fill=tk.X, padx=8, pady=(4, 2))
        self._test_stop_btn = _btn(col2, "■  STOP", self._single_stop_fn, bg=CLR_FAIL, fg=FG_ERR, font=FNB, state=tk.DISABLED)
        self._test_stop_btn.pack(fill=tk.X, padx=8, pady=2)

        # ── Log ───────────────────────────────────────────────────────────
        col3 = tk.Frame(f, bg=BG_BASE)
        col3.grid(row=0, column=2, sticky="nsew", padx=(3, 6), pady=6)
        col3.rowconfigure(0, weight=1)
        col3.columnconfigure(0, weight=1)
        self._test_log = scrolledtext.ScrolledText(col3, font=(FM, 8),
                                                     bg="#0A0A14", fg=FG_MAIN,
                                                     state=tk.DISABLED, wrap=tk.WORD,
                                                     relief=tk.FLAT, padx=10, pady=6)
        self._test_log.grid(row=0, column=0, sticky="nsew")
        for tag, fg in [("ok", "#5CCC5C"), ("warn", "#F9A825"), ("err", FG_ERR), ("dim", FG_DIM), ("info", ACC_BLUE)]:
            self._test_log.tag_config(tag, foreground=fg)

        # Auto-populate: use existing active_devices or scan
        self.after(200, self._test_auto_populate)

    def _test_auto_populate(self):
        """On tab build: always scan so both single and multi show all online devices."""
        self._test_scan_devices()

    def _scan_online_bluestacks_devices(self, log_fn=None, deep: bool = False) -> list:
        """
        Shared device-scan core used by BOTH the Test tab and the Screenshotor.

        Two modes:

          FAST (deep=False, the default)
            Read the conf for the port/name map, then run ONE netstat sweep and
            ONE `adb devices` call and keep only ports that are actually
            LISTENING or already known to ADB.  Only those get `adb connect` and
            `get-state`.  With ~190 configured instances and two windows open
            this touches two ports instead of 190.

          FULL (deep=True, opt-in)
            Probe every configured instance.  Slow by nature — kept for the case
            where an emulator is running but neither netstat nor ADB reports it.

        Runs SYNCHRONOUSLY in the caller's (background) thread.  `log_fn(msg,
        tag)` is an optional sink for progress lines.

        Does NOT launch/close emulators and does NOT touch _running_devs, the run
        queue, or cache/sheet sync.

        Returns dicts compatible with both callers:
            {"adb_id", "name", "friendly", "device_type", "statuses"}
        """
        def _log(msg, tag="dim"):
            if log_fn:
                try:
                    log_fn(msg, tag)
                except Exception:
                    pass

        if self.demo:
            return [{"adb_id": d["adb_id"], "name": d["name"],
                     "friendly": d["name"],
                     "device_type": d.get("device_type", ""),
                     "statuses": d.get("statuses", {})}
                    for d in DEMO_ACTIVE]

        bot = self.bridge.load_bot()

        # Fail clearly rather than scanning nothing when the conf is missing.
        status = bot.bluestacks_conf_status()
        if not status["found"]:
            _log("BlueStacks config not found. Checked:", "err")
            for path, _ in status["candidates"]:
                _log(f"  {path}", "err")
            return []

        raw = self.bridge.get_conf_devices_raw()
        raw = [d for d in raw if str(d.get("port", "")) != "5555"]
        conf_count = len(raw)
        if not raw:
            _log("No instances found in BlueStacks conf.", "warn")
            return []

        all_ids = [f"localhost:{d['port']}" for d in raw]
        conf_name_by_id = {f"localhost:{d['port']}": (d.get("name") or d.get("display_name") or "")
                           for d in raw}

        # ── Decide which ports are worth touching ────────────────────────────
        # FAST (default): a BlueStacks instance only holds its ADB port open
        # while its window is running, so one netstat sweep plus one
        # `adb devices` call narrows ~190 configured instances down to the two
        # or three that actually exist right now.  Blindly `adb connect`ing every
        # configured port is what made scans take minutes.
        #
        # FULL (opt-in): check every configured instance, for the case where an
        # emulator is up but neither netstat nor ADB reports it.
        listening = set()
        adb_listed = set()
        if deep:
            candidate_ids = list(all_ids)
            _log(f"FULL scan: checking all {conf_count} configured instance(s) — "
                 f"this is the slow path", "warn")
        else:
            try:
                listening = bot.list_listening_ports()
            except Exception as exc:
                _log(f"netstat sweep failed ({exc}) — falling back to adb devices only", "warn")
            try:
                adb_listed = bot.list_adb_listed_ids()
            except Exception as exc:
                _log(f"adb devices failed ({exc})", "warn")

            candidate_ids = []
            for d, adb_id in zip(raw, all_ids):
                port = str(d.get("port", ""))
                if port in listening or adb_id in adb_listed:
                    candidate_ids.append(adb_id)

            # Nothing detected: say so plainly instead of silently deep-scanning
            # ~190 ports and appearing to hang.
            if not candidate_ids:
                _log(f"Scan: conf_count={conf_count} listening_ports={len(listening)} "
                     f"adb_listed={len(adb_listed)} checked=0 online=0", "warn")
                _log("No open emulator windows detected. Start an instance, or use "
                     "Full scan to probe every configured port.", "warn")
                return []

        checked_count = len(candidate_ids)
        _log(f"Scan: conf_count={conf_count} listening_ports={len(listening)} "
             f"adb_listed={len(adb_listed)} checked={checked_count}", "dim")
        _log(f"Connecting {checked_count} candidate instance(s)…", "dim")

        # Bounded pool: one thread per configured instance spawned ~190 threads
        # and swamped the adb server. 20 is plenty for this workload.
        _MAX_SCAN_WORKERS = 20
        workers = max(1, min(_MAX_SCAN_WORKERS, checked_count))
        with ThreadPoolExecutor(max_workers=workers) as pool:
            futs = [pool.submit(_adb_connect_quiet, a) for a in candidate_ids]
            for f in as_completed(futs):
                pass

        # get-state in parallel too — serial checks meant checked_count x timeout
        # in the worst case, which on a full scan was minutes of pure waiting.
        def _get_state(adb_id):
            try:
                chk = subprocess.run(["adb", "-s", adb_id, "get-state"],
                                     capture_output=True, text=True, timeout=4)
                return adb_id, (chk.stdout or "").strip()
            except Exception:
                return adb_id, ""

        online_ids = []
        with ThreadPoolExecutor(max_workers=workers) as pool:
            for adb_id, state in pool.map(_get_state, candidate_ids):
                if state == "device":
                    online_ids.append(adb_id)
        online_ids.sort(key=lambda a: int(a.rsplit(":", 1)[-1]) if a.rsplit(":", 1)[-1].isdigit() else 0)

        _multi_log.info(
            f"[SCAN] mode={'full' if deep else 'fast'} conf_count={conf_count} "
            f"listening_ports_count={len(listening)} adb_listed_count={len(adb_listed)} "
            f"checked_count={checked_count} online_count={len(online_ids)}"
        )
        _log(f"Scan: {len(online_ids)}/{checked_count} checked device(s) online "
             f"({conf_count} configured)", "ok" if online_ids else "warn")
        if not online_ids:
            return []

        devs = []
        for adb_id in online_ids:
            row = self.bridge._lookup_row(adb_id) or {}
            friendly = (row.get("friendly") or row.get("name")
                        or row.get("device_name") or conf_name_by_id.get(adb_id)
                        or adb_id)
            devs.append({
                "adb_id":      adb_id,
                "name":        friendly,
                "friendly":    friendly,
                "device_type": row.get("device_type", ""),
                "statuses":    self.bridge.status_snapshot(adb_id),
            })
        return devs

    def _test_scan_devices(self, deep: bool = False):
        """
        Discover currently-open devices and publish them to every panel.

        deep=False (⟳ Scan)      only ports that are LISTENING or already in
                                 `adb devices` — fast, the normal case
        deep=True  (⟳⟳ Full)     every configured instance — slow, opt-in
        """
        try:
            self._test_scan_btn.configure(state=tk.DISABLED, text="…")
            self._test_full_scan_btn.configure(state=tk.DISABLED)
        except Exception:
            pass

        def _worker():
            try:
                devs = self._scan_online_bluestacks_devices(
                    log_fn=lambda msg, tag="dim": self.q.put(("log", msg, tag)),
                    deep=deep)
                self.q.put(("test_scan_done", devs))
            except Exception as exc:
                self.q.put(("test_scan_done", []))
                self.q.put(("log", f"Test scan error: {exc}", "err"))

        threading.Thread(target=_worker, daemon=True).start()

    def _build_test_multi(self):
        f = self._test_multi_frame
        f.rowconfigure(0, weight=0)   # header — fixed height
        f.rowconfigure(1, weight=1)   # device list — fills rest
        f.columnconfigure(0, weight=1)

        hdr = tk.Frame(f, bg=BG_MID)
        hdr.grid(row=0, column=0, sticky="ew")
        tk.Label(hdr, text="MULTI-DEVICE TEST", font=FH, bg=BG_MID, fg=PRI, padx=8, pady=6).pack(side=tk.LEFT)
        _btn(hdr, "▶ START ALL", self._multi_start_all, bg=PRI, fg="white", font=FNB).pack(side=tk.LEFT, padx=4)
        _btn(hdr, "■ STOP ALL", self._multi_stop_all, bg=CLR_FAIL, fg=FG_ERR, font=FNB).pack(side=tk.LEFT, padx=4)
        # Global task selector — applies chosen tasks to ALL devices at once
        _btn(hdr, "☰ Set All Tasks", self._multi_set_all_tasks, bg=BG_CELL, fg=ACC_BLUE, font=FNB).pack(side=tk.LEFT, padx=6)
        tk.Checkbutton(hdr, text="Skip prepare_target_app", variable=self.skip_var,
                       font=FS, bg=BG_MID, fg=FG_DIM, selectcolor=BG_CELL,
                       activebackground=BG_MID).pack(side=tk.RIGHT, padx=8)

        # Wrap: fills remaining space below header only
        self._multi_wrap = tk.Frame(f, bg=BG_PANEL)
        self._multi_wrap.grid(row=1, column=0, sticky="nsew", padx=6, pady=(0, 6))
        self._multi_wrap.rowconfigure(0, weight=1)
        self._multi_wrap.columnconfigure(0, weight=1)

    def _multi_active_workers(self) -> list:
        """adb_ids whose Multi-Test worker thread is still alive."""
        out = []
        for adb_id, row in (self._multi_rows or {}).items():
            t = row.get("thread")
            try:
                if t is not None and t.is_alive():
                    out.append(adb_id)
            except Exception:
                pass
        return out

    def _render_test_multi_panel(self):
        # A rebuild destroys the widgets AND the dict holding each row's
        # `thread` and `stop_event` — the only handles Stop One / Stop All have.
        # A scan during an active Multi-Test therefore left a worker running
        # that nothing could signal. Defer the visual refresh instead; the scan
        # data itself is already updated, and the panel is rebuilt as soon as
        # the workers finish.
        active = self._multi_active_workers()
        if active:
            self._multi_panel_refresh_pending = True
            _multi_log.info(
                f"[MULTI-TEST] panel refresh deferred — {len(active)} worker(s) "
                f"still running: {active}")
            self._log(f"Multi-Test panel refresh deferred — {len(active)} "
                      f"worker(s) still running", "warn")
            return

        self._multi_panel_refresh_pending = False
        for w in self._multi_wrap.winfo_children():
            w.destroy()
        self._multi_rows.clear()

        self._multi_wrap.rowconfigure(0, weight=1)
        self._multi_wrap.columnconfigure(0, weight=1)

        # Prefer scan results (_test_devices) → fall back to active_devices → conf_devices
        _td = getattr(self, "_test_devices", None)
        devs = list(_td if _td is not None else (self.active_devices or self.conf_devices))
        if not devs:
            tk.Label(self._multi_wrap, text="No devices online. Press ⟳ Scan.", font=FN,
                     bg=BG_PANEL, fg=FG_DIM, pady=16).grid(row=0, column=0)
            return

        canvas = tk.Canvas(self._multi_wrap, bg=BG_PANEL, bd=0, highlightthickness=0)
        sb = tk.Scrollbar(self._multi_wrap, orient=tk.VERTICAL, command=canvas.yview, bg=BG_MID, troughcolor=BG_MID)
        canvas.configure(yscrollcommand=sb.set)
        sb.grid(row=0, column=1, sticky="ns")
        canvas.grid(row=0, column=0, sticky="nsew")
        inner = tk.Frame(canvas, bg=BG_PANEL)
        win_id = canvas.create_window((0, 0), window=inner, anchor=tk.NW)
        inner.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.bind("<Configure>", lambda e: canvas.itemconfig(win_id, width=e.width))

        groups = _group_devices_by_type(devs)
        row_idx = 0
        for group_name, gdevs in groups:
            tk.Label(inner, text=f"▼ {group_name} ({len(gdevs)})", font=FNB,
                     bg="#1A1A30", fg=ACC_BLUE, anchor=tk.W, padx=8, pady=4
                     ).grid(row=row_idx, column=0, columnspan=7, sticky="ew")
            row_idx += 1
            for dev in gdevs:
                adb_id = dev["adb_id"]
                bg_row = BG_MID if row_idx % 2 == 0 else BG_PANEL
                # Presence, not truthiness: [] is a legitimate stored choice.
                # Only a genuinely new device — one with no entry at all — gets
                # the default "everything" selection.
                if adb_id in self._multi_task_selections:
                    selected_tasks = list(self._multi_task_selections[adb_id])
                else:
                    selected_tasks = self._task_sets.all_keys() + list(SUBTASK_ORDER)
                    self._multi_task_selections[adb_id] = list(selected_tasks)

                tk.Label(inner, text=f"{dev['name']} / {adb_id}", font=(F, 8),
                         bg=bg_row, fg=FG_MAIN, anchor=tk.W, width=36
                         ).grid(row=row_idx, column=0, padx=6, pady=3, sticky=tk.W)

                task_count_var = tk.StringVar(value=_tasks_short_label(selected_tasks))
                tasks_ref = {"keys": selected_tasks}

                def _make_picker(a=adb_id, tv=task_count_var, tr=tasks_ref):
                    def _open():
                        btn = self._multi_rows[a]["tasks_btn"]
                        def _confirm(sel):
                            # One path for every selection change: model,
                            # widget, marker and badge together.
                            self._set_multi_selection(a, sel, user_edit=True)
                        TaskPopover(self, btn, tr["keys"], _confirm)
                    return _open

                tasks_btn = tk.Button(inner, bg=BG_CELL, fg="#5CCC5C",
                                      font=(F, 8), relief=tk.FLAT, padx=8, pady=4,
                                      cursor="hand2", bd=0, command=_make_picker())
                tasks_btn.configure(textvariable=task_count_var)
                tasks_btn.grid(row=row_idx, column=1, padx=4, pady=3)

                start_btn = tk.Button(inner, text="▶ START", bg=ACC_BLUE, fg="white",
                                      font=FSB, relief=tk.FLAT, padx=8, pady=3, cursor="hand2", bd=0,
                                      command=lambda a=adb_id: self._multi_start_one(a))
                start_btn.grid(row=row_idx, column=2, padx=4, pady=3)

                stop_btn = tk.Button(inner, text="■ STOP", bg=BG_CELL, fg=FG_DIM,
                                     font=FSB, relief=tk.FLAT, padx=6, pady=3, cursor="hand2", bd=0,
                                     state=tk.DISABLED,
                                     command=lambda a=adb_id: self._multi_stop_one(a))
                stop_btn.grid(row=row_idx, column=3, padx=4, pady=3)

                # Seeded from the canonical display model so a rebuild — the
                # deferred one after a run especially — does not wipe DONE ✓,
                # FAILED ✗, STOPPED or the last log line back to IDLE / "—".
                # A genuinely new device gets the IDLE default.
                _disp = self._multi_display(adb_id)
                _badge = _disp.get("badge") or BADGE_IDLE
                status_var = tk.StringVar(value=_disp.get("status", "IDLE"))
                status_lbl = tk.Label(inner, textvariable=status_var, font=FSB,
                                      bg=_badge[0], fg=_badge[1], width=12)
                status_lbl.grid(row=row_idx, column=4, padx=4, pady=3)

                log_var = tk.StringVar(value=_disp.get("log", "—"))
                tk.Label(inner, textvariable=log_var, font=(FM, 7), bg=bg_row,
                         fg=FG_DIM, anchor=tk.W).grid(row=row_idx, column=5, padx=4, pady=3, sticky="ew")
                inner.columnconfigure(5, weight=1)

                self._multi_rows[adb_id] = {
                    "tasks_ref": tasks_ref, "task_count": task_count_var, "tasks_btn": tasks_btn,
                    "status_var": status_var, "status_lbl": status_lbl, "log_var": log_var,
                    "start_btn": start_btn, "stop_btn": stop_btn,
                    "stop_event": None, "thread": None,
                }
                # Final reconciliation, now that the row exists. A device that
                # was offline when the state loaded had its selection restored
                # but no widget to reconcile against; this is the moment its
                # badge catches up. Terminal and runtime states are filtered out
                # by _SELECTION_BADGES, so DONE ✓ / FAILED ✗ / STOPPED survive.
                self._sync_multi_selection_badge(adb_id)
                row_idx += 1

    # ── test multi start/stop (threading, not multiprocessing) ─────────────
    def _multi_start_one(self, adb_id):
        row = self._multi_rows.get(adb_id)
        if not row or (row.get("thread") and row["thread"].is_alive()):
            return

        task_keys = row["tasks_ref"]["keys"]

        def _log_fn(msg, tag="dim"):
            self.q.put(("multi_log", adb_id, msg[:60]))
            self.q.put(("log", f"[{adb_id.split(':')[-1]}] {msg}", tag))

        # ── Nothing runnable? Decide BEFORE going RUNNING or starting a thread.
        # Test mode exists to test tasks; it has no setup-only interpretation,
        # so an empty or all-invalid selection must never run preparation and
        # report success. That rule belongs to the Run tab alone.
        _task_keys_expanded = self._task_sets.expand_keys(task_keys)
        _invalid = self._invalid_multi_tasks.get(adb_id) or []

        def _no_runnable(why: str, detail=""):
            _log_fn(f"no runnable tasks — {why}", "err")
            _multi_log.error(f"[MULTI-TEST] {adb_id} no runnable tasks: {why}"
                             + (f" {detail}" if detail else ""))
            self._multi_set_badge(adb_id, "INVALID TASKS" if _invalid else "NO TASKS",
                                  BADGE_IDLE[0], BADGE_IDLE[1])
            self.q.put(("multi_done", adb_id, False, "no_runnable_tasks"))

        if _invalid and not _task_keys_expanded:
            _no_runnable("the stored selection is invalid or missing",
                         f"discarded={_invalid}")
            return
        if not _task_keys_expanded:
            # Covers both an explicitly empty selection and one that expanded
            # away. Either way there is nothing to test.
            _no_runnable("the selection is empty" if not task_keys
                         else "every configured task is invalid or the "
                              "referenced task set is missing",
                         f"raw={task_keys}")
            return

        stop_ev = threading.Event()
        row["stop_event"] = stop_ev
        row["start_btn"].configure(state=tk.DISABLED)
        row["stop_btn"].configure(state=tk.NORMAL)
        self._multi_set_badge(adb_id, "RUNNING", BADGE_RUNNING[0], BADGE_RUNNING[1])

        def worker():
            if self.demo:
                for tk_key in _task_keys_expanded:
                    if stop_ev.is_set():
                        break
                    time.sleep(0.8)
                    lbl = TASK_DEFS[tk_key]["label"] if tk_key in TASK_DEFS else tk_key
                    _log_fn(f"✓ {lbl}", "ok")
                ok = not stop_ev.is_set()
                result = "done" if ok else "stopped"
            else:
                ok, result = self.bridge.run_tasks(
                    adb_id, _task_keys_expanded,
                    self.skip_var.get(), stop_ev, _log_fn)
            self.q.put(("multi_done", adb_id, ok, result))

        t = threading.Thread(target=worker, daemon=False, name=f"multi_worker_{adb_id}")
        row["thread"] = t
        t.start()

    def _multi_stop_one(self, adb_id):
        row = self._multi_rows.get(adb_id)
        # Don't overwrite terminal states — task may have already finished
        if row:
            current = row.get("status_var")
            cur_val = current.get() if current else "unknown"
            if cur_val in ("DONE ✓", "STOPPED", "FAILED ✗"):
                _multi_log.info(
                    f"[DIAG] _multi_stop_one ── {adb_id} already in terminal state "
                    f"'{cur_val}' — skip"
                )
                return
        _multi_log.info(f"[DIAG] _multi_stop_one ── {adb_id} STOP signal sent")
        if row and row.get("stop_event"):
            row["stop_event"].set()
        self._multi_set_badge(adb_id, "STOPPING…", BADGE_STOPPING[0], BADGE_STOPPING[1])
        # Per-device flush — non-daemon, waits for task thread to finish cleanly
        def _flush(aid=adb_id):
            try:
                _multi_log.info(f"[DIAG] _multi_stop_one ── {aid} flush thread started")
                t = self._multi_rows.get(aid, {}).get("thread")
                if t and t.is_alive():
                    _multi_log.info(f"[DIAG] _multi_stop_one ── {aid} joining task thread (timeout=30s)")
                    t.join(timeout=30)
                    if t.is_alive():
                        _multi_log.warning(f"[DIAG] _multi_stop_one ── {aid} task thread still alive after 30s join")
                    else:
                        _multi_log.info(f"[DIAG] _multi_stop_one ── {aid} task thread finished cleanly")
                bot = self.bridge.load_bot()
                pending = getattr(bot, "_PENDING_STATUS", {})
                pending_fields = list(pending.get(aid, {}).keys())
                _multi_log.info(
                    f"[DIAG] _multi_stop_one ── {aid} calling flush_status "
                    f"(pending fields: {pending_fields})"
                )
                bot.flush_status(aid)
                _multi_log.info(f"[DIAG] _multi_stop_one ── {aid} flush_status done ✓")
                self.q.put(("log", f"[{aid.split(':')[-1]}] ✓ Flushed to sheet", "ok"))
            except Exception as _fex:
                _multi_log.error(f"[DIAG] _multi_stop_one ── {aid} flush FAILED: {_fex}")
        threading.Thread(target=_flush, daemon=False).start()

    def _multi_start_all(self):
        # NO TASKS / INVALID TASKS included defensively: _set_multi_selection
        # already resets a corrected row to IDLE, but a row that never went
        # through it must not stay permanently unstartable. _multi_start_one
        # re-checks the selection and simply reports no_runnable_tasks again if
        # it is still empty.
        idle = [a for a, r in self._multi_rows.items()
                if r["status_var"].get() in ("IDLE", "FAILED ✗", "STOPPED",
                                             "NO TASKS", "INVALID TASKS")]
        for a in idle:
            self._multi_start_one(a)

    def _multi_stop_all(self):
        devices = list(self._multi_rows)
        _multi_log.info(f"[DIAG] _multi_stop_all ── stopping {len(devices)} device(s): {devices}")
        for a in devices:
            self._multi_stop_one(a)
        # Flush all devices — non-daemon thread waits for all task threads then writes sheet
        def _flush_all():
            try:
                _multi_log.info("[DIAG] _multi_stop_all ── flush_all thread started")
                bot = self.bridge.load_bot()
                for aid, row in self._multi_rows.items():
                    t = row.get("thread")
                    if t and t.is_alive():
                        _multi_log.info(f"[DIAG] _multi_stop_all ── joining {aid} (timeout=30s)")
                        t.join(timeout=30)
                        if t.is_alive():
                            _multi_log.warning(f"[DIAG] _multi_stop_all ── {aid} still alive after 30s")
                        else:
                            _multi_log.info(f"[DIAG] _multi_stop_all ── {aid} thread done")
                pending = getattr(bot, "_PENDING_STATUS", {})
                pending_devs = list(pending.keys())
                _multi_log.info(f"[DIAG] _multi_stop_all ── flushing {len(pending_devs)} device(s): {pending_devs}")
                for dev_id in pending_devs:
                    try:
                        bot.flush_status(dev_id)
                        _multi_log.info(f"[DIAG] _multi_stop_all ── {dev_id} flushed ✓")
                    except Exception as _fe:
                        _multi_log.error(f"[DIAG] _multi_stop_all ── {dev_id} flush FAILED: {_fe}")
                self.q.put(("log", "✓ Flushed all statuses to sheet", "ok"))
                _multi_log.info("[DIAG] _multi_stop_all ── flush_all complete ✓")
            except Exception as ex:
                _multi_log.error(f"[DIAG] _multi_stop_all ── flush_all FAILED: {ex}")
                self.q.put(("log", f"Flush-on-stop error: {ex}", "warn"))
        threading.Thread(target=_flush_all, daemon=False).start()

    def _multi_set_all_tasks(self):
        """Open task picker; apply the selection to every device row at once."""
        # Use first device row button as anchor, or fall back to header
        anchor = None
        for row in self._multi_rows.values():
            try:
                if row.get("tasks_btn") and row["tasks_btn"].winfo_exists():
                    anchor = row["tasks_btn"]
                    break
            except Exception:
                pass
        if anchor is None:
            return

        # Seed popover with whatever the first device currently has
        first_keys = self._task_sets.all_keys() + list(SUBTASK_ORDER)
        for row in self._multi_rows.values():
            if row.get("tasks_ref"):
                first_keys = list(row["tasks_ref"]["keys"])
                break

        def _apply_all(sel):
            label = _tasks_short_label(sel)
            for _aid, row in list(self._multi_rows.items()):
                if row.get("tasks_ref"):
                    self._set_multi_selection(_aid, sel, user_edit=True)

        TaskPopover(self, anchor, first_keys, _apply_all)

    def _multi_set_badge(self, adb_id, text, bg, fg):
        # Record FIRST and unconditionally: a deferred rebuild recreates the
        # row, and without this the terminal DONE/FAILED/STOPPED it is showing
        # would be reset to IDLE the moment the panel refreshes.
        d = self._multi_display(adb_id)
        d["status"], d["badge"] = text, (bg, fg)
        row = self._multi_rows.get(adb_id)
        if not row:
            return
        row["status_var"].set(text)
        try:
            row["status_lbl"].configure(bg=bg, fg=fg)
        except tk.TclError:
            pass

    # ── test single ────────────────────────────────────────────────────────
    def _refresh_single_lb(self):
        try:
            if not hasattr(self, "_single_lb") or not self._single_lb.winfo_exists():
                return
        except Exception:
            return
        # Use dedicated test scan results if available, else fall back to active_devices
        devs = getattr(self, "_test_devices", None)
        if devs is None:
            devs = self.active_devices
        self._single_lb.delete(0, tk.END)
        for dev in devs:
            self._single_lb.insert(tk.END, f"  {dev['name']:<16} {dev['adb_id']}")
        if devs:
            self._single_lb.selection_set(0)
            self._single_device.set(devs[0]["adb_id"])

    def _on_single_sel(self, _=None):
        try:
            if not hasattr(self, "_single_lb") or not self._single_lb.winfo_exists():
                return
        except Exception:
            return
        devs = getattr(self, "_test_devices", None)
        if devs is None:
            devs = self.active_devices
        sel = self._single_lb.curselection()
        if sel and sel[0] < len(devs):
            self._single_device.set(devs[sel[0]]["adb_id"])

    def _single_run(self):
        if not hasattr(self, "_task_sel"):
            return
        dev_id    = self._single_device.get()
        task_keys = self._task_sel.selected_tasks()
        if not dev_id:
            messagebox.showwarning("No device", "Select a device.")
            return
        if not task_keys:
            messagebox.showwarning("No tasks", "Check at least one task.")
            return
        self._single_stop.clear()
        self._set_status(f"● RUNNING  {dev_id.split(':')[-1]}", PRI)
        try:
            self._test_run_btn.configure(state=tk.DISABLED)
            self._test_stop_btn.configure(state=tk.NORMAL)
        except Exception:
            pass

        def _log_fn(msg, tag="dim"):
            self.q.put(("test_log", msg, tag))

        _single_keys_expanded = self._task_sets.expand_keys(task_keys)
        if task_keys and not _single_keys_expanded:
            _log_fn("no runnable tasks — every configured task is invalid or "
                    "the referenced task set is missing", "err")
            _multi_log.error(
                f"[TEST] {dev_id} no runnable tasks after expansion: {task_keys}")
            self.q.put(("single_done", dev_id, task_keys, False,
                        "no_runnable_tasks"))
            return

        def worker():
            if self.demo:
                for k in _single_keys_expanded:
                    if self._single_stop.is_set():
                        break
                    time.sleep(0.8)
                    lbl = TASK_DEFS[k]["label"] if k in TASK_DEFS else k
                    _log_fn(f"✓ {lbl}", "ok")
                ok, result = not self._single_stop.is_set(), "done"
            else:
                ok, result = self.bridge.run_tasks(
                    dev_id, _single_keys_expanded,
                    self.skip_var.get(), self._single_stop, _log_fn)
            self.q.put(("single_done", dev_id, task_keys, ok, result))

        threading.Thread(target=worker, daemon=False, name=f"single_worker_{dev_id}").start()

    def _single_stop_fn(self):
        self._single_stop.set()
        dev_id = self._single_device.get()
        _multi_log.info(f"[DIAG] _single_stop_fn ── STOP signal sent for {dev_id!r}")
        if dev_id:
            def _flush(did=dev_id):
                try:
                    _multi_log.info(f"[DIAG] _single_stop_fn ── waiting 5s for task to finish cleanly")
                    time.sleep(5)
                    bot = self.bridge.load_bot()
                    pending = getattr(bot, "_PENDING_STATUS", {})
                    pending_fields = list(pending.get(did, {}).keys())
                    _multi_log.info(
                        f"[DIAG] _single_stop_fn ── calling flush_status for {did!r} "
                        f"(pending: {pending_fields})"
                    )
                    bot.flush_status(did)
                    _multi_log.info(f"[DIAG] _single_stop_fn ── flush_status done ✓ for {did!r}")
                    self.q.put(("log", f"✓ Flushed {did.split(':')[-1]} to sheet", "ok"))
                except Exception as _fex:
                    _multi_log.error(f"[DIAG] _single_stop_fn ── flush FAILED for {did!r}: {_fex}")
            threading.Thread(target=_flush, daemon=False).start()

    # ══════════════════════════════════════════════════════════════════════════
    # TAB: TASK CONFIG
    # ══════════════════════════════════════════════════════════════════════════
    # ══════════════════════════════════════════════════════════════════════════
    # H: NAMED STATE SAVE / LOAD / DELETE
    # ══════════════════════════════════════════════════════════════════════════

    def _named_state_save(self):
        from tkinter import simpledialog
        name = simpledialog.askstring(
            "Save State", "Enter a name for this state:",
            parent=self,
        )
        if not name or not name.strip():
            return
        name = name.strip()
        self._named_state_mgr.save(name, self._collect_state())
        _multi_log.info(f"[STATE] saved named state {name!r}")
        self._log(f"[STATE] saved named state '{name}'", "ok")
        try:
            self._ns_listbox.delete(0, tk.END)
            for n in self._named_state_mgr.list_names():
                self._ns_listbox.insert(tk.END, n)
        except Exception:
            pass

    def _set_multi_selection(self, adb_id: str, keys, user_edit: bool = True) -> None:
        """
        The ONE way a Multi-Test selection changes.

        Model, widget, invalid marker and badge were being updated in four
        different places with four slightly different sets of steps — which is
        how a corrected row kept its NO TASKS badge and was then skipped by
        Start All, since that only considers IDLE / FAILED / STOPPED.

        `user_edit=False` is used by state restoration: it must not erase the
        invalid provenance the snapshot just restored, and must not pretend the
        user fixed anything.
        """
        keys = list(keys or [])
        self._multi_task_selections[adb_id] = list(keys)

        row = self._multi_rows.get(adb_id)
        if row is not None:
            ref = row.get("tasks_ref")
            if ref is not None:
                ref["keys"] = list(keys)
            if row.get("task_count"):
                try:
                    row["task_count"].set(_tasks_short_label(keys))
                except Exception:
                    pass

        if not user_edit:
            return

        # A deliberate edit invalidates any marker describing the OLD selection.
        self._clear_invalid_multi(adb_id)

        # Release a row parked on a no-runnable badge so Start All sees it
        # again. Never touch a row whose worker is live.
        if row is not None and adb_id not in self._multi_active_workers():
            try:
                cur = row["status_var"].get()
            except Exception:
                cur = ""
            if cur in ("NO TASKS", "INVALID TASKS"):
                self._multi_set_badge(adb_id, "IDLE", BADGE_IDLE[0], BADGE_IDLE[1])
                try:
                    row["start_btn"].configure(state=tk.NORMAL)
                    row["stop_btn"].configure(state=tk.DISABLED)
                except Exception:
                    pass

    def _multi_display(self, adb_id: str) -> dict:
        """Canonical per-device Test display state. Never holds thread objects."""
        return self._multi_display_state.setdefault(
            adb_id, {"status": "IDLE", "badge": BADGE_IDLE, "log": "—"})

    def _schedule_pending_multi_refresh(self) -> None:
        """
        Poll until every Multi-Test worker has actually exited, then rebuild.

        A single check at multi_done is not enough: the worker queues that
        message and only then returns, so it is still is_alive() for a few
        instructions afterwards. That race left the deferred refresh pending
        forever. At most one callback is outstanding, on the Tk thread.
        """
        if getattr(self, "_multi_refresh_after_id", None) is not None:
            return
        try:
            self._multi_refresh_after_id = self.after(
                80, self._try_pending_multi_refresh)
        except Exception:
            self._multi_refresh_after_id = None

    def _try_pending_multi_refresh(self) -> None:
        self._multi_refresh_after_id = None
        if not self._multi_panel_refresh_pending:
            return                                    # nothing to do; stop polling
        if self._multi_active_workers():
            self._schedule_pending_multi_refresh()    # bounded re-check
            return
        _multi_log.info("[MULTI-TEST] all workers finished — applying the "
                        "deferred panel refresh")
        try:
            self._render_test_multi_panel()
        except Exception as exc:
            _multi_log.warning(f"[MULTI-TEST] deferred refresh failed: {exc!r}")

    # Statuses that describe the SELECTION rather than a run. Only these may be
    # rewritten when a snapshot changes what a device is configured to do;
    # RUNNING, STOPPING…, DONE ✓, FAILED ✗ and STOPPED are outcomes and must
    # survive untouched.
    _SELECTION_BADGES = ("IDLE", "NO TASKS", "INVALID TASKS")

    def _sync_multi_selection_badge(self, adb_id: str) -> None:
        """
        Bring a rendered row's badge back in line with its restored selection.

        Restoration deliberately uses user_edit=False so it cannot erase the
        provenance it just restored — but that also means the badge-reset that
        a user edit performs does not happen, leaving a stale NO TASKS or
        INVALID TASKS on a row whose selection is now perfectly runnable.
        """
        row = self._multi_rows.get(adb_id)
        try:
            cur = row["status_var"].get() if row else \
                self._multi_display(adb_id).get("status", "IDLE")
        except Exception:
            cur = "IDLE"
        # Never overwrite a run outcome or a live run.
        if cur not in self._SELECTION_BADGES:
            return
        if adb_id in self._multi_active_workers():
            return

        keys = self._multi_task_selections.get(adb_id, [])
        invalid = self._invalid_multi_tasks.get(adb_id)
        if invalid and not keys:
            want = "INVALID TASKS"
        elif not keys:
            want = "NO TASKS"
        else:
            want = "IDLE"
        if want != cur:
            # _multi_set_badge writes _multi_display_state too, and leaves the
            # stored last-log line alone.
            self._multi_set_badge(adb_id, want, BADGE_IDLE[0], BADGE_IDLE[1])

    def _apply_state_snapshot(self, state: dict, source: str = "") -> None:
        """
        Apply a COMPLETE saved-state snapshot. Replaces, never merges.

        _load_state and _named_state_load had grown two near-identical copies of
        this logic and had already drifted — the named path silently forgot
        record_video. One helper so they cannot drift again.

        Two rules make the difference between correct and subtly wrong here:

        * Everything selection-related is CLEARED first. Rebuilding only the
          keys the incoming state mentions let a DeviceType or device from the
          previous snapshot keep its tasks forever.
        * Restoration is driven by the canonical model, not by the widgets. A
          device that is offline (so has no row) still gets its selection and
          its invalid provenance restored; only the widget update is conditional
          on a row existing.
        """
        # ── scalars ──────────────────────────────────────────────────────────
        for var, key, default in (
                (getattr(self, "skip_var", None), "skip_before", False),
                (getattr(self, "retry_var", None), "retry_enabled", False),
                (getattr(self, "_record_video", None), "record_video", False),
                (getattr(self, "_max_concurrent", None), "max_concurrent", 5)):
            if var is None:
                continue
            try:
                var.set(state.get(key, default))
            except Exception:
                pass

        # ── replace, do not merge ────────────────────────────────────────────
        self.task_config.clear()
        self._multi_task_selections.clear()
        self._invalid_task_config.clear()
        self._invalid_multi_tasks.clear()

        # ── Task Config ──────────────────────────────────────────────────────
        _tc_raw = state.get("task_config") or {}
        _tc_inv = state.get("invalid_task_config") or {}
        # Union: a provenance-only entry from an older or partially repaired
        # file would otherwise be dropped without trace.
        for dt in list(_tc_raw) + [k for k in _tc_inv if k not in _tc_raw]:
            _v = self._task_sets.validate_selection(
                _tc_raw.get(dt, []), where=f"{source}task_config[{dt}]")
            # A selection that already validated to nothing on a previous run
            # was SAVED as [] — the persisted provenance is the only thing that
            # still says it was not empty by choice.
            if not _v["had_input"] and _tc_inv.get(dt):
                _v = {"valid": [], "invalid": list(_tc_inv[dt]), "had_input": True}
            self.task_config[dt] = _v["valid"]
            self._mark_invalid_config(dt, _v)

        # A DeviceType that exists now but predates this snapshot must appear as
        # an explicit EMPTY config — not inherit tasks, and not go missing.
        try:
            self._discover_task_config(self.conf_devices)
        except Exception as exc:
            _multi_log.warning(f"[STATE] _discover_task_config after load: {exc!r}")

        # ── Run-panel checkboxes ─────────────────────────────────────────────
        # A snapshot REPLACES the tick state. Applying only the incoming entries
        # left a device that was ticked before the load — and omitted from the
        # snapshot — still selected, so a Run would silently include it.
        _rc = state.get("run_checks")
        if not isinstance(_rc, dict):
            # Defensive: a caller may bypass StateManager entirely.
            if _rc is not None:
                _multi_log.warning(
                    f"[STATE] {source}run_checks is {type(_rc).__name__}, "
                    f"expected a dict — ignoring it")
            _rc = {}
        # Canonical model first, and completely. Entries for devices with no row
        # are KEPT, not discarded: that is the whole point of the model, and it
        # is what restores an offline device's tick when it next appears.
        self._run_check_selections.clear()
        for adb_id, val in _rc.items():
            self._run_check_selections[adb_id] = bool(val)
        # Then every RENDERED box, including the ones the snapshot never
        # mentioned — those become False rather than keeping a pre-load tick.
        for adb_id in list(self._run_checks):
            self._set_run_checked(
                adb_id, self._run_check_selections.get(adb_id, False))

        # ── Multi-Test selections ────────────────────────────────────────────
        _mt_raw = state.get("multi_tasks") or {}
        _mt_inv = state.get("invalid_multi_tasks") or {}
        for adb_id in list(_mt_raw) + [k for k in _mt_inv if k not in _mt_raw]:
            _v = self._task_sets.validate_selection(
                _mt_raw.get(adb_id, []), where=f"{source}multi_tasks[{adb_id}]")
            _saved_inv = _mt_inv.get(adb_id)
            if not _v["had_input"] and _saved_inv:
                _v = {"valid": [], "invalid": list(_saved_inv), "had_input": True}
            # Model first, and unconditionally — the device may be offline.
            self._set_multi_selection(adb_id, _v["valid"], user_edit=False)
            self._mark_invalid_multi(adb_id, _v)

        # Every RENDERED row must now agree with the rebuilt model, including
        # rows the snapshot never mentioned. Leaving those alone kept their old
        # tasks_ref, and the next _collect_state folded that stale widget value
        # straight back into the canonical model — resurrecting a selection the
        # snapshot had removed.
        for adb_id in list(self._multi_rows):
            if adb_id in self._multi_task_selections:
                self._set_multi_selection(
                    adb_id, self._multi_task_selections[adb_id], user_edit=False)
            else:
                # Visible now, absent from the snapshot: treat exactly like a
                # newly discovered device rather than keeping stale contents.
                self._set_multi_selection(
                    adb_id, self._task_sets.all_keys() + list(SUBTASK_ORDER),
                    user_edit=False)
                self._invalid_multi_tasks.pop(adb_id, None)

        # Selection-state badges for EVERY device the rebuilt model describes —
        # not only the rendered ones. An offline device restored with [] kept
        # whatever _multi_display_state said before the load (usually IDLE), and
        # that stale value is exactly what seeds status_var when the device
        # finally appears — so a device with nothing to run showed up as ready.
        # _sync_multi_selection_badge falls back to _multi_display() when there
        # is no row, so one call covers both cases and the truth table stays in
        # one place. dict.fromkeys: ordered union, no duplicate calls.
        for adb_id in dict.fromkeys(list(self._multi_task_selections)
                                    + list(self._invalid_multi_tasks)
                                    + list(self._multi_rows)):
            # Selection-state badges only — never a runtime/terminal state.
            self._sync_multi_selection_badge(adb_id)

        try:
            self._build_task_config_tab()
        except Exception:
            pass

    def _named_state_load(self):
        try:
            sel = self._ns_listbox.curselection()
            if not sel:
                messagebox.showwarning("No Selection", "Select a state to load.", parent=self)
                return
            name = self._ns_listbox.get(sel[0])
        except Exception:
            return
        state = self._named_state_mgr.load(name)
        if not state:
            messagebox.showwarning("Not Found", f"State '{name}' not found.", parent=self)
            return
        self._apply_state_snapshot(state, source=f"{name}:")
        _multi_log.info(f"[STATE] loaded named state {name!r}")
        self._log(f"[STATE] loaded named state '{name}'", "ok")

    def _named_state_delete(self):
        try:
            sel = self._ns_listbox.curselection()
            if not sel:
                messagebox.showwarning("No Selection", "Select a state to delete.", parent=self)
                return
            name = self._ns_listbox.get(sel[0])
        except Exception:
            return
        confirmed = messagebox.askyesno(
            "Delete State",
            f"Delete named state '{name}'?\nThis cannot be undone.",
            parent=self,
        )
        if not confirmed:
            return
        self._named_state_mgr.delete(name)
        _multi_log.info(f"[STATE] deleted named state {name!r}")
        self._log(f"[STATE] deleted named state '{name}'", "warn")
        try:
            self._ns_listbox.delete(0, tk.END)
            for n in self._named_state_mgr.list_names():
                self._ns_listbox.insert(tk.END, n)
        except Exception:
            pass

    def _build_named_states_ui(self, parent, row: int = 1):
        """H: Named state save/load/delete panel — must be gridded into parent."""
        frm = tk.LabelFrame(
            parent, text=" Named States ", font=FSB,
            bg=BG_PANEL, fg=FG_DIM, bd=1, relief=tk.SOLID,
            labelanchor="nw",
        )
        frm.grid(row=row, column=0, sticky="ew", padx=4, pady=(4, 0))

        # Listbox
        lb_wrap = tk.Frame(frm, bg=BG_PANEL)
        lb_wrap.pack(fill=tk.X, padx=6, pady=(4, 0))
        self._ns_listbox = tk.Listbox(
            lb_wrap, height=4, font=FMN,
            bg=BG_CELL, fg=FG_MAIN, selectbackground=PRI,
            selectforeground="white", relief=tk.FLAT, bd=0,
        )
        self._ns_listbox.pack(side=tk.LEFT, fill=tk.X, expand=True)
        sb_ns = tk.Scrollbar(lb_wrap, orient=tk.VERTICAL,
                              command=self._ns_listbox.yview,
                              bg=BG_MID, troughcolor=BG_MID)
        sb_ns.pack(side=tk.RIGHT, fill=tk.Y)
        self._ns_listbox.configure(yscrollcommand=sb_ns.set)
        for n in self._named_state_mgr.list_names():
            self._ns_listbox.insert(tk.END, n)

        # Buttons
        btn_row = tk.Frame(frm, bg=BG_PANEL)
        btn_row.pack(fill=tk.X, padx=6, pady=(2, 6))
        _btn(btn_row, "💾 Save",   self._named_state_save,   bg=ACC_BLUE, fg="white",  font=FS, padx=6, pady=2).pack(side=tk.LEFT, padx=2)
        _btn(btn_row, "📂 Load",   self._named_state_load,   bg=BG_CELL,  fg=FG_MAIN,  font=FS, padx=6, pady=2).pack(side=tk.LEFT, padx=2)
        _btn(btn_row, "🗑 Delete", self._named_state_delete, bg=CLR_FAIL, fg=FG_ERR,   font=FS, padx=6, pady=2).pack(side=tk.LEFT, padx=2)

    def _build_task_config_tab(self):
        tab = self._tab_taskconf
        for w in tab.winfo_children():
            w.destroy()
        tab.rowconfigure(0, weight=1)
        tab.columnconfigure(0, weight=1)

        wrap = tk.Frame(tab, bg=BG_BASE)
        wrap.grid(row=0, column=0, sticky="nsew", padx=6, pady=6)
        wrap.rowconfigure(0, weight=1)
        wrap.columnconfigure(0, weight=1)

        canvas = tk.Canvas(wrap, bg=BG_BASE, bd=0, highlightthickness=0)
        sb = tk.Scrollbar(wrap, orient=tk.VERTICAL, command=canvas.yview, bg=BG_MID, troughcolor=BG_MID)
        canvas.configure(yscrollcommand=sb.set)
        sb.grid(row=0, column=1, sticky="ns")
        canvas.grid(row=0, column=0, sticky="nsew")
        inner = tk.Frame(canvas, bg=BG_BASE)
        win_id = canvas.create_window((0, 0), window=inner, anchor=tk.NW)
        inner.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.bind("<Configure>", lambda e: canvas.itemconfig(win_id, width=e.width))

        # Sort: named types first, (no tag) / "" last
        types = sorted(k for k in self.task_config if k)
        if "" in self.task_config:
            types.append("")

        for dt in types:
            display_name = dt if dt else "(no tag)"
            current_tasks = self.task_config.get(dt, list(SUBTASK_ORDER))

            section = tk.Frame(inner, bg=BG_PANEL)
            section.pack(fill=tk.X, pady=4, padx=4)

            expanded = tk.BooleanVar(value=True)
            body = tk.Frame(section, bg=BG_PANEL)

            def _toggle(b=body, ev=expanded, tb=None, dn=display_name):
                if ev.get():
                    b.pack_forget()
                    ev.set(False)
                    if tb:
                        tb.configure(text=f"▶ {dn}")
                else:
                    b.pack(fill=tk.X)
                    ev.set(True)
                    if tb:
                        tb.configure(text=f"▼ {dn}")

            hdr = tk.Frame(section, bg="#1A1A30")
            hdr.pack(fill=tk.X)
            tbtn = tk.Button(hdr, text=f"▼ {display_name}", font=FNB, bg="#1A1A30", fg=ACC_BLUE,
                      relief=tk.FLAT, padx=8, pady=4, cursor="hand2", bd=0, anchor=tk.W)
            tbtn.configure(command=lambda b=body, ev=expanded, tb=tbtn, dn=display_name: _toggle(b, ev, tb, dn))
            tbtn.pack(side=tk.LEFT, fill=tk.X, expand=True)

            body.pack(fill=tk.X)
            task_vars: dict[str, tk.BooleanVar] = {}

            # ── Task Sets section ────────────────────────────────────
            sets = self._task_sets.all_sets()
            if sets:
                tk.Label(body, text="── Task Sets ──",
                         font=(FN[0], FN[1], "bold"),
                         bg=BG_PANEL, fg=ACC_BLUE).pack(fill=tk.X, padx=12, pady=(4,1))
                for s in sets:
                    sk = self._task_sets.set_key(s["name"])
                    v_s = tk.BooleanVar(value=(sk in current_tasks))
                    task_vars[sk] = v_s
                    def _on_set_change(dt_=dt, tv=task_vars):
                        self.task_config[dt_] = [
                            k_ for k_ in tv if tv[k_].get()
                        ]
                        # The user just chose; any stale "invalid" marker from a
                        # previous load no longer describes this selection.
                        self._clear_invalid_config(dt_)
                    tk.Checkbutton(body, text=f"📦 {s['name']}", variable=v_s,
                                   font=FN, bg=BG_PANEL, fg="#FFD700",
                                   selectcolor=BG_CELL, activebackground=BG_PANEL,
                                   command=_on_set_change, anchor=tk.W
                                   ).pack(fill=tk.X, padx=12)
                tk.Label(body, text="── Individual Tasks ──",
                         font=(FN[0], FN[1], "bold"),
                         bg=BG_PANEL, fg=FG_DIM).pack(fill=tk.X, padx=12, pady=(6,1))

            # ── Individual tasks ─────────────────────────────────────────
            for k in SUBTASK_ORDER:
                v = tk.BooleanVar(value=(k in current_tasks))
                task_vars[k] = v
                def _on_change(dt_=dt, tv=task_vars):
                    self.task_config[dt_] = [k_ for k_ in tv if tv[k_].get()]
                    self._clear_invalid_config(dt_)

                tk.Checkbutton(body, text=TASK_DEFS[k]["label"], variable=v,
                               font=FN, bg=BG_PANEL, fg=FG_MAIN, selectcolor=BG_CELL,
                               activebackground=BG_PANEL, command=_on_change, anchor=tk.W
                               ).pack(fill=tk.X, padx=12)

            # Select all / none buttons
            bf = tk.Frame(body, bg=BG_PANEL)
            bf.pack(fill=tk.X, padx=12, pady=4)
            def _all(tv=task_vars, dt_=dt):
                for v_ in tv.values(): v_.set(True)
                self.task_config[dt_] = list(tv.keys())
                self._clear_invalid_config(dt_)
            def _none(tv=task_vars, dt_=dt):
                for v_ in tv.values(): v_.set(False)
                self.task_config[dt_] = []
                # Explicitly cleared: setup-only is a valid intent again.
                self._clear_invalid_config(dt_)
            _btn(bf, "All", _all, bg=BG_CELL, fg=ACC_BLUE, font=FS, padx=5, pady=2).pack(side=tk.LEFT, padx=2)
            _btn(bf, "None", _none, bg=BG_CELL, fg=FG_DIM, font=FS, padx=5, pady=2).pack(side=tk.LEFT)

    # ══════════════════════════════════════════════════════════════════════════
    # TAB: SHEET (ttk.Treeview)
    # ══════════════════════════════════════════════════════════════════════════
    def _build_sheet_tab(self):
        tab = self._tab_sheet
        tab.rowconfigure(1, weight=1)
        tab.columnconfigure(0, weight=1)

        hdr = tk.Frame(tab, bg=BG_MID)
        hdr.grid(row=0, column=0, sticky="ew")
        tk.Label(hdr, text="SHEET MIRROR", font=FH, bg=BG_MID, fg=PRI, padx=8, pady=6).pack(side=tk.LEFT)
        _btn(hdr, "🔄 Refresh", self._sheet_refresh, bg=BG_CELL, fg=ACC_BLUE, font=FSB).pack(side=tk.RIGHT, padx=8, pady=4)

        tree_wrap = tk.Frame(tab, bg=BG_BASE)
        tree_wrap.grid(row=1, column=0, sticky="nsew", padx=6, pady=(0, 6))
        tree_wrap.rowconfigure(0, weight=1)
        tree_wrap.columnconfigure(0, weight=1)

        self._sheet_tree = ttk.Treeview(tree_wrap, style="Sheet.Treeview", show="headings")
        vsb = ttk.Scrollbar(tree_wrap, orient=tk.VERTICAL, command=self._sheet_tree.yview)
        hsb = ttk.Scrollbar(tree_wrap, orient=tk.HORIZONTAL, command=self._sheet_tree.xview)
        self._sheet_tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        vsb.grid(row=0, column=1, sticky="ns")
        hsb.grid(row=1, column=0, sticky="ew")
        self._sheet_tree.grid(row=0, column=0, sticky="nsew")

        self._sheet_tree.bind("<ButtonRelease-1>", self._on_sheet_click)

        # Task header columns (for identifying clickable cells)
        self._sheet_task_cols: set[str] = set()
        self._sheet_col_to_taskkey: dict[str, str] = {}

        # Auto-sync timer
        self._schedule_sheet_sync()

    def _draw_sheet_grid(self):
        tree = self._sheet_tree
        # Clear everything
        tree.delete(*tree.get_children())
        for col in tree["columns"]:
            tree.heading(col, text="")
        tree["columns"] = ()

        rows_by_dev = self.bridge.rows_by_device
        if not rows_by_dev:
            tree["columns"] = ("info",)
            tree.heading("info", text="No data loaded")
            tree.column("info", width=400)
            return

        # Build columns from first row keys
        sample = next(iter(rows_by_dev.values()))
        col_keys = list(sample.keys())

        # Determine which columns are task status columns
        # rows_by_device keys: vip_collect_status, etc.
        self._sheet_task_cols = set()
        self._sheet_col_to_taskkey: dict[str, str] = {}
        for tk_key, td in TASK_DEFS.items():
            # The row dict key pattern: vip_collect_status, etc.
            # Match by checking if col_key corresponds to the status_attr minus leading _
            attr_key = td["status_attr"].lstrip("_")  # e.g. "vip_collect_status"
            for ck in col_keys:
                if ck == attr_key:
                    self._sheet_task_cols.add(ck)
                    if td.get("header"):  # only clickable if has header
                        self._sheet_col_to_taskkey[ck] = tk_key
                    break

        display_cols = list(col_keys)
        tree["columns"] = display_cols
        for ck in display_cols:
            w = 90 if ck in self._sheet_task_cols else 130
            tree.heading(ck, text=ck.replace("_", " ").title() if len(ck) < 25 else ck[:24])
            tree.column(ck, width=w, minwidth=30, stretch=False)

        # Row tags for visual grouping
        tree.tag_configure("even", background="#161628")
        tree.tag_configure("odd",  background="#111120")
        tree.tag_configure("done_row", foreground="#5CDD5C")

        # Sort rows by device_type then friendly name
        sorted_rows = sorted(rows_by_dev.values(),
                             key=lambda r: (r.get("device_type", ""), r.get("friendly", "")))

        for ri, row in enumerate(sorted_rows):
            vals = []
            for ck in display_cols:
                v = str(row.get(ck, ""))
                if ck in self._sheet_task_cols:
                    vl = v.strip().lower()
                    if vl == "done":
                        v = "✓ done"
                    elif vl == "":
                        v = "—"
                    # else keep original (error text)
                vals.append(v)
            dev_id = row.get("device_id", "")
            row_tag = "even" if ri % 2 == 0 else "odd"
            tree.insert("", tk.END, values=vals, iid=dev_id, tags=(row_tag,))

    def _on_sheet_click(self, event):
        tree = self._sheet_tree
        region = tree.identify_region(event.x, event.y)
        if region != "cell":
            return
        col_id = tree.identify_column(event.x)
        row_id = tree.identify_row(event.y)
        if not col_id or not row_id:
            return
        col_idx = int(col_id.replace("#", "")) - 1
        cols = list(tree["columns"])
        if col_idx < 0 or col_idx >= len(cols):
            return
        col_name = cols[col_idx]

        # Only allow clicking task status columns that have a header
        task_key = getattr(self, "_sheet_col_to_taskkey", {}).get(col_name)
        if not task_key:
            return

        dev_id = row_id
        if self.demo:
            return

        def _do_toggle():
            try:
                self.bridge.toggle_status(dev_id, task_key)
                self.q.put(("sheet_redraw", None))
                self.q.put(("log", f"Toggled {task_key} for {dev_id}", "ok"))
            except ValueError as ve:
                # L: header=None task — show warning instead of writing null column
                self.q.put(("log", f"Cannot toggle '{task_key}': {ve}", "warn"))
                self.after(0, lambda: messagebox.showwarning(
                    "Toggle Not Allowed",
                    f"Task '{task_key}' cannot be toggled manually:\n\n{ve}",
                    parent=self,
                ))
            except Exception as ex:
                self.q.put(("log", f"Toggle error: {ex}", "err"))
        threading.Thread(target=_do_toggle, daemon=True).start()

    def _prepare_for_sheet_read(self, reason: str = "") -> None:
        """
        J: Common pre-read guard for any path that reads from Google Sheets.
        1. Drain controller queue cache messages (apply in-flight updates).
        2. If dirty or pending writes remain, flush controller cache → Sheets.
        This guarantees the subsequent Sheets read never clobbers unsynced
        done-values held only in the controller cache.
        """
        try:
            self._drain_controller_queue_cache_messages(reason=f"sheet_read:{reason}")
        except Exception as ex:
            _multi_log.warning(f"[SHEET-READ] drain failed ({reason}): {ex}")
        try:
            if self._cache_dirty or self._pending_sheet_status:
                _multi_log.info(f"[SHEET-READ] flushing dirty cache before read ({reason})")
                self._flush_pending_sheet_status()
        except Exception as ex:
            _multi_log.warning(f"[SHEET-READ] pre-read flush failed ({reason}): {ex}")

    def _post_sheet_read_rebuild(self) -> None:
        """
        J: After a Sheets read, rebuild controller cache from the fresh sheet and
        overlay any pending writes that still remain (e.g. a sync that failed).
        """
        try:
            self._rebuild_status_cache_from_sheet()
            self._apply_pending_sheet_status_to_local_cache()
        except Exception as ex:
            _multi_log.warning(f"[SHEET-READ] post-read rebuild failed: {ex}")

    def _sheet_refresh(self):
        def worker():
            try:
                # J/S13/S20: drain + flush controller cache before reading Sheets.
                # Removed the old per-device bot.flush_status() loop that bypassed
                # the controller cache.
                self._prepare_for_sheet_read("sheet_refresh")
                self.bridge.refresh_sheet(force=True)
                self._post_sheet_read_rebuild()
                self.q.put(("sheet_redraw", None))
                self.q.put(("log", "✓ Sheet refreshed", "ok"))
            except Exception as ex:
                self.q.put(("log", f"Sheet refresh error: {ex}", "err"))
        threading.Thread(target=worker, daemon=True).start()

    def _schedule_sheet_sync(self):
        """
        D: Auto-sync cache → Sheets every 60 seconds while at least one device
        is running.  Direction is cache→sheet only — never sheet→cache during a run.
        Skips entirely when nothing is running or cache is not dirty.
        """
        def _sync():
            if self.demo:
                return
            active_ids = list(self._running_devs.keys())
            if not active_ids:
                _multi_log.debug("[SYNC] _schedule_sheet_sync tick — nothing running, skipping")
                return
            if not self._cache_dirty:
                _multi_log.debug("[SYNC] _schedule_sheet_sync tick — cache clean, skipping")
                return
            _multi_log.info(
                f"[SYNC] _schedule_sheet_sync tick — "
                f"{len(active_ids)} device(s) running, flushing dirty cache"
            )
            self._flush_pending_sheet_status()
            # Update sheet grid display from controller-side cache (no Sheets read)
            self.q.put(("sheet_redraw", None))

        def _tick():
            threading.Thread(target=_sync, daemon=True).start()
            self.after(60_000, _tick)

        self.after(60_000, _tick)

    # ══════════════════════════════════════════════════════════════════════════
    # TAB: SYNC DEVICES
    # ══════════════════════════════════════════════════════════════════════════
    def _build_sync_devices_tab(self):
        tab = self._tab_sync
        tab.rowconfigure(1, weight=1)
        tab.columnconfigure(0, weight=1)

        hdr = tk.Frame(tab, bg=BG_MID)
        hdr.grid(row=0, column=0, sticky="ew")
        tk.Label(hdr, text="SYNC DEVICES", font=FH, bg=BG_MID,
                 fg=PRI, padx=8, pady=6).pack(side=tk.LEFT)

        self._sync_btn = _btn(hdr, "⟳  Sync Now", self._run_sync_devices,
                              bg=ACC_BLUE, fg="white", font=FNB)
        self._sync_btn.pack(side=tk.LEFT, padx=8, pady=6)

        self._sync_status_lbl = tk.Label(hdr, text="", font=FS, bg=BG_MID, fg=FG_DIM)
        self._sync_status_lbl.pack(side=tk.LEFT, padx=8)

        body = tk.Frame(tab, bg=BG_BASE)
        body.grid(row=1, column=0, sticky="nsew", padx=24, pady=16)
        body.columnconfigure(0, weight=1)
        body.rowconfigure(3, weight=1)

        tk.Label(body, font=FN, bg=BG_BASE, fg=FG_DIM,
                 justify=tk.LEFT, anchor=tk.W,
                 text=("Reads BlueStacks conf and syncs devices into the control sheet.\n"
                       "  •  Missing devices are appended after the last existing row.\n"
                       "  •  Devices no longer in conf are removed from the sheet.\n"
                       "  •  If only the friendly name changed, that single cell is updated.")
                 ).grid(row=0, column=0, sticky="ew", pady=(0, 14))

        tk.Frame(body, bg=BG_CELL, height=1).grid(row=1, column=0, sticky="ew")

        tk.Label(body, text="LAST SYNC RESULT", font=FNB, bg=BG_BASE,
                 fg=PRI, pady=8).grid(row=2, column=0, sticky="w")

        self._sync_result_frame = tk.Frame(body, bg=BG_PANEL, relief=tk.FLAT, bd=0)
        self._sync_result_frame.grid(row=3, column=0, sticky="nsew")
        self._sync_result_frame.columnconfigure(0, weight=1)

        tk.Label(self._sync_result_frame,
                 text="No sync has been run yet.",
                 font=FN, bg=BG_PANEL, fg=FG_DIM, pady=20).pack()

    def _run_sync_devices(self):
        if self.demo:
            self._show_sync_result({
                "triggered": True, "total": 6,
                "added":        [{"adb_id": "localhost:5565", "name": "TARGET_APP-6"},
                                 {"adb_id": "localhost:5567", "name": "TARGET_APP-7"}],
                "name_updated": [{"adb_id": "localhost:5557",
                                  "old_name": "TARGET_APP-1", "new_name": "Device1"}],
                "unchanged": 3,
            })
            return

        self._sync_btn.configure(state=tk.DISABLED)
        self._sync_status_lbl.configure(text="Syncing…", fg=ACC_YEL)

        def _worker():
            try:
                result = self.bridge.sync_devices()
                self.q.put(("sync_result", result))
            except Exception as ex:
                self.q.put(("sync_result", {"error": str(ex)}))

        threading.Thread(target=_worker, daemon=True).start()

    def _show_sync_result(self, result: dict):
        try:
            self._sync_btn.configure(state=tk.NORMAL)
        except Exception:
            pass

        for w in self._sync_result_frame.winfo_children():
            w.destroy()

        if "error" in result:
            self._sync_status_lbl.configure(text="Error — see result panel", fg=FG_ERR)
            tk.Label(self._sync_result_frame,
                     text=f"✗  Sync failed:\n\n{result['error']}",
                     font=FN, bg=BG_PANEL, fg=FG_ERR,
                     pady=16, padx=16, justify=tk.LEFT).pack(anchor=tk.W)
            return

        added        = result.get("added",        [])
        name_updated = result.get("name_updated", [])
        removed      = result.get("removed",      [])
        unchanged    = result.get("unchanged",    0)
        total        = result.get("total",        0)

        self._sync_status_lbl.configure(text=f"Done at {_ts()}", fg="#5CCC5C")

        p   = self._sync_result_frame
        pad = dict(padx=16, pady=2, anchor=tk.W)

        tk.Label(p, text=f"✓  {len(added)} device(s) added",
                 font=FNB, bg=BG_PANEL, fg=("#5CCC5C" if added else FG_DIM),
                 pady=8).pack(**{**pad, "pady": (14, 2)})
        for d in added:
            tk.Label(p, text=f"      +  {d['adb_id']}  ({d['name']})",
                     font=FMN, bg=BG_PANEL, fg="#5CCC5C").pack(**pad)

        tk.Label(p, text=f"✎  {len(name_updated)} name(s) updated",
                 font=FNB, bg=BG_PANEL, fg=(ACC_YEL if name_updated else FG_DIM),
                 pady=4).pack(**{**pad, "pady": (12, 2)})
        for d in name_updated:
            tk.Label(p,
                     text=f"      {d['adb_id']}:  \"{d['old_name']}\"  →  \"{d['new_name']}\"",
                     font=FMN, bg=BG_PANEL, fg=ACC_YEL).pack(**pad)

        tk.Label(p, text=f"✗  {len(removed)} device(s) removed (not in conf)",
                 font=FNB, bg=BG_PANEL, fg=(FG_ERR if removed else FG_DIM),
                 pady=4).pack(**{**pad, "pady": (12, 2)})
        for d in removed:
            tk.Label(p, text=f"      -  {d['adb_id']}  ({d['name']})",
                     font=FMN, bg=BG_PANEL, fg=FG_ERR).pack(**pad)

        tk.Label(p, text=f"=  {unchanged} device(s) already up to date",
                 font=FN, bg=BG_PANEL, fg=FG_DIM,
                 pady=4).pack(**{**pad, "pady": (12, 2)})

        tk.Frame(p, bg=BG_CELL, height=1).pack(fill=tk.X, padx=16, pady=10)
        tk.Label(p, text=f"Total devices in sheet:  {total}",
                 font=FNB, bg=BG_PANEL, fg=FG_MAIN, pady=4).pack(**pad)

    # ══════════════════════════════════════════════════════════════════════════
    # TAB: VPN MONITOR
    # ══════════════════════════════════════════════════════════════════════════
    # ── FIX 4: Task Sets tab ──────────────────────────────────────────────────
    def _build_task_sets_tab(self):
        tab = self._tab_tasksets
        for w in tab.winfo_children(): w.destroy()
        tab.rowconfigure(1, weight=1)
        tab.columnconfigure(0, weight=1)
        tab.columnconfigure(1, weight=1)

        # ── Header ───────────────────────────────────────────────────────────
        hdr = tk.Frame(tab, bg=BG_MID)
        hdr.grid(row=0, column=0, columnspan=2, sticky="ew")
        tk.Label(hdr, text="📦  TASK SETS", font=FH, bg=BG_MID, fg=PRI,
                 padx=10, pady=8).pack(side=tk.LEFT)
        tk.Label(hdr,
                 text="Group tasks into reusable sets. Sets appear in all task selectors.",
                 font=FS, bg=BG_MID, fg=FG_DIM, padx=4).pack(side=tk.LEFT)

        # ── Left: existing sets list ─────────────────────────────────────────
        left = tk.Frame(tab, bg=BG_PANEL)
        left.grid(row=1, column=0, sticky="nsew", padx=(6,2), pady=6)
        left.rowconfigure(1, weight=1)
        left.columnconfigure(0, weight=1)
        tk.Label(left, text="Saved Sets", font=FNB, bg=BG_PANEL, fg=FG_MAIN,
                 padx=6, pady=4).grid(row=0, column=0, sticky="w")

        sets_lb_frame = tk.Frame(left, bg=BG_PANEL)
        sets_lb_frame.grid(row=1, column=0, sticky="nsew", padx=4)
        sets_lb_frame.rowconfigure(0, weight=1)
        sets_lb_frame.columnconfigure(0, weight=1)
        sets_sb = tk.Scrollbar(sets_lb_frame, bg=BG_MID, troughcolor=BG_MID)
        sets_sb.pack(side=tk.RIGHT, fill=tk.Y)
        self._sets_lb = tk.Listbox(sets_lb_frame, font=FN, bg=BG_CELL,
                                    fg=FG_MAIN, selectbackground=ACC_BLUE,
                                    relief=tk.FLAT, bd=0,
                                    yscrollcommand=sets_sb.set)
        self._sets_lb.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sets_sb.config(command=self._sets_lb.yview)
        self._sets_lb.bind("<<ListboxSelect>>", self._on_set_selected)

        btn_row = tk.Frame(left, bg=BG_PANEL)
        btn_row.grid(row=2, column=0, sticky="ew", pady=4)
        _btn(btn_row, "Delete Set", self._delete_set,
             bg=CLR_FAIL, fg=FG_ERR, font=FS).pack(side=tk.LEFT, padx=6)

        self._sets_lb_refresh()

        # ── Right: create / edit set ─────────────────────────────────────────
        right = tk.Frame(tab, bg=BG_PANEL)
        right.grid(row=1, column=1, sticky="nsew", padx=(2,6), pady=6)
        right.rowconfigure(3, weight=1)
        right.columnconfigure(0, weight=1)

        tk.Label(right, text="Set Name:", font=FNB, bg=BG_PANEL, fg=FG_MAIN,
                 padx=6, pady=4).grid(row=0, column=0, sticky="w")
        self._set_name_var = tk.StringVar()
        tk.Entry(right, textvariable=self._set_name_var, font=FMN,
                 bg=BG_CELL, fg=FG_MAIN, insertbackground=FG_MAIN,
                 relief=tk.FLAT).grid(row=1, column=0, sticky="ew", padx=6, pady=(0,6))

        tk.Label(right, text="Select tasks for this set:", font=FNB,
                 bg=BG_PANEL, fg=FG_MAIN, padx=6).grid(row=2, column=0, sticky="w")

        # Scrollable task checklist
        ck_wrap = tk.Frame(right, bg=BG_PANEL)
        ck_wrap.grid(row=3, column=0, sticky="nsew", padx=4)
        ck_wrap.rowconfigure(0, weight=1)
        ck_wrap.columnconfigure(0, weight=1)
        ck_canvas = tk.Canvas(ck_wrap, bg=BG_PANEL, bd=0, highlightthickness=0)
        ck_sb = tk.Scrollbar(ck_wrap, orient=tk.VERTICAL, command=ck_canvas.yview,
                             bg=BG_MID, troughcolor=BG_MID)
        ck_canvas.configure(yscrollcommand=ck_sb.set)
        ck_sb.pack(side=tk.RIGHT, fill=tk.Y)
        ck_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        ck_inner = tk.Frame(ck_canvas, bg=BG_PANEL)
        ck_wid = ck_canvas.create_window((0,0), window=ck_inner, anchor=tk.NW)
        ck_inner.bind("<Configure>", lambda e: ck_canvas.configure(
            scrollregion=ck_canvas.bbox("all")))
        ck_canvas.bind("<Configure>", lambda e: ck_canvas.itemconfig(ck_wid, width=e.width))

        self._set_task_vars: dict[str, tk.BooleanVar] = {}
        for k in SUBTASK_ORDER:
            v = tk.BooleanVar(value=False)
            self._set_task_vars[k] = v
            tk.Checkbutton(ck_inner, text=TASK_DEFS[k]["label"], variable=v,
                           font=FS, bg=BG_PANEL, fg=FG_MAIN,
                           selectcolor=BG_CELL, activebackground=BG_PANEL,
                           anchor=tk.W).pack(fill=tk.X, padx=8)

        save_row = tk.Frame(right, bg=BG_PANEL)
        save_row.grid(row=4, column=0, sticky="ew", pady=6)
        _btn(save_row, "✓ Save Set", self._save_set,
             bg=ACC_GRN, fg="white", font=FNB).pack(side=tk.LEFT, padx=6)
        _btn(save_row, "Clear", self._clear_set_form,
             bg=BG_CELL, fg=FG_DIM, font=FS).pack(side=tk.LEFT, padx=2)

    def _sets_lb_refresh(self):
        try:
            self._sets_lb.delete(0, tk.END)
            for s in self._task_sets.all_sets():
                tasks_str = ", ".join(SHORT_LABELS.get(t, t) for t in s["tasks"])
                self._sets_lb.insert(tk.END, f"  {s['name']}  [{tasks_str}]")
        except Exception:
            pass

    def _on_set_selected(self, _event=None):
        sel = self._sets_lb.curselection()
        if not sel:
            return
        sets = self._task_sets.all_sets()
        if sel[0] >= len(sets):
            return
        s = sets[sel[0]]
        self._set_name_var.set(s["name"])
        for k, v in self._set_task_vars.items():
            v.set(k in s["tasks"])

    def _save_set(self):
        name = self._set_name_var.get().strip()
        if not name:
            messagebox.showwarning("No name", "Enter a name for the task set.")
            return
        tasks = [k for k, v in self._set_task_vars.items() if v.get()]
        if not tasks:
            messagebox.showwarning("No tasks", "Select at least one task.")
            return
        self._task_sets.add_or_update(name, tasks)
        self._sets_lb_refresh()
        self._log(f"✓ Task set '{name}' saved ({len(tasks)} tasks)", "ok")
        # Refresh all task selectors across the UI
        self._refresh_all_task_selectors()

    def _delete_set(self):
        sel = self._sets_lb.curselection()
        if not sel:
            return
        sets = self._task_sets.all_sets()
        if sel[0] >= len(sets):
            return
        name = sets[sel[0]]["name"]
        if messagebox.askyesno("Delete Set", f"Delete task set '{name}'?"):
            self._task_sets.delete(name)
            self._sets_lb_refresh()
            self._clear_set_form()
            self._log(f"Deleted task set '{name}'", "warn")
            self._refresh_all_task_selectors()

    def _clear_set_form(self):
        self._set_name_var.set("")
        for v in self._set_task_vars.values():
            v.set(False)

    def _refresh_all_task_selectors(self):
        """Rebuild every place that shows task/set checkboxes after sets change."""
        # 1. TaskSelector in Test tab (single device)
        try:
            self._task_sel.refresh_sets()
        except Exception:
            pass
        # 2. Task Config tab (per device-type columns)
        try:
            self._build_task_config_tab()
        except Exception:
            pass
        # 3. TaskPopovers are created fresh each time they open — nothing to do.
        # 4. Multi-panel "Set All" popover reads sets live — nothing to do.

    def _build_vpn_monitor_tab(self):
        tab = self._tab_vpn
        tab.rowconfigure(1, weight=1)
        tab.columnconfigure(0, weight=1)

        hdr = tk.Frame(tab, bg=BG_MID)
        hdr.grid(row=0, column=0, sticky="ew")
        tk.Label(hdr, text="VPN MONITOR", font=FH, bg=BG_MID,
                 fg=PRI, padx=8, pady=6).pack(side=tk.LEFT)

        self._vpn_start_btn = _btn(hdr, "▶  Start", self._vpn_monitor_start,
                                   bg=ACC_GRN, fg="white", font=FNB)
        self._vpn_start_btn.pack(side=tk.LEFT, padx=6, pady=6)

        self._vpn_stop_btn = _btn(hdr, "■  Stop", self._vpn_monitor_stop,
                                  bg=CLR_FAIL, fg=FG_ERR, font=FNB, state=tk.DISABLED)
        self._vpn_stop_btn.pack(side=tk.LEFT, padx=4)

        self._vpn_status_lbl = tk.Label(hdr, text="● Stopped",
                                         font=(F, 8, "bold"), bg=BG_MID, fg=FG_DIM)
        self._vpn_status_lbl.pack(side=tk.LEFT, padx=14)

        body = tk.Frame(tab, bg=BG_BASE)
        body.grid(row=1, column=0, sticky="nsew")
        body.rowconfigure(0, weight=1)
        body.columnconfigure(0, weight=0)
        body.columnconfigure(1, weight=0)
        body.columnconfigure(2, weight=1)

        # ── Left: device grid ─────────────────────────────────────────────
        left = tk.Frame(body, bg=BG_PANEL, width=360)
        left.grid(row=0, column=0, sticky="nsew", padx=(6, 0), pady=6)
        left.pack_propagate(False)
        left.rowconfigure(1, weight=1)
        left.columnconfigure(0, weight=1)

        lhdr = tk.Frame(left, bg=BG_MID)
        lhdr.grid(row=0, column=0, sticky="ew")
        tk.Label(lhdr, text="DEVICES", font=FH, bg=BG_MID,
                 fg=PRI, padx=8, pady=6).pack(side=tk.LEFT)

        lscroll = tk.Frame(left, bg=BG_PANEL)
        lscroll.grid(row=1, column=0, sticky="nsew")
        lscroll.rowconfigure(0, weight=1)
        lscroll.columnconfigure(0, weight=1)

        self._vpn_canvas = tk.Canvas(lscroll, bg=BG_PANEL, bd=0, highlightthickness=0)
        vpn_sb = tk.Scrollbar(lscroll, orient=tk.VERTICAL,
                              command=self._vpn_canvas.yview,
                              bg=BG_MID, troughcolor=BG_MID)
        self._vpn_canvas.configure(yscrollcommand=vpn_sb.set)
        vpn_sb.grid(row=0, column=1, sticky="ns")
        self._vpn_canvas.grid(row=0, column=0, sticky="nsew")

        self._vpn_inner = tk.Frame(self._vpn_canvas, bg=BG_PANEL)
        self._vpn_win_id = self._vpn_canvas.create_window(
            (0, 0), window=self._vpn_inner, anchor=tk.NW)
        self._vpn_inner.bind(
            "<Configure>",
            lambda e: self._vpn_canvas.configure(
                scrollregion=self._vpn_canvas.bbox("all")))
        self._vpn_canvas.bind(
            "<Configure>",
            lambda e: self._vpn_canvas.itemconfig(self._vpn_win_id, width=e.width))

        tk.Label(self._vpn_inner,
                 text="Press  ▶ Start  to discover and monitor devices.",
                 font=FN, bg=BG_PANEL, fg=FG_DIM, pady=24).pack()

        # ── Separator ─────────────────────────────────────────────────────
        tk.Frame(body, bg="#2A2A40", width=1).grid(
            row=0, column=1, sticky="ns", pady=4)

        # ── Right: event log ──────────────────────────────────────────────
        right = tk.Frame(body, bg=BG_BASE)
        right.grid(row=0, column=2, sticky="nsew", padx=(0, 6), pady=6)
        right.rowconfigure(1, weight=1)
        right.columnconfigure(0, weight=1)

        rhdr = tk.Frame(right, bg=BG_MID)
        rhdr.grid(row=0, column=0, sticky="ew")
        tk.Label(rhdr, text="EVENT LOG  (changes only)",
                 font=FH, bg=BG_MID, fg=PRI, padx=8, pady=6).pack(side=tk.LEFT)
        tk.Button(rhdr, text="clear", bg=BG_MID, fg=FG_DIM, font=(F, 7),
                  relief=tk.FLAT, padx=6, pady=2, bd=0, cursor="hand2",
                  activebackground=BG_CELL,
                  command=self._vpn_clear_log).pack(side=tk.RIGHT, padx=6)

        self._vpn_log = scrolledtext.ScrolledText(
            right, font=(FM, 8), bg="#0A0A14", fg=FG_MAIN,
            state=tk.DISABLED, wrap=tk.WORD, relief=tk.FLAT, padx=10, pady=6)
        self._vpn_log.grid(row=1, column=0, sticky="nsew")
        self._vpn_log.tag_config("online",  foreground="#5CCC5C")
        self._vpn_log.tag_config("offline", foreground=FG_ERR)
        self._vpn_log.tag_config("info",    foreground=ACC_BLUE)
        self._vpn_log.tag_config("dim",     foreground=FG_DIM)

    # ── VPN monitor controls ───────────────────────────────────────────────────
    def _vpn_monitor_start(self):
        if not self._vpn_stop_event.is_set():
            return  # already running

        self._vpn_stop_event.clear()
        self._vpn_last_status.clear()
        self._vpn_start_btn.configure(state=tk.DISABLED)
        self._vpn_stop_btn.configure(state=tk.NORMAL)
        self._vpn_status_lbl.configure(text="● Connecting…", fg=ACC_YEL)
        self._vpn_write_log(
            f"[{_ts()}]  Discovering devices from BlueStacks conf…\n", "dim")

        def _start_worker():
            try:
                if self.demo:
                    raw = [{"port": "5557", "name": "TARGET_APP-1"},
                           {"port": "5559", "name": "TARGET_APP-2"},
                           {"port": "5561", "name": "TARGET_APP-3"}]
                else:
                    raw = self.bridge.get_conf_devices_raw()

                raw = [d for d in raw if str(d.get("port", "")) != "5555"]

                if not raw:
                    self.q.put(("vpn_started", [], {}, "No devices found in BlueStacks conf."))
                    return

                adb_ids = [f"localhost:{d['port']}" for d in raw]
                names   = {f"localhost:{d['port']}": (d.get("name") or f"localhost:{d['port']}")
                           for d in raw}

                self.q.put(("vpn_build_grid", adb_ids, names))

                if not self.demo:
                    self.q.put(("vpn_log_msg",
                                f"[{_ts()}]  Connecting {len(adb_ids)} device(s) in parallel…\n",
                                "dim"))
                    with ThreadPoolExecutor(max_workers=max(1, len(adb_ids))) as pool:
                        futs = [pool.submit(_adb_connect_quiet, a) for a in adb_ids]
                        for f in as_completed(futs):
                            pass

                self.q.put(("vpn_started", adb_ids, names, None))

            except Exception as ex:
                self.q.put(("vpn_started", [], {}, str(ex)))

        threading.Thread(target=_start_worker, daemon=True).start()

    def _vpn_monitor_stop(self):
        self._vpn_stop_event.set()
        try:
            self._vpn_start_btn.configure(state=tk.NORMAL)
            self._vpn_stop_btn.configure(state=tk.DISABLED)
            self._vpn_status_lbl.configure(text="● Stopped", fg=FG_DIM)
        except Exception:
            pass
        self._vpn_write_log(f"[{_ts()}]  Monitoring stopped.\n", "dim")

    def _vpn_build_grid(self, adb_ids: list[str], names: dict[str, str]):
        for w in self._vpn_inner.winfo_children():
            w.destroy()
        self._vpn_device_rows.clear()

        if not adb_ids:
            tk.Label(self._vpn_inner, text="No devices found.",
                     font=FN, bg=BG_PANEL, fg=FG_DIM, pady=20).pack()
            return

        hf = tk.Frame(self._vpn_inner, bg=BG_MID)
        hf.pack(fill=tk.X)
        tk.Label(hf, text=" ",        font=FSB, bg=BG_MID, fg=FG_DIM, width=3
                 ).pack(side=tk.LEFT, padx=(8, 0))
        tk.Label(hf, text="Device",   font=FSB, bg=BG_MID, fg=FG_DIM, width=16, anchor=tk.W
                 ).pack(side=tk.LEFT, padx=4)
        tk.Label(hf, text="ADB ID",   font=FSB, bg=BG_MID, fg=FG_DIM, width=20, anchor=tk.W
                 ).pack(side=tk.LEFT, padx=4)
        tk.Label(hf, text="Last Change", font=FSB, bg=BG_MID, fg=FG_DIM, anchor=tk.W
                 ).pack(side=tk.LEFT, padx=4)

        for i, adb_id in enumerate(adb_ids):
            name   = names.get(adb_id, adb_id)
            bg_row = BG_MID if i % 2 == 0 else BG_PANEL

            rf = tk.Frame(self._vpn_inner, bg=bg_row)
            rf.pack(fill=tk.X)

            dot = tk.Label(rf, text="●", font=(F, 11, "bold"),
                           bg=bg_row, fg=FG_DIM, width=3)
            dot.pack(side=tk.LEFT, padx=(8, 0), pady=5)

            tk.Label(rf, text=name,   font=(F, 8),  bg=bg_row,
                     fg=FG_MAIN, width=16, anchor=tk.W).pack(side=tk.LEFT, padx=4)
            tk.Label(rf, text=adb_id, font=(FM, 8), bg=bg_row,
                     fg=FG_DIM,  width=20, anchor=tk.W).pack(side=tk.LEFT, padx=4)

            last_lbl = tk.Label(rf, text="—", font=(F, 8), bg=bg_row,
                                fg=FG_DIM, anchor=tk.W)
            last_lbl.pack(side=tk.LEFT, padx=4)

            self._vpn_device_rows[adb_id] = {"dot": dot, "last_lbl": last_lbl}

    def _vpn_start_threads(self, adb_ids: list[str], names: dict[str, str]):
        self._vpn_threads.clear()
        for adb_id in adb_ids:
            t = threading.Thread(
                target=self._vpn_device_thread,
                args=(adb_id, names.get(adb_id, adb_id)),
                daemon=True,
            )
            t.start()
            self._vpn_threads.append(t)
        try:
            self._vpn_status_lbl.configure(
                text=f"● Monitoring {len(adb_ids)} device(s)", fg="#5CCC5C")
        except Exception:
            pass

    def _vpn_device_thread(self, adb_id: str, name: str):
        """Poll VPN tun0 every ~1 s for one device."""
        first = True
        while not self._vpn_stop_event.is_set():
            if self.demo:
                import random as _rnd
                ok = _rnd.random() > 0.15
            else:
                ok = _adb_vpn_check(adb_id, timeout=2)
            self.q.put(("vpn_update", adb_id, name, ok, first))
            first = False
            for _ in range(10):          # 10 × 0.1 s = 1 s total, interruptible
                if self._vpn_stop_event.is_set():
                    break
                time.sleep(0.1)

    def _vpn_update_device(self, adb_id: str, name: str, online: bool, first: bool):
        row  = self._vpn_device_rows.get(adb_id)
        prev = self._vpn_last_status.get(adb_id)
        changed = (prev is not None) and (prev != online)

        if row:
            try:
                row["dot"].configure(fg="#5CCC5C" if online else FG_ERR)
                if changed:
                    row["last_lbl"].configure(text=_ts())
            except Exception:
                pass

        if first:
            self._vpn_last_status[adb_id] = online
            return

        if changed:
            self._vpn_last_status[adb_id] = online
            port = adb_id.split(":")[-1]
            if online:
                self._vpn_write_log(
                    f"[{_ts()}]  ● {name} ({port})  came BACK ONLINE\n", "online")
            else:
                self._vpn_write_log(
                    f"[{_ts()}]  ● {name} ({port})  went  OFFLINE\n", "offline")

    def _vpn_write_log(self, msg: str, tag: str = "dim"):
        try:
            self._vpn_log.configure(state=tk.NORMAL)
            self._vpn_log.insert(tk.END, msg, tag)
            self._vpn_log.see(tk.END)
            self._vpn_log.configure(state=tk.DISABLED)
        except Exception:
            pass

    def _vpn_clear_log(self):
        try:
            self._vpn_log.configure(state=tk.NORMAL)
            self._vpn_log.delete("1.0", tk.END)
            self._vpn_log.configure(state=tk.DISABLED)
        except Exception:
            pass

    # ══════════════════════════════════════════════════════════════════════════
    # LOG STRIP
    # ══════════════════════════════════════════════════════════════════════════
    # ── FIX 7: Issues tracker tab ─────────────────────────────────────────────
    def _build_issues_tab(self):
        tab = self._tab_issues
        for w in tab.winfo_children():
            w.destroy()
        tab.rowconfigure(1, weight=1)
        tab.columnconfigure(0, weight=1)

        # ── Header bar ───────────────────────────────────────────────────────
        hdr = tk.Frame(tab, bg=BG_MID)
        hdr.grid(row=0, column=0, sticky="ew")
        tk.Label(hdr, text="⚠  ISSUES", font=FH, bg=BG_MID, fg=PRI,
                 padx=10, pady=8).pack(side=tk.LEFT)
        tk.Label(hdr,
                 text="Live parse of ERROR / WARNING lines from device logs. "
                      "Refresh reads logs without holding file locks.",
                 font=FS, bg=BG_MID, fg=FG_DIM, padx=4).pack(side=tk.LEFT)

        _btn(hdr, "⟳ Refresh", self._issues_refresh,
             bg=BG_CELL, fg=ACC_BLUE, font=FNB, padx=8, pady=4).pack(side=tk.RIGHT, padx=8)
        _btn(hdr, "Clear", self._issues_clear,
             bg=BG_CELL, fg=FG_DIM, font=FS, padx=6, pady=4).pack(side=tk.RIGHT, padx=2)

        # ── Filter row ───────────────────────────────────────────────────────
        frow = tk.Frame(tab, bg=BG_PANEL)
        frow.grid(row=0, column=0, sticky="ew")  # will be row 1 after re-grid
        frow.grid_forget()  # re-add properly below
        frow2 = tk.Frame(tab, bg=BG_PANEL)
        frow2.grid(row=1, column=0, sticky="ew")
        tab.rowconfigure(1, weight=0)
        tab.rowconfigure(2, weight=1)

        tk.Label(frow2, text="Filter:", font=FS, bg=BG_PANEL, fg=FG_DIM,
                 padx=6).pack(side=tk.LEFT)
        self._issues_filter = tk.StringVar()
        tk.Entry(frow2, textvariable=self._issues_filter, font=FMN,
                 bg=BG_CELL, fg=FG_MAIN, insertbackground=FG_MAIN,
                 relief=tk.FLAT, width=20).pack(side=tk.LEFT, padx=4)
        self._issues_filter.trace_add("write", lambda *_: self._issues_apply_filter())

        self._issues_show_warn = tk.BooleanVar(value=True)
        self._issues_show_err  = tk.BooleanVar(value=True)
        tk.Checkbutton(frow2, text="Warnings", variable=self._issues_show_warn,
                       font=FS, bg=BG_PANEL, fg="#F9A825",
                       selectcolor=BG_CELL, activebackground=BG_PANEL,
                       command=self._issues_apply_filter).pack(side=tk.LEFT, padx=4)
        tk.Checkbutton(frow2, text="Errors", variable=self._issues_show_err,
                       font=FS, bg=BG_PANEL, fg=FG_ERR,
                       selectcolor=BG_CELL, activebackground=BG_PANEL,
                       command=self._issues_apply_filter).pack(side=tk.LEFT, padx=2)

        # ── Main treeview ────────────────────────────────────────────────────
        tree_wrap = tk.Frame(tab, bg=BG_PANEL)
        tree_wrap.grid(row=2, column=0, sticky="nsew", padx=6, pady=(0,6))
        tree_wrap.rowconfigure(0, weight=1)
        tree_wrap.columnconfigure(0, weight=1)

        cols = ("time", "device", "level", "message")
        style = self.option_get("style", "") or ""
        tv = ttk.Treeview(tree_wrap, columns=cols, show="headings",
                          style="Sheet.Treeview", selectmode="browse")
        tv.heading("time",    text="Time",    anchor=tk.W)
        tv.heading("device",  text="Device",  anchor=tk.W)
        tv.heading("level",   text="Level",   anchor=tk.W)
        tv.heading("message", text="Message", anchor=tk.W)
        tv.column("time",    width=130, minwidth=100, stretch=False)
        tv.column("device",  width=120, minwidth=80,  stretch=False)
        tv.column("level",   width=70,  minwidth=60,  stretch=False)
        tv.column("message", width=900, minwidth=200, stretch=True)

        tv.tag_configure("err",  foreground=FG_ERR,    background="#1A0808")
        tv.tag_configure("warn", foreground="#F9A825",  background="#1A1500")
        tv.tag_configure("info", foreground=ACC_BLUE,  background=BG_CELL)

        ysb = tk.Scrollbar(tree_wrap, orient=tk.VERTICAL, command=tv.yview,
                           bg=BG_MID, troughcolor=BG_MID)
        xsb = tk.Scrollbar(tree_wrap, orient=tk.HORIZONTAL, command=tv.xview,
                           bg=BG_MID, troughcolor=BG_MID)
        tv.configure(yscrollcommand=ysb.set, xscrollcommand=xsb.set)
        ysb.grid(row=0, column=1, sticky="ns")
        xsb.grid(row=1, column=0, sticky="ew")
        tv.grid(row=0, column=0, sticky="nsew")

        self._issues_tv = tv
        self._issues_all_rows: list[tuple] = []   # (time, device, level, message)

        # Auto-refresh when tab becomes visible
        tv.bind("<Map>", lambda e: self._issues_refresh())

    def _issues_scan_logs(self) -> list[tuple]:
        """
        Read every device log file once (open/close — no persistent lock)
        and return rows matching ERROR or WARNING.
        Never raises — bad files are silently skipped.
        """
        import re as _re, glob as _glob

        rows = []
        # Match lines like: 2026-04-17 09:22:48  WARNING   ── message
        pat = _re.compile(
            r"^(\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2})\s+"
            r"(ERROR|WARNING)\s+(.*)"
        )
        # Also catch explicit failure markers at INFO level
        failure_pat = _re.compile(
            r"^(\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2})\s+INFO\s+"
            r".*?(FAILED|stuck at|Fatal Crash|Exceeded max|screenshot failed twice|"
            r"setup_vpn.*FAILED|setup_target_app.*FAILED|prepare_target_app.*FAILED)"
        )

        log_dir = LOG_DIR
        # Device logs: localhost_XXXX.log
        for fpath in _glob.glob(os.path.join(log_dir, "localhost_*.log")):
            device = os.path.basename(fpath).replace("localhost_", "").replace(".log", "")
            try:
                with open(fpath, "r", encoding="utf-8", errors="replace") as f:
                    for line in f:
                        line = line.rstrip()
                        m = pat.match(line)
                        if m:
                            rows.append((m.group(1), device, m.group(2), m.group(3).strip()))
                            continue
                        m2 = failure_pat.match(line)
                        if m2:
                            msg = line[line.find("INFO")+4:].strip()
                            rows.append((m2.group(1), device, "FAIL", msg))
            except Exception:
                pass  # FIX 5: never crash on missing/locked file

        # Controller multi log
        for fpath in [os.path.join(log_dir, "controller_multi.log"),
                      os.path.join(log_dir, "controller_ui.log")]:
            try:
                with open(fpath, "r", encoding="utf-8", errors="replace") as f:
                    for line in f:
                        line = line.rstrip()
                        m = pat.match(line)
                        if m:
                            rows.append((m.group(1), "controller", m.group(2), m.group(3).strip()))
            except Exception:
                pass

        # Sort by time desc (most recent first)
        rows.sort(key=lambda r: r[0], reverse=True)
        return rows

    def _issues_refresh(self):
        def worker():
            rows = self._issues_scan_logs()
            self.q.put(("issues_loaded", rows))
        threading.Thread(target=worker, daemon=True).start()

    def _issues_loaded(self, rows: list[tuple]):
        self._issues_all_rows = rows
        self._issues_apply_filter()

    def _issues_apply_filter(self):
        try:
            tv = self._issues_tv
        except AttributeError:
            return
        show_warn = self._issues_show_warn.get()
        show_err  = self._issues_show_err.get()
        ftext     = self._issues_filter.get().strip().lower()

        tv.delete(*tv.get_children())
        count = 0
        for (ts, dev, level, msg) in self._issues_all_rows:
            if level == "WARNING" and not show_warn:
                continue
            if level in ("ERROR", "FAIL") and not show_err:
                continue
            if ftext and ftext not in dev.lower() and ftext not in msg.lower():
                continue
            tag = "err" if level in ("ERROR", "FAIL") else "warn"
            tv.insert("", tk.END, values=(ts, dev, level, msg), tags=(tag,))
            count += 1
            if count >= 2000:   # cap to avoid sluggish UI with huge logs
                break

    def _issues_clear(self):
        try:
            self._issues_all_rows = []
            self._issues_tv.delete(*self._issues_tv.get_children())
        except Exception:
            pass

    def _build_log_strip(self):
        wrap = tk.Frame(self, bg="#0A0A14")
        wrap.grid(row=2, column=0, sticky="ew")
        hdr = tk.Frame(wrap, bg="#111120")
        hdr.pack(fill=tk.X)
        tk.Label(hdr, text="LOG", font=(F, 8, "bold"), bg="#111120", fg=FG_DIM, padx=10, pady=4).pack(side=tk.LEFT)
        tk.Button(hdr, text="clear", command=self._clear_log, bg="#111120", fg=FG_DIM, font=(F, 7),
                  relief=tk.FLAT, padx=6, pady=2, bd=0, cursor="hand2", activebackground=BG_MID).pack(side=tk.RIGHT, padx=6)

        self._log_txt = scrolledtext.ScrolledText(wrap, height=5, font=(FM, 8),
                                                   bg="#0A0A14", fg=FG_MAIN,
                                                   state=tk.DISABLED, wrap=tk.WORD,
                                                   relief=tk.FLAT, padx=10, pady=6)
        self._log_txt.pack(fill=tk.X)
        for tag, fg in [("ok", "#5CCC5C"), ("warn", "#F9A825"), ("err", FG_ERR), ("dim", FG_DIM), ("info", ACC_BLUE)]:
            self._log_txt.tag_config(tag, foreground=fg)

    # ══════════════════════════════════════════════════════════════════════════
    # MOUSEWHEEL + SHORTCUTS
    # ══════════════════════════════════════════════════════════════════════════
    def _setup_mousewheel(self):
        def _scroll(event):
            delta = 0
            if event.delta:
                delta = int(-1 * (event.delta / 120))
            elif event.num == 4:
                delta = -1
            elif event.num == 5:
                delta = 1
            if delta == 0:
                return
            w = event.widget
            while w:
                if isinstance(w, tk.Canvas):
                    w.yview_scroll(delta, "units")
                    return
                try:
                    w = w.master
                except Exception:
                    break
        self.bind_all("<MouseWheel>", _scroll)
        self.bind_all("<Button-4>",   _scroll)
        self.bind_all("<Button-5>",   _scroll)

    def _setup_shortcuts(self):
        self.bind_all("<F5>",            lambda e: self._reload_devices())
        self.bind_all("<Control-r>",     lambda e: self._run_start_selected())
        self.bind_all("<Escape>",        lambda e: self._run_stop_all())
        # Screenshotor: S / s triggers a screenshot batch when the controller
        # (or mini window) is focused.  Guarded so it never fires while typing.
        self.bind_all("<KeyPress-s>",    self._ss_hotkey_screenshot)
        self.bind_all("<KeyPress-S>",    self._ss_hotkey_screenshot)

    # ══════════════════════════════════════════════════════════════════════════
    # HOT RELOAD
    # ══════════════════════════════════════════════════════════════════════════
    def _reload_code(self):
        def worker():
            try:
                self.bridge.reload_code()
                self.q.put(("log", "✓ Bot code reloaded", "ok"))
            except Exception as ex:
                self.q.put(("log", f"Code reload error: {ex}", "err"))
        threading.Thread(target=worker, daemon=True).start()

    def _reload_sheet(self):
        def worker():
            try:
                # J/S13: flush dirty controller cache before reading Sheets.
                self._prepare_for_sheet_read("reload_sheet")
                self.bridge.refresh_sheet(force=True)
                self._post_sheet_read_rebuild()
                for dev in self.active_devices:
                    dev["statuses"] = self.bridge.status_snapshot(dev["adb_id"])
                self.q.put(("sheet_redraw", None))
                self.q.put(("log", "✓ Sheet reloaded", "ok"))
            except Exception as ex:
                self.q.put(("log", f"Sheet reload error: {ex}", "err"))
        threading.Thread(target=worker, daemon=True).start()

    def _reload_devices(self):
        self._log("Scanning devices…", "dim")
        def worker():
            try:
                if self.demo:
                    devs = DEMO_CONF
                else:
                    # J/S13: flush dirty controller cache before reading Sheets.
                    self._prepare_for_sheet_read("reload_devices")
                    self.bridge.refresh_sheet()
                    self._post_sheet_read_rebuild()
                    devs = self.bridge.list_conf_devices()
                self.q.put(("conf_loaded", devs))
            except Exception as ex:
                self.q.put(("log", f"Device scan error: {ex}", "err"))
        threading.Thread(target=worker, daemon=True).start()

    def _connect_devices(self, chosen):
        """Connect devices and set them as active."""
        def worker():
            try:
                if self.demo:
                    time.sleep(0.5)
                    alive = [d for d in DEMO_ACTIVE if d["adb_id"] in chosen]
                else:
                    alive = self.bridge.connect_selected(chosen, log_fn=lambda m, t: self.q.put(("log", m, t)))
                self.q.put(("devices_connected", alive))
            except Exception as ex:
                self.q.put(("log", f"Connect error: {ex}", "err"))
        threading.Thread(target=worker, daemon=True).start()

    # ══════════════════════════════════════════════════════════════════════════
    # DAILY RESET
    # ══════════════════════════════════════════════════════════════════════════
    def _tick_reset_countdown(self):
        import datetime as _dt
        now    = _dt.datetime.now()
        cutoff = now.replace(hour=13, minute=30, second=0, microsecond=0)
        if now >= cutoff:
            cutoff += _dt.timedelta(days=1)
        delta   = cutoff - now
        total_s = int(delta.total_seconds())
        h, rem  = divmod(total_s, 3600)
        m, _    = divmod(rem, 60)
        if h > 0:
            self._reset_var.set(f"⏱ reset in {h}h {m:02d}m")
        else:
            self._reset_var.set(f"⏱ reset in {m}m")
        self._reset_lbl.configure(fg=ACC_YEL if m < 5 and h == 0 else FG_DIM)

        # G: Auto-shutdown at 1:30 PM is DISABLED.
        # The controller stays open indefinitely.  Daily reset can be applied
        # manually via the Reload Sheet button or at next startup.
        self.after(30_000, self._tick_reset_countdown)

    def _do_daily_reset_safe(self):
        """
        K: Safe daily reset — stops devices if running, drains queues, applies the
        reset, then clears/rebuilds the controller cache exactly like startup, and
        keeps the controller UI open.  Auto-close has been removed (see P).
        """
        # 0. Block queue pump — no new devices during reset
        self._shutdown_pending = True
        # The session is being abandoned; a pending ADB retry must not survive
        # the reset and re-queue its device into whatever comes next.
        self._run_session_active = False
        # WHO the Run owns, captured before any of it is mutated.
        _snap = self._human_snapshot_abandoned_run()
        try:
            # Deliberately NOT _human_finalize_pending_retries: it finalizes
            # with a generic "stopped", which latches the context and makes the
            # route-specific result below unreachable. This route owns its own
            # categories now.
            self._cancel_run_retries(reason="safe reset")
            self._cancel_hard_internet_emergency(reason="safe reset")
            self._cancel_internet_pause(reason="safe reset")
        except Exception:
            pass
        # Phase 1 — queued and retry-only. No live worker is still writing to
        # their raw logs, and they must be finalized before _run_queue and the
        # retry dict are emptied or they vanish from human logging entirely.
        self._human_finalize_abandoned_nonrunning(
            _snap, "stopped_by_safe_reset", note=NOTE_SAFE_RESET,
            close_disposition="not_requested_safe_reset")
        discarded = list(self._run_queue)
        self._run_queue.clear()
        if discarded:
            _multi_log.info(
                f"[RESET-SAFE] discarded {len(discarded)} queued device(s): {discarded}"
            )

        # 1. Signal every running process to stop; drain BEFORE kill
        for adb_id in list(self._running_devs.keys()):
            info = self._running_devs.get(adb_id)
            if info:
                ev = info.get("stop_event")
                if ev:
                    ev.set()
                mp_q = info.get("mp_q")
                if mp_q is not None:
                    self._drain_worker_queue(
                        adb_id, mp_q, reason="reset:pre-kill",
                        session_id=info.get("session_id"),
                        launch_token=info.get("launch_token"))
        self._drain_controller_queue_cache_messages(reason="reset:pre-kill")

        # 2. Wait up to 30s for subprocesses to finish
        deadline = time.time() + 30.0
        while time.time() < deadline:
            procs_alive = [
                info["process"]
                for info in self._running_devs.values()
                if info.get("process") and info["process"].is_alive()
            ]
            if not procs_alive:
                break
            time.sleep(1.0)

        # 3. Force-kill any stragglers
        for info in list(self._running_devs.values()):
            proc = info.get("process")
            if proc and proc.is_alive():
                try:
                    proc.terminate()
                    proc.join(timeout=3)
                except Exception:
                    pass
                if proc.is_alive():
                    try:
                        proc.kill()
                    except Exception:
                        pass

        # 3b. Drain AFTER kill, mark affected devices STOPPED, clear _running_devs
        for adb_id in list(self._running_devs.keys()):
            info = self._running_devs.get(adb_id)
            if info:
                mp_q = info.get("mp_q")
                if mp_q is not None:
                    self._drain_worker_queue(
                        adb_id, mp_q, reason="reset:post-kill",
                        session_id=info.get("session_id"),
                        launch_token=info.get("launch_token"))
            try:
                self._run_set_badge(adb_id, "STOPPED", BADGE_STOPPED[0], BADGE_STOPPED[1])
            except Exception:
                pass
        self._drain_controller_queue_cache_messages(reason="reset:post-kill")
        # Phase 2 — the devices that had a LIVE worker. ONLY NOW: finalizing
        # earlier would freeze raw_end_offset before a gracefully-stopping
        # worker wrote its `recording stopped —`, final counters and
        # [WORKER-END]. Those records exist and belong in the report; a
        # force-killed worker's absence of them is reported just as truthfully.
        self._human_finalize_abandoned_running(
            _snap, "stopped_by_safe_reset", note=NOTE_SAFE_RESET,
            close_disposition="not_requested_safe_reset")
        self._running_devs.clear()

        # 4. Apply daily reset, then clear/rebuild cache exactly like startup.
        try:
            did_reset = self.bridge.run_daily_reset()
            if did_reset:
                # K: wipe stale cache, persist cleared, rebuild from fresh sheet.
                with self._status_cache_lock:
                    self._status_cache = {}
                    self._pending_sheet_status = {}
                    self._cache_dirty = False
                self._persist_status_cache()
                self._rebuild_status_cache_from_sheet()
                self.q.put(("log", "✓ Daily reset applied — cache cleared + rebuilt from fresh sheet", "ok"))
            else:
                # K: no reset — rebuild from sheet and overlay any pending writes.
                self._rebuild_status_cache_from_sheet()
                self._apply_pending_sheet_status_to_local_cache()
                self.q.put(("log", "Daily reset checked — no reset needed (cache rebuilt + overlaid)", "dim"))
        except Exception as ex:
            self.q.put(("log", f"Daily reset error: {ex}", "err"))

        # 5. Redraw UI, keep UI open and allow new runs
        self.q.put(("sheet_redraw", None))
        self._shutdown_pending = False
        # The reset has COMPLETED — every worker is gone, so the fatal latch and
        # any surviving launch expectations belong to a run that no longer
        # exists. Cleared here rather than at the top of the reset, so nothing
        # is unlatched while the fatal session is still being stopped.
        self._fatal_run_stop = False
        self._run_expected_launch.clear()
        self._run_recent_completion.clear()
        self._run_recent_recording_identity.clear()
        # The reset abandoned the session; re-enable RUN SELECTED and apply any
        # panel refresh it deferred.
        try:
            self._cancel_hard_internet_emergency(reason="safe reset complete")
            self._finish_run_session_if_idle()
        except Exception:
            pass
        self.q.put(("log", "✓ Reset complete — controller remains open", "ok"))

    # Keep old name as alias so any external references don't break
    def _do_reset_shutdown(self):
        """Deprecated alias — calls _do_daily_reset_safe (no longer closes the app)."""
        self._do_daily_reset_safe()

    # ══════════════════════════════════════════════════════════════════════════
    # HELPERS
    # ══════════════════════════════════════════════════════════════════════════
    def _set_status(self, text, color=FG_DIM):
        self._global_status.configure(text=text, fg=color)

    def _log(self, msg, tag="info"):
        self._write_log(f"[{_ts()}]  {msg}\n", tag)

    def _write_log(self, msg, tag="info"):
        _ui_log.log(_TAG_LVL.get(tag, logging.DEBUG), msg.rstrip())
        try:
            if not hasattr(self, "_log_txt"):
                return  # UI not built yet — silently drop log to screen
            self._log_txt.configure(state=tk.NORMAL)
            self._log_txt.insert(tk.END, msg, tag)
            self._log_txt.see(tk.END)
            self._log_txt.configure(state=tk.DISABLED)
        except Exception:
            pass

    def _clear_log(self):
        self._log_txt.configure(state=tk.NORMAL)
        self._log_txt.delete("1.0", tk.END)
        self._log_txt.configure(state=tk.DISABLED)

    # ══════════════════════════════════════════════════════════════════════════
    # EXIT HANDLER (Feature 7)
    # ══════════════════════════════════════════════════════════════════════════
    # ── FIX 3: session state persistence ─────────────────────────────────────
    def _collect_state(self) -> dict:
        """Snapshot current UI selections into a serialisable dict."""
        # Task config per device type
        tc = {}
        for dt, keys in self.task_config.items():
            # Copy, so a saved snapshot can never alias the live list — the same
            # rule the Multi-Test selections already follow.
            tc[dt] = list(keys)

        # Multi-panel per-device task selections.
        #
        # Serialised from the CANONICAL model, not from _multi_rows: rows only
        # exist for devices in the current scan, so saving from them silently
        # dropped every offline or unrendered device's selection — and left its
        # invalid_multi_tasks provenance pointing at nothing.
        #
        # Rendered rows are folded back in first as a consistency step, in case
        # anything wrote a widget without going through the model.
        for adb_id, row in self._multi_rows.items():
            ref = row.get("tasks_ref")
            if ref is not None:
                self._multi_task_selections[adb_id] = list(ref.get("keys", []))
        multi_tasks = {adb_id: list(keys)
                       for adb_id, keys in self._multi_task_selections.items()}

        # Run-panel checkbox state.
        #
        # Serialised from the CANONICAL model for the same reason as the
        # Multi-Test selections: BooleanVars exist only for rendered rows, so
        # saving from them dropped every unrendered device's tick — and a
        # rebuild that recreated the vars unticked wrote that loss to disk.
        # Rendered vars are folded back in first as a consistency step.
        for adb_id, var in self._run_checks.items():
            try:
                self._run_check_selections[adb_id] = bool(var.get())
            except Exception:
                pass
        # A copy: a caller mutating the returned snapshot must not reach the
        # live model. False values and unrendered keys are both preserved.
        run_checks = dict(self._run_check_selections)

        return {
            "skip_before":     self.skip_var.get(),
            "retry_enabled":   self.retry_var.get(),
            "record_video":    self._record_video.get(),
            "max_concurrent":  self._max_concurrent.get(),
            "task_config":     tc,
            "multi_tasks":     multi_tasks,
            "run_checks":      run_checks,
            # Provenance for selections that had entries but validated to
            # nothing. Without persisting these, an invalid config loads as [],
            # autosaves as [], and on the NEXT start is indistinguishable from a
            # deliberately empty one — so the device quietly becomes a
            # setup-only run. Plain lists of strings: JSON-safe.
            "invalid_task_config": {k: list(v) for k, v
                                    in self._invalid_task_config.items() if v},
            "invalid_multi_tasks": {k: list(v) for k, v
                                    in self._invalid_multi_tasks.items() if v},
        }

    def _save_state(self):
        self._state_mgr.save(self._collect_state())

    def _load_state(self):
        """Restore selections from the most recently saved state file."""
        state = self._state_mgr.load()
        if not state:
            self._log("No saved state found.", "warn")
            return

        self._apply_state_snapshot(state, source="autosave:")

        self._log("✓ Previous state restored.", "ok")

    def _on_close(self):
        # H: 1. Set shutdown flag and stop VPN monitor threads
        self._shutdown_pending = True
        self._vpn_stop_event.set()
        # Cancel pending ADB retries before the Tk loop goes away — a callback
        # that fires during teardown touches widgets that no longer exist.
        self._run_session_active = False
        self._run_expected_launch.clear()
        self._run_recent_completion.clear()
        self._run_recent_recording_identity.clear()
        # WHO the Run owns, captured before any of it is mutated.
        _snap = self._human_snapshot_abandoned_run()
        try:
            # Deliberately NOT _human_finalize_pending_retries: its generic
            # "stopped" would latch these contexts before this route can
            # classify them.
            self._cancel_run_retries(reason="controller close")
            self._cancel_hard_internet_emergency(reason="controller close")
            self._cancel_internet_pause(reason="controller close")
        except Exception:
            pass

        # Phase 1 — queued and retry-only, before the queue is emptied.
        self._human_finalize_abandoned_nonrunning(
            _snap, "stopped_by_controller_close", note=NOTE_CONTROLLER_CLOSE,
            close_disposition="not_requested_controller_close")
        # H: 2. Clear run queue so nothing new launches during shutdown
        self._run_queue.clear()

        # H: 3a. Signal all running processes/threads to stop
        for adb_id, info in list(self._running_devs.items()):
            ev = info.get("stop_event")
            if ev:
                ev.set()
        for adb_id, row in self._multi_rows.items():
            ev = row.get("stop_event")
            if ev:
                ev.set()

        # H: 3b. Drain BEFORE kill — worker mp_q + controller self.q cache messages
        for adb_id, info in list(self._running_devs.items()):
            mp_q = info.get("mp_q")
            if mp_q is not None:
                self._drain_worker_queue(
                    adb_id, mp_q, reason="close:pre-kill",
                    session_id=info.get("session_id"),
                    launch_token=info.get("launch_token"))
        self._drain_controller_queue_cache_messages(reason="close:pre-kill")

        # 4. Wait up to 15 seconds for processes to finish gracefully
        deadline = time.time() + 15.0
        for info in self._running_devs.values():
            proc = info.get("process")
            if proc and proc.is_alive():
                remaining = max(0.1, deadline - time.time())
                proc.join(timeout=remaining)

        # 5. Force-terminate anything still alive, then kill if needed
        for info in self._running_devs.values():
            proc = info.get("process")
            if proc and proc.is_alive():
                try:
                    proc.terminate()
                    proc.join(timeout=3)
                except Exception:
                    pass
            if proc and proc.is_alive():
                try:
                    proc.kill()
                except Exception:
                    pass

        # H: 6. Drain AFTER kill — catch last messages emitted before death
        for adb_id, info in list(self._running_devs.items()):
            mp_q = info.get("mp_q")
            if mp_q is not None:
                self._drain_worker_queue(
                    adb_id, mp_q, reason="close:post-kill",
                    session_id=info.get("session_id"),
                    launch_token=info.get("launch_token"))
        self._drain_controller_queue_cache_messages(reason="close:post-kill")

        # H: 7. Final cache→sheet sync on close
        if not self.demo:
            try:
                _multi_log.info("[SYNC] _on_close ── final cache→sheet sync")
                self._flush_pending_sheet_status()
                _multi_log.info("[SYNC] _on_close ── final sync done ✓")
            except Exception as _fe:
                _multi_log.error(f"[SYNC] _on_close ── final sync failed: {_fe}")

        # H: 8. Persist default autosave state on exit
        try:
            self._save_state()
        except Exception:
            pass
        # H: Note — emulator windows are intentionally NOT closed here; controller
        # close policy leaves emulator windows open (same as Stop All).
        # If user kills Python from Task Manager, none of this cleanup runs.
        _multi_log.info(
            "[CLOSE] workers stopped; emulator windows left open by controller-close policy"
        )
        # Every device still live when the user closed the window is terminal
        # now. Controller close leaves emulator windows open, exactly like
        # Stop All, so that is the disposition its reports carry.
        # Phase 2 — live workers, only after the post-kill drain, so a worker
        # that shut down gracefully has its final records inside the slice.
        self._human_finalize_abandoned_running(
            _snap, "stopped_by_controller_close", note=NOTE_CONTROLLER_CLOSE,
            close_disposition="not_requested_controller_close")
        # The writer is a DAEMON thread: queueing a report and calling destroy()
        # would race interpreter shutdown and lose it. Wait — boundedly — for
        # what is already queued, then continue regardless.
        self._human_flush_jobs(timeout=8.0)
        self.destroy()

    # ══════════════════════════════════════════════════════════════════════════
    # QUEUE POLL
    # ══════════════════════════════════════════════════════════════════════════
    def _poll(self):
        try:
            for _ in range(200):  # drain up to 200 messages per tick
                item = self.q.get_nowait()
                kind = item[0]

                if kind == "log":
                    _, msg, tag = item
                    try:
                        self._write_log(f"[{_ts()}]  {msg}\n", tag)
                    except Exception:
                        pass

                elif kind == "loading_msg":
                    try:
                        self._loading_status.configure(text=item[1])
                    except Exception:
                        pass

                elif kind == "startup_done":
                    _, devs, error = item
                    try:
                        self._loading_frame.destroy()
                    except Exception:
                        pass
                    self._build()
                    self._setup_mousewheel()
                    self._setup_shortcuts()
                    self._tick_reset_countdown()
                    self.conf_devices = devs
                    # Do NOT auto-connect — just populate UI from conf.
                    # Devices connect on-demand when the user starts them.
                    self._on_startup_done(devs, error)

                elif kind == "conf_loaded":
                    devs = item[1]
                    self.conf_devices = devs
                    self._discover_task_config(devs)
                    self._render_run_device_list()
                    self._build_task_config_tab()
                    self._log(f"Found {len(devs)} instance(s)", "ok")

                elif kind == "devices_connected":
                    self.active_devices = item[1]
                    n = len(self.active_devices)
                    self._set_status(f"● {n} connected", ACC_GRN)
                    self._refresh_single_lb()
                    self._render_run_device_list()
                    self._render_test_multi_panel()
                    self._log(f"✓ {n} device(s) active", "ok")

                elif kind == "test_scan_done":
                    _, devs = item
                    # A scan reports STATUS. It never decides which devices the
                    # Run tab offers — that is always the configured list, because
                    # device_worker opens and connects whatever you selected.
                    self._test_devices = devs
                    self.active_devices = devs           # Test tab / Screenshotor
                    self._online_adb_ids = {d["adb_id"] for d in devs if d.get("adb_id")}
                    self._refresh_single_lb()
                    self._render_test_multi_panel()
                    self._refresh_run_online_badges()    # badges only, list unchanged
                    n = len(devs)
                    if n:
                        self._log(f"⟳ Scan: {n} device(s) currently open", "ok")
                    else:
                        self._log("⟳ Scan: no devices currently open — configured "
                                  "devices are still selectable and will be "
                                  "launched on Run", "warn")
                    try:
                        self._test_scan_btn.configure(state=tk.NORMAL, text="⟳ Scan")
                        self._test_full_scan_btn.configure(state=tk.NORMAL)
                    except Exception:
                        pass

                elif kind == "test_log":
                    _, msg, tag = item
                    try:
                        self._test_log.configure(state=tk.NORMAL)
                        self._test_log.insert(tk.END, f"[{_ts()}]  {msg}\n", tag)
                        self._test_log.see(tk.END)
                        self._test_log.configure(state=tk.DISABLED)
                    except Exception:
                        pass

                elif kind == "single_done":
                    _, adb_id, task_keys, ok, result = item
                    tag = "ok" if ok else ("warn" if result == "stopped" else "err")
                    self._log(f"{'✓' if ok else '✗'} {adb_id} → {result}", tag)
                    self._set_status("● IDLE", FG_DIM)
                    try:
                        self._test_run_btn.configure(state=tk.NORMAL)
                        self._test_stop_btn.configure(state=tk.DISABLED)
                    except Exception:
                        pass
                    if ok:
                        for dev in self.active_devices:
                            if dev["adb_id"] == adb_id:
                                for k in task_keys:
                                    dev.setdefault("statuses", {})[k] = "done"

                elif kind == "multi_log":
                    _, adb_id, msg = item
                    # Model first, so the line survives a rebuild.
                    self._multi_display(adb_id)["log"] = msg[:60]
                    row = self._multi_rows.get(adb_id)
                    if row:
                        try:
                            row["log_var"].set(msg[:60])
                        except Exception:
                            pass

                elif kind == "multi_done":
                    _, adb_id, ok, result = item
                    if ok:
                        self._multi_set_badge(adb_id, "DONE ✓", BADGE_DONE[0], BADGE_DONE[1])
                        threading.Thread(target=_beep, daemon=True).start()
                    elif result == "stopped":
                        self._multi_set_badge(adb_id, "STOPPED", BADGE_STOPPED[0], BADGE_STOPPED[1])
                    elif result == "no_runnable_tasks":
                        # _multi_start_one already set the correct badge and
                        # never started anything; overwriting it with FAILED ✗
                        # (and beeping) reported a failure that never occurred.
                        self._multi_set_badge(
                            adb_id,
                            "INVALID TASKS" if self._invalid_multi_tasks.get(adb_id)
                            else "NO TASKS",
                            BADGE_IDLE[0], BADGE_IDLE[1])
                    else:
                        self._multi_set_badge(adb_id, "FAILED ✗", BADGE_FAILED[0], BADGE_FAILED[1])
                    row = self._multi_rows.get(adb_id)
                    if row:
                        try:
                            row["start_btn"].configure(state=tk.NORMAL)
                            row["stop_btn"].configure(state=tk.DISABLED)
                        except Exception:
                            pass
                    # A scan that arrived mid-run deferred its panel refresh so
                    # this worker's stop handles survived. Now that the last one
                    # is done, apply it.
                    # The worker is still is_alive() for a few instructions
                    # after queueing this message, so a single check here loses
                    # the race and the refresh stays pending forever. Poll.
                    if self._multi_panel_refresh_pending:
                        self._schedule_pending_multi_refresh()

                elif kind == "run_log":
                    _, adb_id, msg, tag = item
                    self._run_log_msg(f"[{adb_id.split(':')[-1]}] {msg}", tag)
                    # Model first: a message that arrives while the row is absent
                    # (offline device, or a rebuild in flight) is still recorded
                    # and appears when the row is next rendered.
                    if adb_id:
                        self._run_set_log(adb_id, msg)

                elif kind == "run_task_done":
                    _, adb_id, task_key = item
                    # Update UI active_devices tracker
                    for dev in self.active_devices:
                        if dev["adb_id"] == adb_id:
                            dev.setdefault("statuses", {})[task_key] = "done"
                    # Update controller's in-memory bot status dict
                    try:
                        td = TASK_DEFS.get(task_key, {})
                        attr = td.get("status_attr")
                        if attr and self.bridge.bot:
                            status_dict = getattr(self.bridge.bot, attr, None)
                            if isinstance(status_dict, dict):
                                status_dict[adb_id] = "done"
                    except Exception:
                        pass
                    # Persist to local status cache immediately
                    self._record_task_done(adb_id, task_key, "done")
                    # D: no immediate per-task flush — _schedule_sheet_sync handles batching

                elif kind == "run_task_skipped":
                    # J: task was already done — log only, no dirty cache write
                    _, adb_id, task_key = item
                    _multi_log.info(
                        f"[CACHE] {adb_id} task_skipped {task_key!r} — "
                        f"already done, not marking as newly completed"
                    )

                elif kind == "run_status_update":
                    # D: worker's monkey-patched update_status sent this immediately.
                    # Store raw header/value in pending_sheet_status (for all non-null headers).
                    # Also update status_cache by task_key where mapping exists.
                    _, adb_id, header, value = item
                    if not header:
                        _multi_log.debug(
                            f"[CACHE] run_status_update {adb_id} null header "
                            f"value={value!r} — cache not updated (no column to write)"
                        )
                    else:
                        # Map header → task_key (TASK_DEFS headers first, then
                        # the raw-header fallback for header=None tasks; that
                        # map is empty until a live task needs one)
                        _h2t = {v["header"]: k for k, v in TASK_DEFS.items()
                                if v.get("header")}
                        task_key = _h2t.get(header) or RAW_STATUS_HEADER_TO_TASK.get(header)
                        with self._status_cache_lock:
                            # Always store raw header/value for sheet sync
                            self._pending_sheet_status.setdefault(adb_id, {})[header] = value
                            # Also store by task_key in status_cache if known
                            if task_key:
                                self._status_cache.setdefault(adb_id, {})[task_key] = value
                        self._cache_dirty = True
                        # 5: Persist to disk so raw updates survive a force-kill
                        self._persist_status_cache()
                        # Fix 3: write back into rows_by_device so status_snapshot()
                        # returns the live value without needing a Sheets read.
                        row_field = RAW_STATUS_HEADER_TO_ROW_FIELD.get(header)
                        if row_field:
                            try:
                                row = self.bridge._lookup_row(adb_id)
                                if row:
                                    row[row_field] = value
                            except Exception:
                                pass
                        _multi_log.debug(
                            f"[CACHE] run_status_update {adb_id} "
                            f"header={header!r} value={value!r} "
                            f"task_key={task_key!r} → dirty + persisted"
                        )

                elif kind == "recording_done":
                    adb_id = item[1] if len(item) > 1 else ""
                    info   = item[2] if len(item) > 2 else {}
                    _rec_sid = item[3] if len(item) > 3 else None
                    _rec_tok = item[4] if len(item) > 4 else None
                    # Its own rule: recording_done legitimately arrives AFTER
                    # run_done (the grace drain is often the only thing that
                    # sees the folder/report paths), so the expectation is
                    # already consumed. Accept the expected launch OR the exact
                    # completion just accepted — nothing else.
                    if not self._recording_identity_matches(adb_id, _rec_sid,
                                                            _rec_tok):
                        continue
                    self._on_recording_done(adb_id, info)

                elif kind == "host_internet_pause":
                    dev = item[1] if len(item) > 1 else None
                    _p_sid = item[2] if len(item) > 2 else None
                    _p_tok = item[3] if len(item) > 3 else None
                    # Pausing halts the entire queue, so a dead attempt must not
                    # be able to trigger it.
                    if not self._run_control_identity_matches(
                            dev, _p_sid, _p_tok, what="host_internet_pause"):
                        continue
                    self._enter_internet_pause(dev)

                elif kind == "host_internet_back":
                    dev = item[1] if len(item) > 1 else None
                    _b_sid = item[2] if len(item) > 2 else None
                    _b_tok = item[3] if len(item) > 3 else None
                    if not self._run_control_identity_matches(
                            dev, _b_sid, _b_tok, what="host_internet_back"):
                        continue
                    _multi_log.info(f"[INTERNET-PAUSE] device {dev} reports host internet back")

                elif kind == "host_internet_resume":
                    # No launch identity — this comes from the controller's own
                    # poll thread, not a worker — but it DOES carry the pause it
                    # was started for. A resume from a superseded or cancelled
                    # pause must not release workers a newer pause is holding.
                    _pr_sid = item[1] if len(item) > 1 else None
                    _pr_tok = item[2] if len(item) > 2 else None
                    _pr_own = getattr(self, "_internet_pause_owner", None)
                    if _pr_own is None:
                        _multi_log.warning(
                            f"[INTERNET-PAUSE] stale resume (session={_pr_sid} "
                            f"token={_pr_tok}) ignored — no pause is active")
                        continue
                    if _pr_sid is None or _pr_tok is None:
                        _multi_log.warning(
                            "[INTERNET-PAUSE] identity-less resume discarded — "
                            "it cannot be attributed to a pause")
                        continue
                    if (_pr_own.get("session_id") != _pr_sid
                            or _pr_own.get("token") != _pr_tok):
                        _multi_log.warning(
                            f"[INTERNET-PAUSE] stale resume (session={_pr_sid} "
                            f"token={_pr_tok}) is not the current pause owner "
                            f"{_pr_own} — ignored entirely")
                        continue
                    self._exit_internet_pause()

                elif kind == "internet_down_emergency":
                    # Legacy queue message — routed to the pause tier.  The old
                    # kill-and-close handler is still available via
                    # _handle_internet_down_emergency() for manual Stop,
                    # shutdown, and user-requested hard reset.
                    dev = item[1] if len(item) > 1 else None
                    _e_sid = item[2] if len(item) > 2 else None
                    _e_tok = item[3] if len(item) > 3 else None
                    if not self._run_control_identity_matches(
                            dev, _e_sid, _e_tok, what="internet_down_emergency"):
                        continue
                    _multi_log.warning(
                        f"[INTERNET-PAUSE] legacy internet_down_emergency for {dev} "
                        f"— handling as pause"
                    )
                    self._enter_internet_pause(dev)

                elif kind == "internet_restored_restart":
                    # Internet came back — restart unfinished devices from the
                    # CURRENT RUN only (not every device in active_devices).
                    #
                    # ── Does this restore still belong to the live session? ──
                    # The wait thread can be minutes old. In between, the
                    # operator may have pressed Stop All, the controller may
                    # have started an entirely different run, or shutdown may
                    # have begun. Verify BEFORE touching the queue or any run
                    # metadata: a resurrected old run is worse than no restart.
                    _restore_sid = item[1] if len(item) > 1 else None
                    _restore_tok = item[2] if len(item) > 2 else None
                    _cur_sid = getattr(self, "_run_session_id", 0)
                    _owner = getattr(self, "_internet_emergency_owner", None)
                    _stale = None
                    if _restore_sid is not None and _restore_sid != _cur_sid:
                        _stale = (f"owned by session {_restore_sid}, "
                                  f"current is {_cur_sid}")
                    elif _owner is None:
                        _stale = "the emergency was already cancelled"
                    elif _restore_tok is not None and _owner.get("token") != _restore_tok:
                        _stale = (f"token {_restore_tok} is not the current owner "
                                  f"token {_owner.get('token')}")
                    elif _owner.get("session_id") != _cur_sid:
                        _stale = (f"owner session {_owner.get('session_id')} is not "
                                  f"the current session {_cur_sid}")
                    elif not getattr(self, "_run_session_active", False):
                        _stale = "the run session is no longer active"
                    elif getattr(self, "_shutdown_pending", False):
                        _stale = "shutdown/stop is pending"
                    if _stale is not None:
                        # TOTAL no-op. Clearing _internet_killed_ids /
                        # _internet_restart_ids here used to wipe a NEWER
                        # emergency's restart set, so its restore found nothing
                        # to restart and silently dropped every device.
                        _multi_log.warning(
                            f"[INTERNET] stale/cancelled emergency restore ignored "
                            f"(session={_restore_sid} token={_restore_tok}) — "
                            f"{_stale}; no state touched")
                        continue

                    # Ownership proven. Only now may controller state change —
                    # the wait thread no longer does any of this itself, and
                    # this is the first point at which announcing a restart is
                    # truthful.
                    self._run_log_msg(
                        "[INTERNET] Internet returned — restarting unfinished "
                        "devices", "ok")
                    self._internet_down_emergency = False
                    self._internet_emergency_owner = None
                    try:
                        self._flush_pending_sheet_status()
                    except Exception as _fe0:
                        _multi_log.warning(f"[INTERNET] restore pre-flush failed: {_fe0}")
                    _multi_log.info(
                        f"[INTERNET] internet_restored_restart (session {_cur_sid} "
                        f"token={_restore_tok}): re-queuing unfinished devices")

                    # I/S8: flush dirty controller cache BEFORE reading Sheets so
                    # the sheet read does not clobber unsynced done-values.
                    self._drain_controller_queue_cache_messages(reason="internet_restore")
                    if self._cache_dirty or self._pending_sheet_status:
                        try:
                            _multi_log.info("[INTERNET] flushing dirty cache before sheet read")
                            self._flush_pending_sheet_status()
                        except Exception as _fe:
                            _multi_log.warning(f"[INTERNET] pre-read flush failed: {_fe}")
                    # Then refresh sheet and rebuild controller cache from it.
                    try:
                        self.bridge.refresh_sheet(force=True)
                        self._rebuild_status_cache_from_sheet()
                        # Overlay any pending writes that still remain (failed sync)
                        self._apply_pending_sheet_status_to_local_cache()
                    except Exception as _re:
                        _multi_log.warning(f"[INTERNET] Sheet refresh/rebuild failed after restore: {_re}")

                    # Use the exact selected order from run-start, not active_devices
                    _sel_order = list(getattr(self, "_current_run_selected_order", []))
                    _restart_ids = getattr(self, "_internet_restart_ids", set())
                    _was_running = getattr(self, "_internet_running_ids", set())
                    _was_queued = getattr(self, "_internet_queued_ids", set())
                    _was_retry = getattr(self, "_internet_retry_ids", set())

                    _multi_log.info(f"[INTERNET] requeue source=current_run_selected_order")
                    _multi_log.info(f"[INTERNET] selected_run_ids={_sel_order}")
                    _multi_log.info(
                        f"[INTERNET] categories running={sorted(_was_running)} "
                        f"queued={sorted(_was_queued)} retry={sorted(_was_retry)}")

                    self._run_queue.clear()
                    for adb_id in _sel_order:
                        # SAME resolver as _run_launch_one. The old copy here
                        # skipped every DeviceType with no Task Config, so a
                        # device a normal Run would have restarted as a
                        # prepare_target_app-only setup run was silently dropped.
                        _rv = self._resolve_run_task_keys(adb_id)
                        if _rv["action"] == "skip":
                            _multi_log.info(
                                f"[INTERNET] {adb_id} not restarted — {_rv['reason']}")
                            continue
                        if _rv["action"] == "invalid":
                            # Never reinterpreted as setup-only: the device is
                            # misconfigured, and running preparation would report
                            # a success it did not earn.
                            _multi_log.error(
                                f"[INTERNET] {adb_id} not restarted — {_rv['reason']}")
                            self._run_set_badge(adb_id, _rv["badge"] or "NO TASKS",
                                                BADGE_IDLE[0], BADGE_IDLE[1])
                            continue
                        # "run" -> its resolved keys; "setup_only" -> [].
                        task_keys = _rv["task_keys"]

                        # ── Category decides whether task statuses are even
                        # relevant ──────────────────────────────────────────
                        # A QUEUED device never launched, so prepare_target_app never
                        # ran for it. Its tasks may well read "done" from an
                        # earlier run — that says nothing about this one. Same
                        # for a RETRY-only device: its connection attempt never
                        # completed. Only a device that was actively RUNNING has
                        # task statuses that describe the current attempt.
                        if adb_id in _was_queued:
                            all_done = False
                            _multi_log.info(
                                f"[INTERNET] {adb_id} was QUEUED at the emergency — "
                                f"prepare_target_app never ran, restarting regardless of "
                                f"task status")
                        elif adb_id in _was_retry:
                            all_done = False
                            _multi_log.info(
                                f"[INTERNET] {adb_id} was awaiting an ADB retry at the "
                                f"emergency — its attempt never completed, restarting")
                        else:
                            cached = self._status_cache.get(adb_id, {})
                            snapshot = {}
                            try:
                                snapshot = self.bridge.status_snapshot(adb_id)
                            except Exception as _ss_e:
                                _multi_log.warning(f"[INTERNET] status_snapshot({adb_id}) failed: {_ss_e}")

                            def _is_task_done(tk, _c=cached, _s=snapshot):
                                if _c.get(tk) == "done":
                                    return True
                                sv = _s.get(tk, "")
                                if sv and sv.strip().lower() == "done":
                                    return True
                                td = TASK_DEFS.get(tk, {})
                                if td.get("header") is None and sv:
                                    return True
                                return False

                            if task_keys:
                                all_done = all(_is_task_done(tk) for tk in task_keys)
                            else:
                                # setup-only run (task_keys=[]): re-queue if the
                                # device was part of this run at all.
                                if adb_id in _restart_ids:
                                    all_done = False
                                    _multi_log.info(f"[INTERNET] setup-only restart required adb_id={adb_id}")
                                else:
                                    all_done = True
                                    _multi_log.info(f"[INTERNET] setup-only already completed before emergency, skipping adb_id={adb_id}")

                        if not all_done and adb_id not in self._running_devs \
                                and adb_id not in self._run_queue:
                            # `not in _run_queue` matters: a device already
                            # waiting would otherwise be queued twice and
                            # launched twice.
                            _multi_log.info(f"[INTERNET] re-queuing unfinished adb_id={adb_id}")
                            self._run_queue.append(adb_id)
                        else:
                            _multi_log.info(f"[INTERNET] skipping completed adb_id={adb_id}")

                    # Order-preserving de-duplication, defensively: the loop
                    # already guards each append, but the queue must never carry
                    # the same device twice.
                    _seen_r: set = set()
                    self._run_queue[:] = [
                        a for a in self._run_queue
                        if not (a in _seen_r or _seen_r.add(a))]

                    self._internet_killed_ids = set()
                    self._internet_restart_ids = set()
                    self._internet_running_ids = set()
                    self._internet_queued_ids = set()
                    self._internet_retry_ids = set()
                    self._internet_emergency_owner = None
                    self.q.put(("sheet_redraw", None))
                    _multi_log.info(
                        f"[INTERNET] restore complete — {len(self._run_queue)} "
                        f"device(s) re-queued for session {_cur_sid}")
                    self._run_pump()
                    # Nothing left to restart (everything finished before the
                    # outage): the session ends here, RUN SELECTED re-enables and
                    # any deferred panel refresh is applied.
                    self._finish_run_session_if_idle()

                elif kind == "run_done":
                    # ("run_done", session_id, launch_token, adb_id, ok, result).
                    # The four-element legacy form is still unpacked so an older
                    # in-flight message cannot crash the handler; _on_run_done
                    # then rejects it unless it is provably harmless.
                    if len(item) >= 6:
                        _, _rd_sid, _rd_tok, adb_id, ok, result = item[:6]
                    else:
                        _, adb_id, ok, result = item[:4]
                        _rd_sid = _rd_tok = None
                    # No logging here. _on_run_done validates the identity first
                    # and writes both the ✓/✗ result line and the [RUN-DONE]
                    # record itself, so a stale completion produces only the
                    # [IDENTITY] diagnostic — never a result the user or
                    # LogAnalyzer would read as real.
                    self._on_run_done(adb_id, ok, result, _rd_sid, _rd_tok)

                elif kind == "run_fatal_stop":
                    # C: FatalAPKError — newer TargetApp version on device, APK missing locally.
                    # Must stop the entire run immediately and show a popup.
                    _, adb_id, reason = item[:3]
                    _f_sid = item[3] if len(item) > 3 else None
                    _f_tok = item[4] if len(item) > 4 else None
                    # A fatal from a dead attempt must not tear down a newer Run:
                    # this handler kills every worker and clears the queue.
                    if not self._run_control_identity_matches(
                            adb_id, _f_sid, _f_tok, what="run_fatal_stop"):
                        continue
                    err_msg = f"⛔ FATAL [{adb_id.split(':')[-1]}]: {reason}"
                    self._fatal_run_stop = True   # C: set flag — no new devices start
                    self._shutdown_pending = True  # block queue pump
                    # WHO the Run owns, before any of it is mutated. The queue
                    # is cleared below and _run_stop_all — which normally
                    # finalizes queued devices — then finds it already empty,
                    # so queued contexts got no report at all.
                    _fsnap = self._human_snapshot_abandoned_run()
                    # Claim the trigger's terminal result NOW, bound to its
                    # exact launch identity. Its own all_done may already be
                    # sitting in self.q — the cache drain preserves non-cache
                    # messages — so without this the wording would depend on
                    # which run_done _poll happened to reach first.
                    _finfo0 = self._running_devs.get(adb_id) or {}
                    self._set_terminal_override(
                        adb_id, _finfo0.get("session_id", _f_sid),
                        _finfo0.get("launch_token", _f_tok),
                        f"fatal: {reason}" if reason else "fatal", ok=False)
                    _fnote = (f"Run aborted because device {adb_id} reported: "
                              f"{reason}")
                    # A device in its ADB retry window has no worker to kill;
                    # cancel the callback or it re-queues after the fatal stop.
                    # NOT _human_finalize_pending_retries: its generic "stopped"
                    # reads as a manual Stop, which this is not.
                    self._cancel_run_retries(reason="fatal_stop")
                    self._cancel_hard_internet_emergency(reason="fatal_stop")
                    self._cancel_internet_pause(reason="fatal_stop")
                    try:
                        self._run_log_msg(err_msg, "err")
                    except Exception:
                        pass
                    try:
                        self._log(err_msg, "err")
                    except Exception:
                        pass
                    _multi_log.error(f"[FATAL] run_fatal_stop received: {reason}")

                    # Phase 1 — queued and retry-only. Before the queue is
                    # cleared, and with the fatal reason preserved in the report
                    # rather than only in controller_ui.log.
                    self._human_finalize_abandoned_nonrunning(
                        _fsnap, "stopped_by_fatal_run", note=_fnote,
                        close_disposition="not_requested_stop_all")

                    # Clear queue so no more devices launch
                    discarded = list(self._run_queue)
                    self._run_queue.clear()
                    if discarded:
                        _multi_log.info(f"[FATAL] cleared {len(discarded)} queued device(s)")

                    # G: Drain every running worker's mp_q AND the controller
                    # self.q BEFORE killing, so in-flight status updates are
                    # committed to the cache and not lost.
                    for _fid in list(self._running_devs.keys()):
                        _finfo = self._running_devs.get(_fid) or {}
                        _fq = _finfo.get("mp_q")
                        if _fq is not None:
                            self._drain_worker_queue(
                                _fid, _fq, reason="fatal:pre-kill",
                                session_id=_finfo.get("session_id"),
                                launch_token=_finfo.get("launch_token"))
                    self._drain_controller_queue_cache_messages(reason="fatal:pre-kill")

                    # Kill all running worker processes (no emulator close).
                    # _run_stop_all() drains mp_q + self.q around each kill too.
                    # 6: Only use _run_stop_all() — the main run-flow killer.
                    # _multi_stop_all() is for the Test/Multi tab's own threads
                    # and uses old direct flush_status logic outside the cache flow.
                    # final_sync=False: skip its background sync so this handler
                    # performs exactly ONE controlled synchronous final sync below
                    # (avoids the double-sync race against the sync lock).
                    # ── FATAL TRIGGER OWNERSHIP: CONTROLLER-OWNED ────────
                    # Once run_fatal_stop is accepted the CONTROLLER owns the
                    # trigger's terminal completion. It deliberately drains and
                    # drops the worker's own all_done — `_drain_worker_queue`
                    # discards all_done by design — and supplies the terminal
                    # result itself, taken from the fatal reason. This is
                    # deterministic: it does not depend on whether the worker's
                    # message wins a race with the kill.
                    #
                    # What the worker still owns is its RAW evidence. The grace
                    # below lets it finish writing `recording stopped —`, its
                    # counter snapshot and [WORKER-END] into the device log,
                    # and the human slice is captured afterwards — so a
                    # graceful finalizer's records appear, and a killed one's
                    # absence is reported honestly. Nothing is fabricated
                    # either way.
                    #
                    # The trigger is excluded from the generic Stop All path
                    # because that path would label it "stopped", losing the
                    # only record of why the Run died.
                    try:
                        self._run_stop_all(final_sync=False,
                                           exclude={adb_id},
                                           terminal_result="stopped_by_fatal_run")
                    except Exception:
                        pass

                    # Bounded grace, then stop. Either way the terminal
                    # result is the controller's fatal-specific one; the grace
                    # only decides how much real evidence the raw log holds.
                    if adb_id in self._running_devs:
                        _fres = f"fatal: {reason}" if reason else "fatal"
                        try:
                            self._force_stop_worker_process(
                                adb_id, reason="fatal:trigger",
                                terminal_result=_fres,
                                grace_s=FATAL_TRIGGER_GRACE_SECONDS)
                        except Exception:
                            pass
                        _hc_trig = self._human_ctx.get(
                            (self._run_session_id, adb_id))
                        if _hc_trig is not None and not _hc_trig.finalized:
                            _hc_trig.notes.append(
                                f"This device raised the fatal error that "
                                f"aborted the Run: {reason}")

                    # Phase 2 — the OTHER running devices. _run_stop_all has
                    # killed and drained them by now, so their slices are
                    # complete. The trigger is excluded: its terminal result is
                    # the controller-owned fatal one emitted above, which is
                    # more specific than "aborted by a fatal error on another
                    # device". Its own report is finalized by _on_run_done when
                    # that run_done is processed.
                    self._human_finalize_abandoned_running(
                        {"running": [d for d in _fsnap.get("running", [])
                                     if d != adb_id]},
                        "stopped_by_fatal_run", note=_fnote,
                        close_disposition="not_requested_stop_all")

                    # _run_stop_all returns early on the final_sync=False path,
                    # before its own completion check, so the fatal route ends
                    # the session itself.
                    try:
                        self._finish_run_session_if_idle()
                    except Exception:
                        pass

                    # G: Final controller-queue drain, then ONE SYNCHRONOUS final
                    # cache→sheet sync so the writes complete before the modal
                    # popup blocks the UI thread.  _flush_pending_sheet_status()
                    # is itself a no-op when nothing is pending/dirty.
                    self._drain_controller_queue_cache_messages(reason="fatal_final")
                    try:
                        _multi_log.info("[FATAL] final cache→sheet sync before popup")
                        self._flush_pending_sheet_status()
                    except Exception as _fe:
                        _multi_log.warning(f"[FATAL] final sync failed: {_fe}")

                    # C: Show Tkinter error popup on main thread
                    popup_msg = (
                        f"A newer Target Application version was detected on device {adb_id}.\n\n"
                        f"The matching APK / XAPK file is missing from APK_FOLDER.\n\n"
                        f"Add the new APK/XAPK to APK_FOLDER, then start the run again.\n\n"
                        f"The controller run has been stopped.\n\n"
                        f"Reason: {reason}"
                    )
                    try:
                        messagebox.showerror("Fatal APK / Version Issue", popup_msg)
                    except Exception:
                        pass

                elif kind == "sheet_redraw":
                    self._draw_sheet_grid()

                # ── Sync Devices ──────────────────────────────────────────
                elif kind == "sync_result":
                    result = item[1]
                    try:
                        self._show_sync_result(result)
                    except Exception as ex:
                        self._log(f"Sync result display error: {ex}", "err")
                    if "error" not in result:
                        n_add = len(result.get("added", []))
                        n_upd = len(result.get("name_updated", []))
                        self._log(
                            f"✓ Sync done — {n_add} added, {n_upd} name(s) updated, "
                            f"{result.get('total', 0)} total", "ok")
                        self.q.put(("sheet_redraw", None))
                    else:
                        self._log(f"✗ Sync error: {result.get('error', '')}", "err")

                # ── VPN Monitor ───────────────────────────────────────────
                elif kind == "vpn_build_grid":
                    _, adb_ids, names = item
                    try:
                        self._vpn_build_grid(adb_ids, names)
                    except Exception as ex:
                        print(f"[vpn_build_grid] {ex}")

                elif kind == "vpn_log_msg":
                    _, msg, tag = item
                    self._vpn_write_log(msg, tag)

                elif kind == "vpn_started":
                    _, adb_ids, names, error = item
                    if error:
                        self._vpn_write_log(
                            f"[{_ts()}]  ✗ Error: {error}\n", "offline")
                        try:
                            self._vpn_start_btn.configure(state=tk.NORMAL)
                            self._vpn_stop_btn.configure(state=tk.DISABLED)
                            self._vpn_status_lbl.configure(text="● Error", fg=FG_ERR)
                        except Exception:
                            pass
                    else:
                        try:
                            self._vpn_start_threads(adb_ids, names)
                            self._vpn_write_log(
                                f"[{_ts()}]  ✓ Monitoring started — "
                                f"{len(adb_ids)} device(s)\n", "info")
                        except Exception as ex:
                            self._vpn_write_log(
                                f"[{_ts()}]  ✗ Thread start failed: {ex}\n", "offline")

                elif kind == "vpn_update":
                    _, adb_id, name, online, first = item
                    try:
                        self._vpn_update_device(adb_id, name, online, first)
                    except Exception:
                        pass

                # ── FIX 7: Issues tab ─────────────────────────────────────
                elif kind == "issues_loaded":
                    try:
                        self._issues_loaded(item[1])
                    except Exception:
                        pass

                # ── Log Analyzer tab ──────────────────────────────────────
                elif kind == "la_status":
                    self._la_set_status(item[1])
                elif kind == "la_scanned":
                    try:
                        self._la_on_scanned(item[1], item[2], item[3])
                    except Exception as _e:
                        print(f"[_poll] la_scanned error: {_e}")
                elif kind == "la_result":
                    try:
                        self._la_on_result(item[1])
                    except Exception as _e:
                        print(f"[_poll] la_result error: {_e}")

                # ── Screenshotor tab ──────────────────────────────────────
                elif kind == "ss_status":
                    self._ss_set_status(item[1])
                elif kind == "ss_scan_done":
                    # item = ("ss_scan_done", session_id, devices_or_error)
                    try:
                        _sid, _devices = item[1], item[2]
                        if _sid == self._ss_session_id:
                            self._ss_finish_start(_devices)
                        # else: stale scan from a stopped/cleared/restarted
                        # session — ignore so it cannot reactivate or repopulate.
                    except Exception as _e:
                        print(f"[_poll] ss_scan_done error: {_e}")
                elif kind == "ss_device_result":
                    # item = ("ss_device_result", session_id, result_dict)
                    # All state mutation + file save happen here on the main
                    # thread; stale sessions are dropped inside the handler.
                    try:
                        self._ss_on_device_result(item[1], item[2])
                    except Exception as _e:
                        print(f"[_poll] ss_device_result error: {_e}")
                elif kind == "ss_batch_done":
                    # item = ("ss_batch_done", session_id, summary)
                    try:
                        _sid, _summary = item[1], item[2]
                        if _sid == self._ss_session_id:
                            self._ss_on_batch_done(_summary)
                        # else: stale batch finishing after Stop/Clear/new Start —
                        # ignore.  Do NOT clear _ss_busy here: a newer current
                        # batch may already be running.  Stop/Clear own the reset.
                    except Exception as _e:
                        print(f"[_poll] ss_batch_done error: {_e}")

                # ── Data Extractor tab ────────────────────────────────────
                elif kind == "de_status":
                    self._de_set_status(item[1])
                elif kind == "de_page_detected":
                    try:
                        self._de_on_page_detected(item[1])
                    except Exception as _e:
                        print(f"[_poll] de_page_detected error: {_e}")
                elif kind == "de_extract_result":
                    try:
                        self._de_on_extract_result(item[1])
                    except Exception as _e:
                        print(f"[_poll] de_extract_result error: {_e}")
                elif kind == "de_error":
                    try:
                        self._de_on_error(item[1])
                    except Exception as _e:
                        print(f"[_poll] de_error error: {_e}")

        except Empty:
            pass
        except Exception as ex:
            print(f"[_poll] error: {ex}")
        finally:
            self.after(80, self._poll)

    # ══════════════════════════════════════════════════════════════════════════
    # TAB: LOG ANALYZER  (local log parsing only — no Google Sheets)
    # ══════════════════════════════════════════════════════════════════════════
    def _build_log_analyzer_tab(self):
        tab = self._tab_log_analyzer
        for w in tab.winfo_children():
            w.destroy()
        tab.columnconfigure(0, weight=1)
        tab.rowconfigure(4, weight=1)   # bottom (timeline / issues) stretches

        # analyzer state
        self._la_analyzer = LogAnalyzer(base_dir=LOG_DIR)
        self._la_entries = []           # scanned LogEntry dicts
        self._la_timeframes = []        # list of {label,start,end}
        self._la_last_result = None     # last analysis dict (for export)

        # ── Row 0: controls ──────────────────────────────────────────────────
        ctl = tk.Frame(tab, bg=BG_MID)
        ctl.grid(row=0, column=0, sticky="ew")
        tk.Label(ctl, text="📊  LOG ANALYZER", font=FH, bg=BG_MID, fg=PRI,
                 padx=10, pady=8).pack(side=tk.LEFT)
        tk.Label(ctl, text="Local log parsing only — no Google Sheets required.",
                 font=FS, bg=BG_MID, fg=FG_DIM, padx=4).pack(side=tk.LEFT)

        _btn(ctl, "⟳ Refresh Logs", self._la_refresh_logs,
             bg=BG_CELL, fg=ACC_BLUE, font=FNB, padx=8, pady=4).pack(side=tk.LEFT, padx=(14, 4))

        tk.Label(ctl, text="Timeframe:", font=FS, bg=BG_MID, fg=FG_DIM).pack(side=tk.LEFT, padx=(8, 2))
        self._la_tf_var = tk.StringVar(value="All logs")
        self._la_tf_combo = ttk.Combobox(ctl, textvariable=self._la_tf_var, state="readonly",
                                          width=34, font=FS, values=["All logs"])
        self._la_tf_combo.pack(side=tk.LEFT, padx=2)

        tk.Label(ctl, text="Device:", font=FS, bg=BG_MID, fg=FG_DIM).pack(side=tk.LEFT, padx=(8, 2))
        self._la_dev_var = tk.StringVar(value="(all devices)")
        self._la_dev_combo = ttk.Combobox(ctl, textvariable=self._la_dev_var, state="readonly",
                                           width=20, font=FS, values=["(all devices)"])
        self._la_dev_combo.pack(side=tk.LEFT, padx=2)

        self._la_analyze_btn = _btn(ctl, "▶ Analyze", self._la_analyze,
                                    bg=ACC_BLUE, fg="white", font=FNB, padx=10, pady=4)
        self._la_analyze_btn.pack(side=tk.LEFT, padx=(10, 4))
        self._la_export_btn = _btn(ctl, "⬇ Export", self._la_export,
                                   bg=BG_CELL, fg=FG_MAIN, font=FNB, padx=8, pady=4,
                                   state=tk.DISABLED)
        self._la_export_btn.pack(side=tk.LEFT, padx=2)
        _btn(ctl, "ⓘ Pattern Coverage", self._la_show_pattern_coverage,
             bg=BG_CELL, fg=FG_DIM, font=FS, padx=8, pady=4).pack(side=tk.LEFT, padx=2)

        self._la_status = tk.Label(ctl, text="", font=FS, bg=BG_MID, fg=FG_DIM)
        self._la_status.pack(side=tk.RIGHT, padx=10)

        # ── Row 1: overall summary card ──────────────────────────────────────
        ov = tk.LabelFrame(tab, text=" Overall ", font=FSB, bg=BG_PANEL, fg=FG_DIM,
                           bd=1, relief=tk.SOLID, labelanchor="nw")
        ov.grid(row=1, column=0, sticky="ew", padx=6, pady=(6, 2))
        self._la_overall_txt = tk.Text(ov, height=7, font=FMS, bg=BG_CELL, fg=FG_MAIN,
                                       relief=tk.FLAT, wrap="word", bd=0)
        self._la_overall_txt.pack(fill=tk.X, padx=6, pady=6)
        self._la_overall_txt.configure(state=tk.DISABLED)

        # ── Row 2: tables (task left, devicetype right) ──────────────────────
        tables = tk.Frame(tab, bg=BG_BASE)
        tables.grid(row=2, column=0, sticky="ew", padx=6, pady=2)
        tables.columnconfigure(0, weight=3)
        tables.columnconfigure(1, weight=2)

        # task table
        tfrm = tk.LabelFrame(tables, text=" Task Summary ", font=FSB, bg=BG_PANEL,
                             fg=FG_DIM, bd=1, relief=tk.SOLID, labelanchor="nw")
        tfrm.grid(row=0, column=0, sticky="nsew", padx=(0, 4))
        tcols = ("task", "attempts", "done", "skipped", "failed", "restarts", "succ")
        self._la_task_tv = ttk.Treeview(tfrm, columns=tcols, show="headings",
                                        style="Sheet.Treeview", height=9)
        for c, w, t in [("task", 150, "Task"), ("attempts", 70, "Attempts"),
                        ("done", 55, "Done"), ("skipped", 60, "Skipped"),
                        ("failed", 55, "Failed"), ("restarts", 65, "Restarts"),
                        ("succ", 60, "Succ %")]:
            self._la_task_tv.heading(c, text=t, anchor=tk.W)
            self._la_task_tv.column(c, width=w, minwidth=40,
                                    stretch=(c == "task"), anchor=tk.W)
        self._la_task_tv.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)

        # devicetype table
        dfrm = tk.LabelFrame(tables, text=" DeviceType Summary ", font=FSB, bg=BG_PANEL,
                             fg=FG_DIM, bd=1, relief=tk.SOLID, labelanchor="nw")
        dfrm.grid(row=0, column=1, sticky="nsew", padx=(4, 0))
        dcols = ("type", "devices", "runs", "success", "failed", "stopped", "incomplete",
                 "known", "overall")
        self._la_devtype_tv = ttk.Treeview(dfrm, columns=dcols, show="headings",
                                           style="Sheet.Treeview", height=9)
        for c, w, t in [("type", 92, "Type"), ("devices", 54, "Devices"),
                        ("runs", 44, "Runs"), ("success", 52, "Success"),
                        ("failed", 48, "Failed"), ("stopped", 52, "Stopped"),
                        ("incomplete", 56, "Incompl."),
                        ("known", 70, "Known%"), ("overall", 70, "Overall%")]:
            self._la_devtype_tv.heading(c, text=t, anchor=tk.W)
            self._la_devtype_tv.column(c, width=w, minwidth=40,
                                       stretch=(c == "type"), anchor=tk.W)
        self._la_devtype_tv.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)

        # ── Row 3: selected device detail ────────────────────────────────────
        dd = tk.LabelFrame(tab, text=" Selected Device ", font=FSB, bg=BG_PANEL,
                           fg=FG_DIM, bd=1, relief=tk.SOLID, labelanchor="nw")
        dd.grid(row=3, column=0, sticky="ew", padx=6, pady=2)
        self._la_device_txt = tk.Text(dd, height=8, font=FMS, bg=BG_CELL, fg=FG_MAIN,
                                      relief=tk.FLAT, wrap="word", bd=0)
        self._la_device_txt.pack(fill=tk.X, padx=6, pady=6)
        self._la_device_txt.configure(state=tk.DISABLED)

        # ── Row 4: timeline + potential issues + unclassified (side by side) ──
        bottom = tk.Frame(tab, bg=BG_BASE)
        bottom.grid(row=4, column=0, sticky="nsew", padx=6, pady=(2, 6))
        bottom.columnconfigure(0, weight=2)
        bottom.columnconfigure(1, weight=2)
        bottom.columnconfigure(2, weight=1)
        bottom.rowconfigure(0, weight=1)

        tlf = tk.LabelFrame(bottom, text=" Important Event Timeline ", font=FSB,
                            bg=BG_PANEL, fg=FG_DIM, bd=1, relief=tk.SOLID, labelanchor="nw")
        tlf.grid(row=0, column=0, sticky="nsew", padx=(0, 4))
        self._la_timeline_txt = scrolledtext.ScrolledText(
            tlf, font=FMS, bg=BG_CELL, fg=FG_MAIN, relief=tk.FLAT, wrap="none", bd=0)
        self._la_timeline_txt.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)
        self._la_timeline_txt.configure(state=tk.DISABLED)

        isf = tk.LabelFrame(bottom, text=" Potential Issues / Things to Check ", font=FSB,
                            bg=BG_PANEL, fg=FG_DIM, bd=1, relief=tk.SOLID, labelanchor="nw")
        isf.grid(row=0, column=1, sticky="nsew", padx=4)
        self._la_issues_txt = scrolledtext.ScrolledText(
            isf, font=FMS, bg=BG_CELL, fg=FG_MAIN, relief=tk.FLAT, wrap="word", bd=0)
        self._la_issues_txt.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)
        self._la_issues_txt.tag_configure("err", foreground=FG_ERR)
        self._la_issues_txt.tag_configure("hdr", foreground=PRI)
        self._la_issues_txt.tag_configure("dim", foreground=FG_DIM)
        self._la_issues_txt.configure(state=tk.DISABLED)

        # Unclassified important lines (F) — helps refine patterns later
        ucf = tk.LabelFrame(bottom, text=" Unclassified Important Lines ", font=FSB,
                            bg=BG_PANEL, fg=FG_DIM, bd=1, relief=tk.SOLID, labelanchor="nw")
        ucf.grid(row=0, column=2, sticky="nsew", padx=(4, 0))
        self._la_unclassified_txt = scrolledtext.ScrolledText(
            ucf, font=FMS, bg=BG_CELL, fg=FG_DIM, relief=tk.FLAT, wrap="word", bd=0)
        self._la_unclassified_txt.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)
        self._la_unclassified_txt.configure(state=tk.DISABLED)

        # auto-scan once when the tab first becomes visible
        tab.bind("<Map>", lambda e: self._la_auto_first_scan())

    def _la_auto_first_scan(self):
        if getattr(self, "_la_scanned_once", False):
            return
        self._la_scanned_once = True
        self._la_refresh_logs()

    # ── analyzer enrichment from controller (optional) ──────────────────────────
    def _la_enrich_device_maps(self):
        """Populate analyzer DeviceType/name maps from already-loaded sheet rows.
        Optional enrichment only — never reads Google Sheets."""
        try:
            rows = getattr(self.bridge, "rows_by_device", {}) or {}
            dt_map, nm_map = {}, {}
            for adb_id, row in rows.items():
                dt = (row.get("device_type") or "").strip()
                if dt:
                    dt_map[adb_id] = dt
                nm = (row.get("name") or row.get("device_name") or "").strip()
                if nm:
                    nm_map[adb_id] = nm
            self._la_analyzer.device_type_map = dt_map
            self._la_analyzer.device_name_map = nm_map
        except Exception:
            pass

    # ── controls ────────────────────────────────────────────────────────────────
    def _la_refresh_logs(self):
        self._la_set_status("scanning logs…")
        self._log("[LOG-ANALYZER] scanning local logs…", "dim")

        def worker():
            try:
                self._la_enrich_device_maps()
                def _prog(msg):
                    self.q.put(("la_status", f"scan: {msg}"))
                entries = self._la_analyzer.scan_logs(progress=_prog)
                timeframes = self._la_analyzer.available_timeframes(entries)
                devices = self._la_analyzer.devices_in(entries)
                self.q.put(("la_scanned", entries, timeframes, devices))
            except Exception as ex:
                self.q.put(("la_status", f"scan error: {ex}"))
                self.q.put(("log", f"[LOG-ANALYZER] scan error: {ex}", "err"))
        threading.Thread(target=worker, daemon=True).start()

    def _la_analyze(self):
        if not self._la_entries:
            self._la_set_status("no logs scanned yet — click Refresh Logs")
            return
        # resolve timeframe
        label = self._la_tf_var.get()
        start = end = None
        for tf in self._la_timeframes:
            if tf["label"] == label:
                start, end = tf.get("start"), tf.get("end")
                break
        dev = self._la_dev_var.get()
        if dev == "(all devices)":
            dev = None
        self._la_set_status("analyzing…")
        self._log(f"[LOG-ANALYZER] analyzing timeframe={label!r} device={dev or 'all'}", "dim")

        entries = self._la_entries
        analyzer = self._la_analyzer

        def worker():
            try:
                result = analyzer.analyze(entries, start=start, end=end, device=dev,
                                          task_defs=TASK_DEFS,
                                          subtask_order=SUBTASK_ORDER)
                self.q.put(("la_result", result))
            except Exception as ex:
                import traceback as _tb
                self.q.put(("la_status", f"analyze error: {ex}"))
                self.q.put(("log", f"[LOG-ANALYZER] analyze error: {ex}\n{_tb.format_exc()}", "err"))
        threading.Thread(target=worker, daemon=True).start()

    def _la_export(self):
        result = getattr(self, "_la_last_result", None)
        if not result:
            self._la_set_status("nothing to export — run Analyze first")
            return

        def worker():
            try:
                stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                txt_path = os.path.join(LOG_DIR, f"log_analysis_{stamp}.txt")
                json_path = os.path.join(LOG_DIR, f"log_analysis_{stamp}.json")
                report = self._la_analyzer.render_text_report(result)

                # Additive recording section — the existing report body above is
                # untouched, so nothing that already parsed these exports breaks.
                rec_meta = {}
                try:
                    rec_meta = self._la_collect_recording_metadata()
                except Exception as rex:
                    self.q.put(("log", f"[LOG-ANALYZER] recording metadata skipped: {rex}", "warn"))

                if rec_meta:
                    lines = ["", "=" * 72, "RECORDINGS", "=" * 72]
                    for adb_id, m in sorted(rec_meta.items()):
                        lines.append(f"\n[{adb_id}]")
                        lines.append(f"  folder        : {m.get('folder','')}")
                        lines.append(f"  report        : {m.get('report','')}")
                        lines.append(f"  segments      : {m.get('segment_count',0)}")
                        lines.append(f"  events        : {m.get('event_count',0)}")
                        lines.append(f"  duration      : {m.get('duration_s',0)}s")
                        if m.get("video_failed"):
                            lines.append("  NOTE          : video incomplete — "
                                         "event timeline still available")
                        tc = m.get("event_type_counts") or {}
                        if tc:
                            lines.append("  event types   : " + ", ".join(
                                f"{k}={v}" for k, v in sorted(tc.items())))
                        pages = m.get("top_pages") or []
                        if pages:
                            lines.append("  page timeline :")
                            for pg in pages[:25]:
                                lines.append(f"     t+{pg.get('t')}s  {pg.get('page')}")
                        clicks = m.get("top_clicks") or []
                        if clicks:
                            lines.append("  click timeline:")
                            for ck in clicks[:25]:
                                lines.append(
                                    f"     t+{ck.get('t')}s  page={ck.get('page','')} "
                                    f"button={ck.get('button','')} coord={ck.get('coord','')} "
                                    f"attempt={ck.get('attempt','')} "
                                    f"result={ck.get('result','')}")
                    report = report + "\n" + "\n".join(lines) + "\n"
                    result = dict(result)
                    result["recordings"] = rec_meta

                with open(txt_path, "w", encoding="utf-8") as f:
                    f.write(report)
                with open(json_path, "w", encoding="utf-8") as f:
                    json.dump(result, f, indent=2, default=str)
                self.q.put(("la_status", f"exported {os.path.basename(txt_path)} + .json"))
                self.q.put(("log", f"[LOG-ANALYZER] exported {txt_path} and {json_path}", "ok"))
            except Exception as ex:
                self.q.put(("la_status", f"export error: {ex}"))
                self.q.put(("log", f"[LOG-ANALYZER] export error: {ex}", "err"))
        threading.Thread(target=worker, daemon=True).start()

    # ── queue-driven UI updates (called from _poll) ──────────────────────────────
    def _la_set_status(self, text: str):
        try:
            self._la_status.configure(text=text)
        except Exception:
            pass

    def _la_on_scanned(self, entries, timeframes, devices):
        self._la_entries = entries
        self._la_timeframes = timeframes
        tf_labels = [t["label"] for t in timeframes]
        try:
            self._la_tf_combo.configure(values=tf_labels)
            if tf_labels and self._la_tf_var.get() not in tf_labels:
                self._la_tf_var.set(tf_labels[0])
            dev_vals = ["(all devices)"] + list(devices)
            self._la_dev_combo.configure(values=dev_vals)
            if self._la_dev_var.get() not in dev_vals:
                self._la_dev_var.set("(all devices)")
        except Exception:
            pass
        self._la_set_status(f"scanned {len(entries)} log line(s) · "
                            f"{len(devices)} device(s) · {len(timeframes)} timeframe(s)")
        self._log(f"[LOG-ANALYZER] scan complete: {len(entries)} lines, "
                  f"{len(devices)} devices", "ok")

    def _la_collect_recording_metadata(self) -> dict:
        """
        Gather recording metadata for the Log Analyzer export.

        Reads recordings/run_*/<device>/recording_manifest.json and events.jsonl
        for every recording this controller session produced.  Purely additive:
        when nothing was recorded this returns an empty dict and the existing
        text/JSON export is completely unchanged.
        """
        out = {}
        for adb_id, info in (self._recording_paths or {}).items():
            folder = info.get("folder", "")
            if not folder or not os.path.isdir(folder):
                continue
            entry = {
                "folder":        folder,
                "report":        info.get("report", ""),
                "segment_count": info.get("segments", 0),
                "event_count":   info.get("events", 0),
                "duration_s":    info.get("duration_s", 0),
                "video_failed":  bool(info.get("failed")),
            }
            try:
                mpath = os.path.join(folder, "recording_manifest.json")
                if os.path.exists(mpath):
                    with open(mpath, "r", encoding="utf-8") as f:
                        man = json.load(f)
                    entry["segment_count"] = man.get("segment_count", entry["segment_count"])
                    entry["event_count"]   = man.get("event_count",   entry["event_count"])
                    entry["run_id"]        = man.get("run_id", "")
                    entry["started_at"]    = man.get("started_at", "")
                    entry["ended_at"]      = man.get("ended_at", "")
                    entry["event_type_counts"] = man.get("event_type_counts", {})
                    entry["segments"] = [sg.get("file") for sg in man.get("segments", [])]
            except Exception as exc:
                entry["manifest_error"] = str(exc)

            # Top timeline: the clicks and pages that explain the run.
            try:
                epath = os.path.join(folder, "events.jsonl")
                if os.path.exists(epath):
                    clicks, pages = [], []
                    with open(epath, "r", encoding="utf-8") as f:
                        for line in f:
                            line = line.strip()
                            if not line:
                                continue
                            try:
                                ev = json.loads(line)
                            except Exception:
                                continue
                            if ev.get("type") == "click" and len(clicks) < 100:
                                clicks.append({
                                    "t": ev.get("elapsed_s"),
                                    "page": ev.get("page", ""),
                                    "button": ev.get("button", ""),
                                    "coord": ev.get("coord", ""),
                                    "attempt": ev.get("attempt", ""),
                                    "result": ev.get("result", ""),
                                    "registered": ev.get("registered", ""),
                                })
                            elif ev.get("type") == "page_seen" and len(pages) < 100:
                                pages.append({"t": ev.get("elapsed_s"),
                                              "page": ev.get("page", "")})
                    entry["top_clicks"] = clicks
                    entry["top_pages"]  = pages
            except Exception as exc:
                entry["events_error"] = str(exc)

            out[adb_id] = entry
        return out

    def _la_on_result(self, result: dict):
        self._la_last_result = result
        try:
            self._la_export_btn.configure(state=tk.NORMAL)
        except Exception:
            pass

        o = result.get("overall", {})
        r = result.get("rates", {})
        tf = result.get("timeframe", {})

        # overall card
        overall_lines = [
            f"Timeframe: {tf.get('start')} → {tf.get('end')}   "
            f"(scanned {tf.get('entries_scanned')} lines)",
            f"Devices seen: {o.get('total_devices_seen', 0)}    "
            f"Runs: {o.get('total_device_runs', 0)}    "
            f"Completed: {o.get('completed_runs', 0)}    "
            f"Failed: {o.get('failed_runs', 0)}    "
            f"Stopped: {o.get('stopped_runs', 0)}    "
            f"Incomplete/unknown: {o.get('incomplete_runs', 0)}    "
            f"Skipped/no-pending: {o.get('skipped_no_pending', 0)}",
            f"prepare_target_app: attempts {o.get('prepare_target_app_attempts', 0)} · "
            f"success {o.get('prepare_target_app_success', 0)} · "
            f"failure {o.get('prepare_target_app_failure', 0)}",
            f"Tasks: attempts {o.get('total_task_attempts', 0)} · "
            f"done {o.get('task_done', 0)} · skipped {o.get('task_skipped', 0)} "
            f"(already-done {o.get('task_skipped_already_done', 0)}, "
            f"after-max {o.get('task_skipped_after_max', 0)}) · "
            f"failed {o.get('task_failed', 0)} · restarts {o.get('task_restarts', 0)} · "
            f"max_attempts {o.get('max_attempts_failures', 0)}",
            f"Events (deduped): guard_recovery {o.get('guard_recoveries', 0)} · "
            f"vpn_down {o.get('vpn_down_events', 0)} · "
            f"reopen {o.get('emulator_reopen_events', 0)} · "
            f"conn_issue {o.get('connection_issue_events', 0)} · "
            f"internet_emergency {o.get('internet_emergency_events', 0)} · "
            f"FatalAPK {o.get('fatal_apk_events', 0)}",
            f"RATES →  known finished run success: {r.get('run_success_rate', 0):.1f}% (completed/resolved)   "
            f"incl. incomplete: {r.get('run_success_rate_incl_incomplete', 0):.1f}% (completed/all)   "
            f"task exec: {r.get('task_execution_success_rate', 0):.1f}% (done/attempts)   "
            f"effective: {r.get('effective_completion_rate', 0):.1f}% (done+skipped/attempts)",
        ]
        for n in result.get("notes", []):
            overall_lines.append(f"NOTE: {n}")
        self._la_set_text(self._la_overall_txt, "\n".join(overall_lines))

        # task table
        self._la_fill_tree(self._la_task_tv, [
            (t["label"], t["attempts"], t["done"], t["skipped"], t["failed"],
             t["restarts"], f"{t['success_pct']:.0f}%")
            for t in result.get("task_rows", [])
        ])

        # devicetype table (item 1: Known% + Overall%)
        self._la_fill_tree(self._la_devtype_tv, [
            (d["device_type"], d["devices"], d["runs"], d["success"],
             d["failed"], d["stopped"], d.get("incomplete", 0),
             f"{d.get('known_success_pct', d.get('success_pct', 0)):.0f}%",
             f"{d.get('overall_success_pct', 0):.0f}%")
            for d in result.get("devtype_rows", [])
        ])

        # device detail
        dd = result.get("device_detail")
        if dd:
            dlines = [
                f"Device: {dd['device']}    Name: {dd.get('name') or '-'}    "
                f"Type: {dd.get('device_type')}",
                f"Runs: {dd['runs']}  ·  Success: {dd['success']}  ·  "
                f"Failed: {dd['failed']}  ·  Stopped: {dd['stopped']}  ·  "
                f"Incomplete: {dd.get('incomplete', 0)}  ·  "
                f"Skipped/no-pending: {dd['skipped']}",
                f"Success rates →  Known: {dd.get('known_success_pct', 0):.0f}% "
                f"(success/resolved)   Overall: {dd.get('overall_success_pct', 0):.0f}% "
                f"(success/all runs incl. incomplete)",
                f"prepare_target_app: attempts {dd.get('prepare_target_app_attempts', 0)} · "
                f"success {dd.get('prepare_target_app_success', 0)} · "
                f"failures {dd.get('prepare_target_app_failures', 0)}    "
                f"emulator reopen: {dd.get('emulator_reopen', 0)}",
                f"VPN: setup {dd.get('vpn_setup', 0)} · connect {dd.get('vpn_connect', 0)} · "
                f"down {dd.get('vpn_down', 0)} · setup-fail {dd.get('setup_vpn_failures', 0)}",
                f"TargetApp: setup {dd.get('target_app_setup', 0)} · loading-stuck {dd.get('target_app_loading_stuck', 0)} · "
                f"setup-fail {dd.get('setup_target_app_failures', 0)} · "
                f"conn-issue {dd.get('connection_issue', 0)} · guard-recovery {dd.get('guard_recovery', 0)}",
                f"FatalAPK: {dd.get('fatal_apk', 0)}    internet-down: {dd.get('internet_down', 0)}",
                f"Last issue / incomplete reason: {dd.get('last_issue', dd.get('last_failure', '-'))}",
                "",
                "Task breakdown:",
            ]
            for t in dd.get("tasks", []):
                dlines.append(
                    f"  {t['label'][:22]:<22} attempts {t['attempts']:>3}  "
                    f"done {t['done']:>3}  skip {t['skipped']:>3}  fail {t['failed']:>3}  "
                    f"restarts {t['restarts']:>3}  last={t['last_result']}"
                )
            self._la_set_text(self._la_device_txt, "\n".join(dlines))
        else:
            self._la_set_text(self._la_device_txt,
                              "Select a device and click Analyze to see its detail.")

        # timeline
        self._la_set_text(self._la_timeline_txt,
                          "\n".join(result.get("timeline_lines", [])) or "(no events)")

        # issues
        self._la_issues_txt.configure(state=tk.NORMAL)
        self._la_issues_txt.delete("1.0", tk.END)
        issues = result.get("issues", [])
        if not issues:
            self._la_issues_txt.insert(tk.END, "No potential issues detected for this timeframe.\n")
        else:
            for it in issues:
                raw = it.get("raw_lines", it["count"])
                affected = it.get("devices_affected", 0)
                if it.get("noisy"):
                    # item 4: events | raw lines | devices affected
                    hdr = (f"• {it['issue']}: events {it['count']} | "
                           f"raw lines {raw} | devices affected {affected}\n")
                else:
                    suffix = f"  (raw lines: {raw})" if raw != it["count"] else ""
                    hdr = f"• {it['issue']}  ×{it['count']}{suffix}\n"
                self._la_issues_txt.insert(tk.END, hdr, "hdr")
                # item 3/4: top affected devices (max 5)
                top = it.get("top_devices", [])
                if top:
                    td_str = ", ".join(f"{t['device']} x{t['count']}" for t in top)
                    self._la_issues_txt.insert(tk.END, f"    Top devices: {td_str}\n", "dim")
                for s in it.get("samples", []):
                    self._la_issues_txt.insert(tk.END, f"    {s}\n", "err")
        self._la_issues_txt.configure(state=tk.DISABLED)

        # unclassified important lines (F)
        unc = result.get("unclassified", [])
        self._la_set_text(
            self._la_unclassified_txt,
            ("\n".join(unc) if unc
             else "No unclassified important lines for this timeframe."))

        self._la_set_status(f"analysis done · {tf.get('entries_scanned')} lines in timeframe")

    def _la_show_pattern_coverage(self):
        """C: show the source-derived pattern coverage report in a popup."""
        try:
            report = self._la_analyzer.pattern_coverage_report()
        except Exception as ex:
            report = f"Pattern coverage unavailable: {ex}"
        top = tk.Toplevel(self)
        top.title("Log Analyzer — Pattern Coverage")
        top.configure(bg=BG_BASE)
        top.geometry("640x560")
        txt = scrolledtext.ScrolledText(top, font=FMS, bg=BG_CELL, fg=FG_MAIN,
                                        relief=tk.FLAT, wrap="word", bd=0)
        txt.pack(fill=tk.BOTH, expand=True, padx=8, pady=8)
        txt.insert(tk.END, report)
        txt.configure(state=tk.DISABLED)

    def _la_set_text(self, widget, text: str):
        try:
            widget.configure(state=tk.NORMAL)
            widget.delete("1.0", tk.END)
            widget.insert(tk.END, text)
            widget.configure(state=tk.DISABLED)
        except Exception:
            pass

    def _la_fill_tree(self, tv, rows):
        try:
            tv.delete(*tv.get_children())
            for r in rows:
                tv.insert("", tk.END, values=r)
        except Exception:
            pass

    # ══════════════════════════════════════════════════════════════════════════
    # TAB: SCREENSHOTOR  (standalone device-screenshot helper — no run/cache/sheet)
    # ══════════════════════════════════════════════════════════════════════════
    SS_BASE_DIR = "screenshots"   # root folder (relative to controller cwd)
    SS_HASH_FILE = "_screenshot_hashes.json"   # under SS_BASE_DIR
    SS_CAPTURE_RETRIES = 5        # screencap attempts per device before failing
    SS_CAPTURE_RETRY_DELAY = 0.75 # seconds between attempts (interruptible)
    SS_CAPTURE_TIMEOUT = 10       # per-attempt adb screencap timeout (seconds)
    SS_SCAN_CONNECT_TIMEOUT = 4   # per-port adb connect timeout during scan
    SS_SCAN_STATE_TIMEOUT = 2     # per-port adb get-state timeout during scan
    SS_PAGES_FILE = "screenshot_pages.json"    # persistent page-name list (cwd)
    SS_ENTER_SENTINEL = "Enter name:"          # dropdown entry that lets user type a new page
    SS_DEFAULT_PAGES = [
        "target app main", "game main map", "monster", "server", "resource",
        "shield", "app level", "app power", "speedup", "equipment chest",
        "equipment market", "resources", "inventory other",
    ]

    # ── page-name persistence ─────────────────────────────────────────────────
    def _ss_load_page_names(self):
        """
        Load the page-name list from screenshot_pages.json (cwd).  Creates it with
        the default list if missing/corrupt.  Names are trimmed; duplicates
        removed (case-insensitive) while preserving order/display.
        """
        path = self.SS_PAGES_FILE
        names = []
        try:
            if os.path.exists(path):
                with open(path, "r", encoding="utf-8") as fh:
                    data = json.load(fh)
                raw = data.get("pages") if isinstance(data, dict) else data
                if isinstance(raw, list):
                    seen = set()
                    for n in raw:
                        nm = str(n).strip()
                        if nm and nm.lower() not in seen:
                            seen.add(nm.lower())
                            names.append(nm)
        except Exception:
            names = []
        if not names:
            names = list(self.SS_DEFAULT_PAGES)
            self._ss_page_names = names
            self._ss_save_page_names()
        else:
            self._ss_page_names = names
        return names

    def _ss_save_page_names(self):
        """Persist the current page-name list (best-effort, never raises)."""
        try:
            tmp = self.SS_PAGES_FILE + ".tmp"
            with open(tmp, "w", encoding="utf-8") as fh:
                json.dump({"pages": list(self._ss_page_names)}, fh, indent=2)
            os.replace(tmp, self.SS_PAGES_FILE)
        except Exception:
            pass

    def _ss_add_page_name(self, name):
        """
        Add a trimmed page name to the list (no case-insensitive duplicates),
        persist it, and refresh both dropdowns.  Returns the canonical name or "".
        """
        nm = (name or "").strip()
        if not nm or nm == self.SS_ENTER_SENTINEL:
            return ""
        # Already present (case-insensitive)? return the existing display form.
        for existing in self._ss_page_names:
            if existing.lower() == nm.lower():
                return existing
        self._ss_page_names.append(nm)
        self._ss_save_page_names()
        self._ss_refresh_page_dropdowns()
        return nm

    def _ss_refresh_page_dropdowns(self):
        """Update the combobox value lists in the main tab and mini window."""
        values = list(self._ss_page_names) + [self.SS_ENTER_SENTINEL]
        for cb_attr in ("_ss_page_combo", "_ss_mini_page_combo"):
            cb = getattr(self, cb_attr, None)
            if cb is not None:
                try:
                    cb.configure(values=values)
                except Exception:
                    pass

    def _ss_sanitize_page_name(self, page):
        """
        Windows-safe filename token for a page name: replace forbidden chars and
        spaces with '_', collapse repeats, trim.  Uses the shared sanitizer then
        converts spaces → underscores.
        """
        import re as _re
        s = self._ss_sanitize(page or "")
        s = _re.sub(r"\s+", "_", s)
        s = _re.sub(r"_+", "_", s).strip("_")
        return s or "page"

    def _ss_selected_page_name(self, mini=False):
        """
        Return the trimmed selected page name.  Main and mini share _ss_page_var,
        so the shared var is the source of truth; fall back to the mini var only
        if the shared one is unavailable.
        """
        var = self._ss_page_var or self._ss_mini_page_var
        if mini and self._ss_mini_page_var is not None:
            var = self._ss_mini_page_var or self._ss_page_var
        try:
            val = (var.get() if var is not None else "").strip()
        except Exception:
            val = ""
        if val == self.SS_ENTER_SENTINEL:
            return ""
        return val

    def _ss_existing_page_count(self, device_folder, ark_name, page_name):
        """
        Count existing saved files for this device folder + page (matching the
        '<device>_<page>_<NNN>.png' pattern).  Used to continue numbering and to
        decide page-status 'done'.
        """
        import re as _re
        dev_dir = os.path.join(self.SS_BASE_DIR, device_folder)
        page_tok = self._ss_sanitize_page_name(page_name)
        ark_tok = self._ss_sanitize_page_name(ark_name)
        pat = _re.compile(r"^" + _re.escape(f"{ark_tok}_{page_tok}_") + r"(\d+)\.png$",
                          _re.IGNORECASE)
        count = 0
        try:
            for fn in os.listdir(dev_dir):
                if pat.match(fn):
                    count += 1
        except Exception:
            pass
        return count

    def _ss_next_page_filename(self, device_folder, ark_name, page_name):
        """
        Build the next '<device>_<page>_<NNN>.png' path for this device+page,
        continuing from the highest existing number.  Falls back to a timestamp
        suffix only if a collision somehow remains.
        """
        import re as _re
        dev_dir = os.path.join(self.SS_BASE_DIR, device_folder)
        page_tok = self._ss_sanitize_page_name(page_name)
        ark_tok = self._ss_sanitize_page_name(ark_name)
        pat = _re.compile(r"^" + _re.escape(f"{ark_tok}_{page_tok}_") + r"(\d+)\.png$",
                          _re.IGNORECASE)
        highest = 0
        try:
            for fn in os.listdir(dev_dir):
                m = pat.match(fn)
                if m:
                    highest = max(highest, int(m.group(1)))
        except Exception:
            pass
        nxt = highest + 1
        fname = f"{ark_tok}_{page_tok}_{nxt:03d}.png"
        path = os.path.join(dev_dir, fname)
        if os.path.exists(path):   # collision fallback
            from datetime import datetime as _dt
            fname = f"{ark_tok}_{page_tok}_{nxt:03d}_{_dt.now().strftime('%H%M%S')}.png"
            path = os.path.join(dev_dir, fname)
        return path

    def _ss_hash_index_path(self):
        import os as _os
        return _os.path.join(self.SS_BASE_DIR, self.SS_HASH_FILE)

    def _ss_device_hash_key(self, adb_id: str, folder: str) -> str:
        """Stable per-device key for the persistent hash index."""
        return f"{folder}|{adb_id}"

    def _ss_load_hash_index(self) -> dict:
        """
        Load the persistent per-device index from disk and normalise it to the
        rich shape:
            {"<folder>|<adb_id>": {"sha256": [..], "records": [ {sha256, ahash,
              dhash, sig, path, saved_at}, .. ]}, ..}

        Migration: an old value that is a plain list of SHAs is converted to
        {"sha256": [...], "records": []}.  Missing/corrupt JSON → {} (clean
        start; a warning is logged).
        """
        import os as _os, json as _json
        path = self._ss_hash_index_path()
        out = {}
        try:
            if not _os.path.exists(path):
                return {}
            with open(path, "r", encoding="utf-8") as fh:
                data = _json.load(fh)
            if not isinstance(data, dict):
                _multi_log.info("[SCREENSHOT] hash index not a dict — starting clean")
                return {}
            for k, v in data.items():
                if isinstance(v, (list, tuple)):
                    # Old format: list of SHA strings.
                    out[str(k)] = {"sha256": [str(s) for s in v], "records": []}
                elif isinstance(v, dict):
                    shas = v.get("sha256") or []
                    recs = v.get("records") or []
                    out[str(k)] = {
                        "sha256": [str(s) for s in shas if isinstance(s, str)],
                        "records": [r for r in recs if isinstance(r, dict)],
                    }
                # else: ignore malformed entry
        except Exception as exc:
            _multi_log.info(f"[SCREENSHOT] hash index unreadable ({exc}) — starting clean")
            return {}
        return out

    def _ss_save_hash_index(self) -> None:
        """
        Persist the current in-memory per-device SHA set + visual records to disk
        in the rich format, keyed by '<folder>|<adb_id>'.  MERGES with the
        existing on-disk index so records for devices that are not part of the
        current scan are preserved (not dropped).  Best-effort.
        """
        import os as _os, json as _json
        try:
            _os.makedirs(self.SS_BASE_DIR, exist_ok=True)
            # Start from whatever is already on disk, then overlay this session's
            # devices.  Unscanned devices' entries are kept as-is.
            merged = self._ss_load_hash_index()
            with self._ss_lock:
                keys = set(self._ss_hashes_by_device) | set(self._ss_records_by_device)
                for adb_id in keys:
                    folder = self._ss_folder_by_device.get(adb_id) \
                        or self._ss_sanitize(self._ss_friendly_name(adb_id))
                    key = self._ss_device_hash_key(adb_id, folder)
                    merged[key] = {
                        "sha256": sorted(self._ss_hashes_by_device.get(adb_id, set())),
                        "records": list(self._ss_records_by_device.get(adb_id, [])),
                    }
            tmp = self._ss_hash_index_path() + ".tmp"
            with open(tmp, "w", encoding="utf-8") as fh:
                _json.dump(merged, fh, indent=0)
            _os.replace(tmp, self._ss_hash_index_path())
        except Exception:
            pass

    # ── visual-hash helpers (PIL, stdlib only) ────────────────────────────────
    # Thresholds for "visually duplicate" (per device only):
    SS_AHASH_MAX = 4      # aHash hamming distance ≤ 4
    SS_DHASH_MAX = 6      # dHash hamming distance ≤ 6
    SS_SIM_MIN   = 0.995  # downscaled grayscale similarity ≥ 99.5%

    @staticmethod
    def _ss_ahash_from_png(png_bytes) -> str:
        """8x8 average hash → 16-char hex (64 bits).  '' if PIL unavailable."""
        if not _PIL_OK:
            return ""
        import io as _io
        img = Image.open(_io.BytesIO(png_bytes)).convert("L").resize((8, 8))
        px = list(img.tobytes())
        avg = sum(px) / len(px)
        bits = 0
        for i, p in enumerate(px):
            if p > avg:
                bits |= (1 << i)
        return f"{bits:016x}"

    @staticmethod
    def _ss_dhash_from_png(png_bytes) -> str:
        """9x8 difference hash → 16-char hex (64 bits).  '' if PIL unavailable."""
        if not _PIL_OK:
            return ""
        import io as _io
        img = Image.open(_io.BytesIO(png_bytes)).convert("L").resize((9, 8))
        px = list(img.tobytes())
        bits = 0; idx = 0
        for row in range(8):
            for col in range(8):
                left = px[row * 9 + col]
                right = px[row * 9 + col + 1]
                if left > right:
                    bits |= (1 << idx)
                idx += 1
        return f"{bits:016x}"

    @staticmethod
    def _ss_downscaled_signature(png_bytes) -> str:
        """
        32x18 grayscale signature as hex string (576 bytes → 1152 hex chars).
        Used for a mean-absolute-difference similarity check.  '' if no PIL.
        """
        if not _PIL_OK:
            return ""
        import io as _io
        img = Image.open(_io.BytesIO(png_bytes)).convert("L").resize((32, 18))
        return img.tobytes().hex()

    @staticmethod
    def _ss_hamming_distance(hex1: str, hex2: str) -> int:
        """Hamming distance between two equal-length hex hashes (bit count)."""
        if not hex1 or not hex2:
            return 64  # treat missing as "far"
        try:
            return bin(int(hex1, 16) ^ int(hex2, 16)).count("1")
        except Exception:
            return 64

    @staticmethod
    def _ss_downscaled_similarity(sig1: str, sig2: str) -> float:
        """1 - mean(|a-b|)/255 over the two grayscale signatures.  0.0 if bad."""
        if not sig1 or not sig2 or len(sig1) != len(sig2):
            return 0.0
        try:
            a = bytes.fromhex(sig1); b = bytes.fromhex(sig2)
        except Exception:
            return 0.0
        if not a or len(a) != len(b):
            return 0.0
        total = sum(abs(x - y) for x, y in zip(a, b))
        return 1.0 - (total / (len(a) * 255.0))

    def _ss_visual_match(self, ahash, dhash, sig, records):
        """
        Return (matched_record, reason_str) if (ahash,dhash,sig) is a visual
        duplicate of any record in `records` (same device), else (None, "").
        Pure comparison — no shared-state mutation.
        """
        for rec in records:
            ah = self._ss_hamming_distance(ahash, rec.get("ahash", ""))
            dh = self._ss_hamming_distance(dhash, rec.get("dhash", ""))
            sim = self._ss_downscaled_similarity(sig, rec.get("sig", ""))
            if ah <= self.SS_AHASH_MAX and dh <= self.SS_DHASH_MAX and sim >= self.SS_SIM_MIN:
                reason = f"visual match ahash={ah} dhash={dh} similarity={sim*100:.2f}%"
                return rec, reason
        return None, ""

    @staticmethod
    def _ss_sanitize(name: str) -> str:
        """Make a string safe for a Windows folder/file name."""
        import re as _re
        s = (name or "").strip()
        # Replace forbidden characters : \ / * ? " < > |  and control chars
        s = _re.sub(r'[:\\/*?"<>|\x00-\x1f]', "_", s)
        s = s.strip(" .")            # Windows disallows trailing space/dot
        s = _re.sub(r"\s+", " ", s)  # collapse whitespace, keep readable
        return s or "device"

    def _ss_friendly_name(self, adb_id: str) -> str:
        """
        Resolve a friendly device name with the priority:
          1. controller sheet cache (bridge.rows_by_device): friendly / name / device_name
          2. fallback to sanitized ADB id.
        """
        try:
            row = self.bridge._lookup_row(adb_id) or {}
        except Exception:
            row = {}
        nm = (row.get("friendly") or row.get("name") or row.get("device_name") or "").strip()
        if not nm:
            nm = adb_id
        return nm

    @staticmethod
    def _ss_port_suffix(adb_id: str) -> str:
        return adb_id.split(":")[-1] if ":" in adb_id else adb_id

    # ── page completion status ────────────────────────────────────────────────
    def _ss_rebuild_page_status(self):
        """
        Recompute, for each known page name, which scanned devices already have
        at least one saved screenshot for that page (by scanning the device
        folders on disk).  Then refresh the status table.  Main thread only.
        """
        status = {}
        with self._ss_lock:
            devices = [(d["adb_id"], d.get("folder") or self._ss_sanitize(d.get("friendly", d["adb_id"])),
                        d.get("friendly", d["adb_id"])) for d in self._ss_devices]
        for page in self._ss_page_names:
            done, missing = [], []
            for adb_id, folder, friendly in devices:
                if self._ss_existing_page_count(folder, friendly, page) > 0:
                    done.append(friendly)
                else:
                    missing.append(friendly)
            status[page] = {"done": done, "missing": missing, "total": len(devices)}
        self._ss_page_status = status
        self._ss_update_page_status_table()

    def _ss_update_page_status_table(self):
        """Render the page-status table from self._ss_page_status (main thread)."""
        tv = getattr(self, "_ss_page_tv", None)
        if tv is None:
            return
        try:
            tv.delete(*tv.get_children())
        except Exception:
            return
        for page in self._ss_page_names:
            info = self._ss_page_status.get(page, {"done": [], "missing": [], "total": 0})
            total = info.get("total", 0)
            ndone = len(info.get("done", []))
            nmiss = len(info.get("missing", []))
            if total == 0:
                state, tag = "—", "ss_miss"
            elif ndone == 0:
                state, tag = "missing", "ss_miss"
            elif ndone == total:
                state, tag = "done", "ss_done"
            else:
                state, tag = "partial", "ss_partial"
            label = f"{state} {ndone}/{total}" if total else state
            try:
                tv.insert("", tk.END, values=(page, ndone, nmiss, label), tags=(tag,))
            except Exception:
                pass

    # ── tab build ─────────────────────────────────────────────────────────────
    def _build_screenshotor_tab(self):
        tab = self._tab_screenshotor
        for w in tab.winfo_children():
            w.destroy()
        tab.columnconfigure(0, weight=1)
        tab.rowconfigure(3, weight=1)

        # Ensure page names are loaded once.
        if not self._ss_page_names:
            self._ss_load_page_names()

        # ── Row 0: controls ──────────────────────────────────────────────────
        ctl = tk.Frame(tab, bg=BG_MID)
        ctl.grid(row=0, column=0, sticky="ew", padx=6, pady=(6, 2))

        self._ss_start_btn = _btn(ctl, "▶ Start / Scan Devices", self._ss_start,
                                  bg=BG_CELL, fg=FG_MAIN, font=FNB, padx=8, pady=4)
        self._ss_start_btn.pack(side=tk.LEFT, padx=2)
        self._ss_stop_btn = _btn(ctl, "■ Stop", self._ss_stop,
                                 bg=BG_CELL, fg=FG_MAIN, font=FNB, padx=8, pady=4,
                                 state=tk.DISABLED)
        self._ss_stop_btn.pack(side=tk.LEFT, padx=2)
        self._ss_shot_btn = _btn(ctl, "📸 Screenshot Now (S)", self._ss_screenshot_all,
                                 bg=BG_CELL, fg=FG_MAIN, font=FNB, padx=8, pady=4,
                                 state=tk.DISABLED)
        self._ss_shot_btn.pack(side=tk.LEFT, padx=2)
        self._ss_retry_btn = _btn(ctl, "↻ Retry Failed", self._ss_retry_failed,
                                  bg=BG_CELL, fg=FG_MAIN, font=FNB, padx=8, pady=4,
                                  state=tk.DISABLED)
        self._ss_retry_btn.pack(side=tk.LEFT, padx=2)
        _btn(ctl, "📂 Open Folder", self._ss_open_folder,
             bg=BG_CELL, fg=FG_DIM, font=FS, padx=8, pady=4).pack(side=tk.LEFT, padx=2)
        _btn(ctl, "🗑 Clear List", self._ss_clear_list,
             bg=BG_CELL, fg=FG_DIM, font=FS, padx=8, pady=4).pack(side=tk.LEFT, padx=2)
        _btn(ctl, "🪟 Mini Window", self._ss_open_mini_window,
             bg=BG_CELL, fg=FG_DIM, font=FS, padx=8, pady=4).pack(side=tk.LEFT, padx=2)

        self._ss_status = tk.Label(ctl, text="Screenshotor inactive", font=FS,
                                   bg=BG_MID, fg=FG_DIM)
        self._ss_status.pack(side=tk.RIGHT, padx=10)

        # ── Row 1: page selector + add ───────────────────────────────────────
        prow = tk.Frame(tab, bg=BG_MID)
        prow.grid(row=1, column=0, sticky="ew", padx=6, pady=(0, 2))
        tk.Label(prow, text="Page:", font=FSB, bg=BG_MID, fg=FG_MAIN).pack(side=tk.LEFT, padx=(4, 4))
        self._ss_page_var = tk.StringVar(
            value=self._ss_page_names[0] if self._ss_page_names else "")
        self._ss_page_combo = ttk.Combobox(
            prow, textvariable=self._ss_page_var, state="readonly", width=22,
            values=list(self._ss_page_names) + [self.SS_ENTER_SENTINEL])
        self._ss_page_combo.pack(side=tk.LEFT, padx=2)
        self._ss_page_combo.bind("<<ComboboxSelected>>", self._ss_on_page_selected)
        tk.Label(prow, text="Enter name:", font=FS, bg=BG_MID, fg=FG_DIM).pack(side=tk.LEFT, padx=(12, 2))
        self._ss_page_entry = tk.Entry(prow, font=FS, width=18, bg=BG_CELL, fg=FG_MAIN,
                                       insertbackground=FG_MAIN)
        self._ss_page_entry.pack(side=tk.LEFT, padx=2)
        self._ss_page_entry.bind("<Return>", lambda e: self._ss_add_page_from_entry())
        _btn(prow, "Add", self._ss_add_page_from_entry, bg=BG_CELL, fg=FG_MAIN,
             font=FS, padx=8, pady=2).pack(side=tk.LEFT, padx=2)

        # ── Row 2: totals + note ─────────────────────────────────────────────
        info = tk.Frame(tab, bg=BG_BASE)
        info.grid(row=2, column=0, sticky="ew", padx=6, pady=(0, 2))
        self._ss_totals = tk.Label(
            info, text="Devices: 0 | Saved: 0 | Duplicates skipped: 0 | Failed: 0",
            font=FNB, bg=BG_BASE, fg=FG_MAIN)
        self._ss_totals.pack(side=tk.LEFT)
        tk.Label(info,
                 text="Screenshots include running devices; this may slightly slow active tasks.",
                 font=FS, bg=BG_BASE, fg=FG_DIM).pack(side=tk.RIGHT)

        # ── Row 3: device table (left) + page-status table (right) ───────────
        body = tk.Frame(tab, bg=BG_BASE)
        body.grid(row=3, column=0, sticky="nsew", padx=6, pady=(2, 6))
        body.columnconfigure(0, weight=3)
        body.columnconfigure(1, weight=1)
        body.rowconfigure(0, weight=1)

        tf = tk.LabelFrame(body, text=" Scanned Devices ", font=FSB, bg=BG_PANEL,
                           fg=FG_DIM, bd=1, relief=tk.SOLID, labelanchor="nw")
        tf.grid(row=0, column=0, sticky="nsew", padx=(0, 4))
        tf.columnconfigure(0, weight=1)
        tf.rowconfigure(0, weight=1)
        cols = ("friendly", "adb", "status", "saved", "dups", "failed", "last_path", "last_err")
        self._ss_tv = ttk.Treeview(tf, columns=cols, show="headings",
                                   style="Sheet.Treeview")
        for c, w, t, anchor in [
            ("friendly", 150, "Friendly Name", tk.W),
            ("adb", 130, "Device ID", tk.W),
            ("status", 130, "Status", tk.W),
            ("saved", 60, "Saved", tk.E),
            ("dups", 80, "Duplicates", tk.E),
            ("failed", 60, "Failed", tk.E),
            ("last_path", 320, "Last Screenshot", tk.W),
            ("last_err", 220, "Last Error", tk.W),
        ]:
            self._ss_tv.heading(c, text=t, anchor=anchor)
            self._ss_tv.column(c, width=w, minwidth=40,
                               stretch=(c in ("last_path", "last_err")), anchor=anchor)
        self._ss_tv.grid(row=0, column=0, sticky="nsew", padx=4, pady=4)
        _sb = ttk.Scrollbar(tf, orient="vertical", command=self._ss_tv.yview)
        self._ss_tv.configure(yscrollcommand=_sb.set)
        _sb.grid(row=0, column=1, sticky="ns")

        # Page-status table
        pf = tk.LabelFrame(body, text=" Page Status ", font=FSB, bg=BG_PANEL,
                           fg=FG_DIM, bd=1, relief=tk.SOLID, labelanchor="nw")
        pf.grid(row=0, column=1, sticky="nsew")
        pf.columnconfigure(0, weight=1)
        pf.rowconfigure(0, weight=1)
        pcols = ("page", "done", "missing", "state")
        self._ss_page_tv = ttk.Treeview(pf, columns=pcols, show="headings",
                                        style="Sheet.Treeview")
        for c, w, t, anchor in [
            ("page", 150, "Page", tk.W), ("done", 50, "Done", tk.E),
            ("missing", 60, "Missing", tk.E), ("state", 90, "Status", tk.W),
        ]:
            self._ss_page_tv.heading(c, text=t, anchor=anchor)
            self._ss_page_tv.column(c, width=w, minwidth=40,
                                    stretch=(c == "page"), anchor=anchor)
        # Row colour tags
        try:
            self._ss_page_tv.tag_configure("ss_done", foreground="#3fb950")
            self._ss_page_tv.tag_configure("ss_partial", foreground="#d29922")
            self._ss_page_tv.tag_configure("ss_miss", foreground="#f85149")
        except Exception:
            pass
        self._ss_page_tv.grid(row=0, column=0, sticky="nsew", padx=4, pady=4)
        _psb = ttk.Scrollbar(pf, orient="vertical", command=self._ss_page_tv.yview)
        self._ss_page_tv.configure(yscrollcommand=_psb.set)
        _psb.grid(row=0, column=1, sticky="ns")

        self._ss_update_page_status_table()

    # ── page-selector callbacks ───────────────────────────────────────────────
    def _ss_on_page_selected(self, event=None):
        """If the user picks the 'Enter name:' sentinel, focus the entry box."""
        try:
            if self._ss_page_var.get() == self.SS_ENTER_SENTINEL:
                self._ss_page_entry.focus_set()
        except Exception:
            pass

    def _ss_add_page_from_entry(self):
        """Add the typed page name (main tab) and select it."""
        try:
            name = self._ss_page_entry.get()
        except Exception:
            name = ""
        canon = self._ss_add_page_name(name)
        if canon:
            try:
                self._ss_page_var.set(canon)
                self._ss_page_entry.delete(0, tk.END)
            except Exception:
                pass
            self._ss_rebuild_page_status()
            self._ss_set_status(f"Page '{canon}' ready.")

    # ── status / table helpers (main thread only) ────────────────────────────
    def _ss_set_status(self, text: str):
        try:
            self._ss_status.configure(text=text)
        except Exception:
            pass
        # Mirror to the mini window if open
        try:
            if self._ss_mini_window is not None and self._ss_mini_lbl is not None:
                self._ss_mini_lbl.configure(text=self._ss_mini_summary())
        except Exception:
            pass

    def _ss_mini_summary(self) -> str:
        tot = self._ss_totals_dict()
        n = len(self._ss_devices)
        page = self._ss_selected_page_name() or "—"
        cur_failed = sum(1 for st in self._ss_stats.values()
                         if st.get("last_status") == "failed")
        # Compact: "7 dev | game main map | saved 14 | failed 0"
        return f"{n} dev | {page} | saved {tot['saved']} | failed {cur_failed}"

    def _ss_totals_dict(self) -> dict:
        with self._ss_lock:
            stats = list(self._ss_stats.values())
        saved = sum(s.get("saved", 0) for s in stats)
        dups  = sum(s.get("duplicates", 0) for s in stats)
        failed = sum(s.get("failed", 0) for s in stats)
        return {"saved": saved, "dups": dups, "failed": failed}

    def _ss_refresh_totals(self):
        tot = self._ss_totals_dict()
        try:
            self._ss_totals.configure(
                text=(f"Devices: {len(self._ss_devices)} | Saved: {tot['saved']} | "
                      f"Duplicates skipped: {tot['dups']} | Failed: {tot['failed']}"))
        except Exception:
            pass
        try:
            if self._ss_mini_window is not None and self._ss_mini_lbl is not None:
                self._ss_mini_lbl.configure(text=self._ss_mini_summary())
        except Exception:
            pass

    def _ss_rebuild_table(self):
        """Rebuild the whole device table from _ss_stats (main thread)."""
        try:
            self._ss_tv.delete(*self._ss_tv.get_children())
        except Exception:
            return
        with self._ss_lock:
            devices = list(self._ss_devices)
            stats = {k: dict(v) for k, v in self._ss_stats.items()}
        for d in devices:
            adb_id = d["adb_id"]
            st = stats.get(adb_id, {})
            self._ss_tv.insert("", tk.END, iid=adb_id, values=(
                st.get("friendly", d.get("friendly", adb_id)),
                adb_id,
                st.get("last_status", "scanned"),
                st.get("saved", 0),
                st.get("duplicates", 0),
                st.get("failed", 0),
                st.get("last_path", ""),
                st.get("last_error", ""),
            ))
        self._ss_refresh_totals()

    def _ss_apply_device_update(self, adb_id: str):
        """Update a single row from _ss_stats (main thread, via queue)."""
        with self._ss_lock:
            st = self._ss_stats.get(adb_id)
            st = dict(st) if st else None
        if not st:
            return
        vals = (
            st.get("friendly", adb_id), adb_id, st.get("last_status", ""),
            st.get("saved", 0), st.get("duplicates", 0), st.get("failed", 0),
            st.get("last_path", ""), st.get("last_error", ""),
        )
        try:
            if self._ss_tv.exists(adb_id):
                self._ss_tv.item(adb_id, values=vals)
            else:
                self._ss_tv.insert("", tk.END, iid=adb_id, values=vals)
        except Exception:
            pass
        self._ss_refresh_totals()

    # ── Start / scan ──────────────────────────────────────────────────────────
    def _ss_start(self):
        """Scan currently-open devices ONCE, reset session, set active."""
        # 4: block re-scan while already active or busy.
        if self._ss_active:
            self._ss_set_status("Stop first before scanning again.")
            return
        if self._ss_busy:
            self._ss_set_status("busy — screenshot batch in progress")
            return
        if self._ss_scanning:
            self._ss_set_status("scan already in progress")
            return
        # New session — invalidate any late results from a prior batch/scan worker.
        self._ss_session_id += 1
        session_id = self._ss_session_id   # tag this scan's result
        self._ss_scanning = True
        self._ss_set_status("scanning devices…")
        try:
            self._ss_start_btn.configure(state=tk.DISABLED)
        except Exception:
            pass

        def _worker():
            try:
                devices = self._ss_scan_open_devices()
                # Hand the scan result back to the main thread via the queue —
                # NEVER touch Tk (or self.after) from a background thread.
                self.q.put(("ss_scan_done", session_id, devices))
            except Exception as exc:
                self.q.put(("ss_scan_done", session_id, {"__error__": str(exc)}))
        threading.Thread(target=_worker, daemon=True).start()

    def _ss_normalize_adb_id(self, adb_id: str) -> str:
        """
        Normalize an ADB id to the controller's `localhost:<port>` style so
        friendly-name lookup against bridge.rows_by_device matches.
        `127.0.0.1:5555` → `localhost:5555`; `emulator-5554` → `localhost:5554`.
        Anything else is returned unchanged.
        """
        a = (adb_id or "").strip()
        if a.startswith("127.0.0.1:"):
            return "localhost:" + a.split(":", 1)[1]
        if a.startswith("emulator-"):
            return "localhost:" + a.split("-", 1)[1]
        return a

    def _ss_scan_open_devices(self) -> list:
        """
        Discover online devices for the Screenshotor.

        Delegates to the shared optimised scan core (`_scan_online_bluestacks_devices`,
        fast mode) rather than probing every configured instance. That core does
        one netstat sweep and one `adb devices` call, then only `adb connect`s and
        `get-state`s ports that are actually LISTENING or already known to ADB —
        so with ~190 configured instances and two windows open it touches two
        ports instead of 190.

        This function used to carry its own full copy of the old slow scan, which
        meant fixing the Run/Test path left the Screenshotor just as slow. Having
        one implementation is the point: any future scan improvement lands here
        automatically.

        Does NOT launch/close emulators and does NOT touch _running_devs / run
        queue / cache / sheets. Runs in the scan worker thread.

        Returns [{adb_id, friendly}] — the Screenshotor's format.
        """
        import time as _time

        t0 = _time.time()
        try:
            devs = self._scan_online_bluestacks_devices(
                log_fn=lambda msg, tag="dim": self.q.put(("ss_status", msg)),
                deep=False,
            )
        except Exception as exc:
            self.q.put(("ss_status", f"scan error: {exc}"))
            _multi_log.error(f"[SCREENSHOT] scan failed: {exc!r}")
            return []

        # Convert the core's richer dicts to the Screenshotor's shape.
        out = [{"adb_id": d["adb_id"],
                "friendly": d.get("friendly") or d.get("name") or d["adb_id"]}
               for d in devs]

        total = _time.time() - t0
        _multi_log.info(
            f"[SCREENSHOT] scan done devices={len(out)} total={total:.2f}s "
            f"(shared fast scan core)"
        )
        # Empty result is handled by the caller, which disables the screenshot
        # controls and shows "no open devices found — nothing to screenshot".
        return out

    def _ss_finish_start(self, devices):
        """Main thread (via ss_scan_done queue event): install scanned devices,
        reset session, activate.  Only reached for the current session (the
        _poll handler drops stale ss_scan_done before calling this)."""
        self._ss_scanning = False   # scan finished for the current session
        try:
            self._ss_start_btn.configure(state=tk.NORMAL)
        except Exception:
            pass

        # Worker reports a scan error as {"__error__": msg}
        if isinstance(devices, dict) and "__error__" in devices:
            self._ss_active = False
            try:
                self._ss_stop_btn.configure(state=tk.DISABLED)
                self._ss_shot_btn.configure(state=tk.DISABLED)
            except Exception:
                pass
            self._ss_set_status(f"scan error: {devices['__error__']}")
            return

        if not devices:
            # 8: no devices → stay inactive, screenshot button disabled.
            self._ss_active = False
            try:
                self._ss_stop_btn.configure(state=tk.DISABLED)
                self._ss_shot_btn.configure(state=tk.DISABLED)
            except Exception:
                pass
            self._ss_set_status("no open devices found — nothing to screenshot")
            _multi_log.info("[SCREENSHOT] scanned 0 devices")
            return

        # Assign collision-safe friendly folder names within this scan
        seen_folders: dict[str, int] = {}
        stats = {}
        folder_by_device = {}
        for d in devices:
            adb_id = d["adb_id"]
            base = self._ss_sanitize(d["friendly"])
            # If friendly name blank/duplicate, append port for uniqueness
            folder = base
            if folder in seen_folders or base == "device":
                folder = f"{base}_{self._ss_port_suffix(adb_id)}"
            seen_folders[folder] = seen_folders.get(folder, 0) + 1
            d["folder"] = folder
            folder_by_device[adb_id] = folder
            stats[adb_id] = {
                "friendly": d["friendly"], "adb_id": adb_id, "folder": folder,
                "saved": 0, "duplicates": 0, "failed": 0,
                "last_path": "", "last_error": "", "last_status": "scanned",
            }

        # Seed the in-memory per-device hash cache + visual records from the
        # PERSISTENT index so duplicate detection survives Stop/Start and
        # controller restarts.
        persisted = self._ss_load_hash_index()
        hashes = {}
        records = {}
        for adb_id, folder in folder_by_device.items():
            key = self._ss_device_hash_key(adb_id, folder)
            entry = persisted.get(key, {})
            hashes[adb_id] = set(entry.get("sha256", []))
            records[adb_id] = list(entry.get("records", []))

        # Reset session under the lock.  Stats are fresh each Start; the hash
        # cache + records are seeded from disk (NOT cleared) so they persist.
        with self._ss_lock:
            self._ss_devices = devices
            self._ss_stats = stats
            self._ss_folder_by_device = folder_by_device
            self._ss_hashes_by_device = hashes
            self._ss_records_by_device = records
            self._ss_last_hash_by_device = {}
        # Fresh session — clear any prior cancellation.
        self._ss_stop_event.clear()

        self._ss_active = True
        try:
            self._ss_stop_btn.configure(state=tk.NORMAL)
            self._ss_shot_btn.configure(state=tk.NORMAL)
        except Exception:
            pass
        self._ss_rebuild_table()
        self._ss_rebuild_page_status()
        self._ss_refresh_retry_button()
        self._ss_set_status(f"Scanned {len(devices)} devices")
        _multi_log.info(f"[SCREENSHOT] scanned {len(devices)} devices")
        _multi_log.info("[SCREENSHOT] active=True")

    # ── Stop / clear ────────────────────────────────────────────────────────
    def _ss_stop(self):
        self._ss_active = False
        # 3: cancel any in-flight batch between devices.
        self._ss_stop_event.set()
        # Invalidate any late results from the active batch/scan worker.
        self._ss_session_id += 1
        # An in-flight scan is now stale and will be ignored, so clear the flag
        # here and re-enable Start so the user can scan again.
        self._ss_scanning = False
        # The in-flight screenshot batch (if any) is now invalidated by the
        # session bump and its ss_batch_done will be ignored, so clear busy here
        # — otherwise Start would stay blocked with "busy" forever.
        self._ss_busy = False
        try:
            self._ss_start_btn.configure(state=tk.NORMAL)
            self._ss_stop_btn.configure(state=tk.DISABLED)
            self._ss_shot_btn.configure(state=tk.DISABLED)
            if self._ss_retry_btn is not None:
                self._ss_retry_btn.configure(state=tk.DISABLED)
        except Exception:
            pass
        self._ss_set_status("Stopped")
        _multi_log.info("[SCREENSHOT] stopped")

    def _ss_clear_list(self):
        self._ss_active = False
        self._ss_stop_event.set()   # also cancel any in-flight batch
        # Invalidate any late results so a stale row cannot reappear after clear.
        self._ss_session_id += 1
        # In-flight scan is now stale and will be ignored — clear the flag.
        self._ss_scanning = False
        # In-flight screenshot batch is invalidated by the session bump; clear
        # busy so Start is not blocked with "busy" after the batch is discarded.
        self._ss_busy = False
        with self._ss_lock:
            self._ss_devices = []
            self._ss_stats = {}
            self._ss_hashes_by_device = {}
            self._ss_records_by_device = {}
            self._ss_last_hash_by_device = {}
        try:
            self._ss_tv.delete(*self._ss_tv.get_children())
            self._ss_start_btn.configure(state=tk.NORMAL)
            self._ss_stop_btn.configure(state=tk.DISABLED)
            self._ss_shot_btn.configure(state=tk.DISABLED)
            if self._ss_retry_btn is not None:
                self._ss_retry_btn.configure(state=tk.DISABLED)
        except Exception:
            pass
        self._ss_refresh_totals()
        # Page-name list is preserved; just clear the per-device status display.
        self._ss_page_status = {}
        self._ss_update_page_status_table()
        self._ss_set_status("Screenshotor inactive")
        _multi_log.info("[SCREENSHOT] list cleared")

    # ── hotkey ────────────────────────────────────────────────────────────────
    def _ss_hotkey_screenshot(self, event):
        # Do not trigger while typing in an entry/text/combobox widget.
        widget = getattr(event, "widget", None)
        try:
            if isinstance(widget, (tk.Entry, tk.Text, ttk.Combobox, ttk.Entry,
                                   tk.Spinbox)):
                return
        except Exception:
            pass
        # ttk.Combobox sometimes reports class name only
        try:
            cls = widget.winfo_class() if widget is not None else ""
            if cls in ("TEntry", "Entry", "Text", "TCombobox", "TSpinbox", "Spinbox"):
                return
        except Exception:
            pass
        # Use the mini-window page if the key came from the mini window.
        from_mini = False
        try:
            if widget is not None and self._ss_mini_window is not None:
                from_mini = (widget.winfo_toplevel() is self._ss_mini_window)
        except Exception:
            from_mini = False
        self._ss_screenshot_all(mini=from_mini)

    # ── screenshot batch ──────────────────────────────────────────────────────
    def _ss_failed_devices(self):
        """Devices whose CURRENT status is failed (eligible for Retry Failed)."""
        failed = []
        with self._ss_lock:
            for d in self._ss_devices:
                st = self._ss_stats.get(d["adb_id"], {})
                if st.get("last_status") == "failed":
                    failed.append(dict(d))
        return failed

    def _ss_retry_failed(self):
        """Re-screenshot only the devices whose current status is failed."""
        if not self._ss_active:
            self._ss_set_status("Click Start first.")
            return
        failed_devices = self._ss_failed_devices()
        if not failed_devices:
            self._ss_set_status("No failed devices to retry.")
            self._ss_refresh_retry_button()
            return
        self._ss_set_status(f"Retrying {len(failed_devices)} failed device(s)…")
        _multi_log.info(f"[SCREENSHOT] retry-failed for {len(failed_devices)} device(s)")
        self._ss_screenshot_all(devices_override=failed_devices, retry_failed=True)

    def _ss_refresh_retry_button(self):
        """Enable Retry Failed (main + mini) only when ≥1 device is currently failed."""
        try:
            has_failed = any(
                st.get("last_status") == "failed" for st in self._ss_stats.values())
            state = (tk.NORMAL if (self._ss_active and has_failed) else tk.DISABLED)
        except Exception:
            return
        for attr in ("_ss_retry_btn", "_ss_mini_retry_btn"):
            btn = getattr(self, attr, None)
            if btn is not None:
                try:
                    btn.configure(state=state)
                except Exception:
                    pass

    def _ss_screenshot_all(self, mini=False, devices_override=None, retry_failed=False):
        if not self._ss_active or not self._ss_devices:
            self._ss_set_status("Click Start first.")
            return
        # Page name is required for tagging the filename.
        page = self._ss_selected_page_name(mini=mini)
        if not page:
            # try the other selector as a fallback before warning
            page = self._ss_selected_page_name(mini=not mini)
        if not page:
            self._ss_set_status("Select or enter a page name first.")
            try:
                if self._ss_mini_window is not None and self._ss_mini_lbl is not None:
                    self._ss_mini_lbl.configure(text="Select a page name first.")
            except Exception:
                pass
            return
        if self._ss_busy:
            self._ss_set_status("busy — previous batch still running")
            return
        self._ss_busy = True
        session_id = self._ss_session_id   # tag this batch's results
        with self._ss_lock:
            if devices_override is not None:
                # Retry-failed subset: snapshot only the requested devices that
                # are still part of the current scanned set.
                want = {d["adb_id"] for d in devices_override}
                devices = [dict(d) for d in self._ss_devices if d["adb_id"] in want]
            else:
                devices = list(self._ss_devices)   # snapshot for the thread
        if not devices:
            self._ss_busy = False
            self._ss_set_status("No devices to screenshot.")
            return

        def _worker():
            import hashlib, os as _os, time as _time
            from datetime import datetime as _dt
            from concurrent.futures import ThreadPoolExecutor, as_completed
            stamp = _dt.now().strftime("%Y%m%d_%H%M%S")
            cancelled = False
            _t_batch = _time.time()
            _multi_log.info(
                f"[SCREENSHOT] batch started devices={len(devices)} page={page!r} "
                f"{'(retry-failed) ' if retry_failed else ''}(parallel, "
                f"retries={self.SS_CAPTURE_RETRIES})")

            # Cancel cleanly if Stop/Clear/new-session happened before submit.
            if self._ss_stop_event.is_set() or session_id != self._ss_session_id:
                self.q.put(("ss_batch_done", session_id,
                            {"cancelled": True}))
                return

            def _capture(d):
                # Capture ONLY: bytes + sha + visual hashes, with up to
                # SS_CAPTURE_RETRIES attempts per device (parallel across devices).
                # The final filename (per-device+page numbering) is decided on the
                # main thread in _ss_on_device_result.
                adb_id = d["adb_id"]
                folder = d.get("folder") or self._ss_sanitize(d.get("friendly", adb_id))
                friendly = d.get("friendly", adb_id)
                outcome = "captured"; sha = ""; err = ""; png = None
                ahash = ""; dhash = ""; sig = ""
                cap = self._ss_capture_one_with_retry(adb_id, session_id=session_id)
                attempts_used = cap.get("attempts_used", 0)
                if cap.get("cancelled"):
                    outcome = "cancelled"; err = "cancelled"
                elif cap.get("ok") and cap.get("png"):
                    try:
                        png = cap["png"]
                        sha = hashlib.sha256(png).hexdigest()
                        ahash = self._ss_ahash_from_png(png)
                        dhash = self._ss_dhash_from_png(png)
                        sig   = self._ss_downscaled_signature(png)
                    except Exception as exc:
                        outcome = "failed"; err = str(exc)[:200]; png = None
                else:
                    outcome = "failed"; err = cap.get("error", "capture failed")[:200]; png = None
                return {
                    "adb_id": adb_id, "friendly": friendly, "folder": folder,
                    "sha": sha, "png": png, "page": page,
                    "ahash": ahash, "dhash": dhash, "sig": sig,
                    "outcome": outcome, "error": err, "stamp": stamp,
                    "attempts_used": attempts_used,
                    "max_attempts": self.SS_CAPTURE_RETRIES,
                }

            max_workers = min(len(devices), 12) or 1
            _multi_log.info(
                f"[SCREENSHOT] capture submit devices={len(devices)} workers={max_workers}")
            with ThreadPoolExecutor(max_workers=max_workers) as pool:
                futs = {pool.submit(_capture, d): d for d in devices}
                for fut in as_completed(futs):
                    # As results finish, stop processing if cancelled / superseded.
                    if self._ss_stop_event.is_set() or session_id != self._ss_session_id:
                        cancelled = True
                        _multi_log.info("[SCREENSHOT] batch cancelled (stop/new session)")
                        break
                    try:
                        result = fut.result()
                    except Exception as exc:
                        # A capture worker should not raise (it catches), but guard.
                        d = futs[fut]
                        result = {"adb_id": d["adb_id"],
                                  "friendly": d.get("friendly", d["adb_id"]),
                                  "folder": d.get("folder", ""), "sha": "", "png": None,
                                  "page": page, "outcome": "failed",
                                  "error": str(exc)[:200], "stamp": stamp,
                                  "attempts_used": self.SS_CAPTURE_RETRIES,
                                  "max_attempts": self.SS_CAPTURE_RETRIES}
                    # Main thread applies save/duplicate/stats (session-guarded).
                    self.q.put(("ss_device_result", session_id, result))

            _cap_secs = _time.time() - _t_batch
            _multi_log.info(
                f"[SCREENSHOT] batch capture phase done in {_cap_secs:.2f}s "
                f"cancelled={cancelled}")
            self.q.put(("ss_batch_done", session_id,
                        {"cancelled": cancelled, "page": page,
                         "capture_secs": round(_cap_secs, 2),
                         "batch_started": _t_batch}))

        threading.Thread(target=_worker, daemon=True).start()

    def _ss_on_device_result(self, session_id: int, result: dict):
        """
        Main-thread application of one captured device result.

        ALL shared-state mutation lives here (not in the worker): duplicate check,
        hash-set update, file save, and _ss_stats/table update.  Guarded by
        session id — a late result from a stopped/cleared/restarted session is
        dropped before it can mutate any state or write a file.
        """
        # Stale result (Stop / Clear / new Start happened) — drop entirely.
        if session_id != self._ss_session_id:
            return

        import os as _os
        adb_id   = result.get("adb_id", "")
        friendly = result.get("friendly", adb_id)
        folder   = result.get("folder") or self._ss_sanitize(friendly or adb_id)
        outcome  = result.get("outcome", "failed")
        sha      = result.get("sha", "")
        png      = result.get("png")
        page     = result.get("page", "")
        err      = result.get("error", "")
        ahash    = result.get("ahash", "")
        dhash    = result.get("dhash", "")
        sig      = result.get("sig", "")
        attempts_used = result.get("attempts_used", 0)
        max_attempts  = result.get("max_attempts", self.SS_CAPTURE_RETRIES)

        st = self._ss_stats.setdefault(adb_id, {
            "friendly": friendly, "adb_id": adb_id, "folder": folder,
            "saved": 0, "duplicates": 0, "failed": 0,
            "last_path": "", "last_error": "", "last_status": ""})

        # Cancelled result (Stop mid-batch): do not count as a failure, leave the
        # prior status intact so Retry Failed eligibility is unchanged.
        if outcome == "cancelled":
            self._ss_apply_device_update(adb_id)
            self._ss_refresh_retry_button()
            return

        if outcome == "failed" or not png or not sha:
            st["failed"] += 1
            st["last_status"] = "failed"
            st["last_error"] = (err or "capture failed")[:200]
            st["last_attempts"] = attempts_used or max_attempts
            _multi_log.info(
                f"[SCREENSHOT] {friendly} {adb_id} failed after "
                f"{attempts_used or max_attempts} attempts: {st['last_error']}")
            self._ss_apply_device_update(adb_id)
            self._ss_refresh_retry_button()
            return

        seen = self._ss_hashes_by_device.setdefault(adb_id, set())
        records = self._ss_records_by_device.setdefault(adb_id, [])

        # 1) Exact SHA-256 match (per device) → duplicate.  (Per-device, not
        # per-page; the selected page is logged so the user knows what was skipped.)
        if sha in seen:
            st["duplicates"] += 1
            st["last_status"] = f"duplicate skipped: sha exact (page {page})"
            st["last_error"] = ""
            _multi_log.info(
                f"[SCREENSHOT] duplicate skipped: sha exact {friendly} {adb_id} "
                f"page={page!r} hash={sha[:12]}")
            self._ss_apply_device_update(adb_id)
            self._ss_refresh_retry_button()
            return

        # 2) Visual match against this device's records (per device only).
        match_rec, reason = self._ss_visual_match(ahash, dhash, sig, records)
        if match_rec is not None:
            st["duplicates"] += 1
            st["last_status"] = f"duplicate skipped: {reason} (page {page})"
            st["last_error"] = ""
            # Record the new exact SHA so an identical future frame is caught fast,
            # but do NOT save the file (it is a visual duplicate).
            seen.add(sha)
            self._ss_folder_by_device[adb_id] = folder
            self._ss_index_dirty = True   # persist once at batch end
            _multi_log.info(
                f"[SCREENSHOT] duplicate skipped: {reason} {friendly} {adb_id} page={page!r}")
            self._ss_apply_device_update(adb_id)
            self._ss_refresh_retry_button()
            return

        # 3) New (not exact, not visual) — save with per-(device,page) numbering:
        #    screenshots/<folder>/<device>_<page>_<NNN>.png  (no batch timestamp folder).
        path = self._ss_next_page_filename(folder, friendly, page)
        try:
            _os.makedirs(_os.path.dirname(path), exist_ok=True)
            with open(path, "wb") as fh:
                fh.write(png)
        except Exception as exc:
            st["failed"] += 1
            st["last_status"] = "failed"
            st["last_error"] = f"save failed: {exc}"[:200]
            _multi_log.info(f"[SCREENSHOT] {friendly} {adb_id} save failed: {exc}")
            self._ss_apply_device_update(adb_id)
            self._ss_refresh_retry_button()
            return

        seen.add(sha)
        self._ss_last_hash_by_device[adb_id] = sha
        # Append the visual record (now including the page name) for future
        # visual-duplicate comparison.
        records.append({
            "sha256": sha, "ahash": ahash, "dhash": dhash, "sig": sig,
            "path": path, "page": page, "saved_at": result.get("stamp", ""),
        })
        # Keep the folder map current so the persistent index is keyed correctly.
        self._ss_folder_by_device[adb_id] = folder
        st["saved"] += 1
        st["last_path"] = path
        if attempts_used and attempts_used > 1:
            st["last_status"] = f"saved after {attempts_used} attempts ({page})"
        else:
            st["last_status"] = f"saved ({page})"
        st["last_error"] = ""
        _multi_log.info(f"[SCREENSHOT] {friendly} {adb_id} saved {path} hash={sha[:12]}")
        # Defer the (relatively expensive) hash-index write and page-status
        # rebuild to the END of the batch so a large device set does not feel
        # one-by-one.  The row itself is updated immediately below.
        self._ss_index_dirty = True
        self._ss_page_status_dirty = True
        self._ss_apply_device_update(adb_id)
        self._ss_refresh_retry_button()

    def _ss_capture_one(self, adb_id: str) -> bytes:
        """
        Capture one device screenshot via `adb -s <id> exec-out screencap -p`.
        Returns raw PNG bytes (no tap/click/swipe/OCR).  Raises on failure.
        """
        proc = subprocess.run(
            ["adb", "-s", adb_id, "exec-out", "screencap", "-p"],
            capture_output=True, timeout=self.SS_CAPTURE_TIMEOUT,
        )
        if proc.returncode != 0:
            err = (proc.stderr or b"").decode("utf-8", "replace").strip()
            raise RuntimeError(f"adb screencap failed (rc={proc.returncode}) {err}")
        data = proc.stdout or b""
        _PNG_SIG = b"\x89PNG\r\n\x1a\n"
        # Validate the full 8-byte PNG signature.  Some legacy `screencap`
        # transports translate LF→CRLF; exec-out avoids it, but repair anyway.
        if not data.startswith(_PNG_SIG):
            repaired = data.replace(b"\r\n", b"\n")
            if repaired.startswith(_PNG_SIG):
                data = repaired
            else:
                raise RuntimeError("screencap output is not a valid PNG")
        # Reject empty/partial captures (a real frame is well over a few KB).
        if len(data) < 1024:
            raise RuntimeError(f"screencap output too small ({len(data)} bytes)")
        return data

    def _ss_capture_one_with_retry(self, adb_id, session_id=None, attempts=None):
        """
        Capture one device screenshot with up to `attempts` tries (default
        SS_CAPTURE_RETRIES).  ADB/emulator can briefly lag or drop the transport,
        so a single screencap failure should not immediately fail the device.

        Between failed attempts, if the device is not in state 'device', a quiet
        `adb connect` is attempted (reconnect only — never launches/closes the
        emulator and never taps/clicks/swipes).  Honours the Stop event so a
        cancelled batch returns promptly.  Returns a dict:
          {ok, png, attempts_used, error, cancelled}
        Safe to call from the parallel capture worker (no shared-state mutation).
        """
        if attempts is None:
            attempts = self.SS_CAPTURE_RETRIES
        last_error = ""
        for attempt in range(1, attempts + 1):
            # Cancel promptly if Stop / new session happened.
            if self._ss_stop_event.is_set() or (
                    session_id is not None and session_id != self._ss_session_id):
                return {"ok": False, "cancelled": True,
                        "attempts_used": attempt - 1 if attempt > 1 else 0,
                        "error": "cancelled", "png": None}
            try:
                _multi_log.info(f"[SCREENSHOT] {adb_id} capture attempt {attempt}/{attempts}")
                png = self._ss_capture_one(adb_id)
                if png:
                    if attempt > 1:
                        _multi_log.info(
                            f"[SCREENSHOT] {adb_id} capture succeeded attempt {attempt}/{attempts}")
                    return {"ok": True, "png": png, "attempts_used": attempt,
                            "error": "", "cancelled": False}
                last_error = "adb screencap returned no data"
            except Exception as exc:
                last_error = str(exc)
            _multi_log.info(
                f"[SCREENSHOT] {adb_id} capture failed attempt {attempt}/{attempts}: "
                f"{last_error[:160]}")
            # Optional reconnect (screencap/connect only) before the next try.
            if attempt < attempts:
                try:
                    state = ""
                    try:
                        chk = subprocess.run(["adb", "-s", adb_id, "get-state"],
                                             capture_output=True, text=True,
                                             timeout=self.SS_SCAN_STATE_TIMEOUT)
                        state = (chk.stdout or "").strip()
                    except Exception:
                        state = ""
                    if state != "device":
                        _adb_connect_quiet(adb_id)
                except Exception:
                    pass
                # Interruptible delay so Stop is responsive between attempts.
                if self._ss_stop_event.wait(self.SS_CAPTURE_RETRY_DELAY):
                    return {"ok": False, "cancelled": True,
                            "attempts_used": attempt, "error": "cancelled", "png": None}
        _multi_log.info(
            f"[SCREENSHOT] {adb_id} capture failed after {attempts} attempts")
        return {"ok": False, "cancelled": False, "attempts_used": attempts,
                "error": last_error or "capture failed", "png": None}

    def _ss_on_batch_done(self, summary: dict):
        import time as _time
        self._ss_busy = False
        # ── Save/hash phase (deferred work flushed once per batch) ──
        _t_save = _time.time()
        if getattr(self, "_ss_index_dirty", False):
            try:
                self._ss_save_hash_index()
            except Exception:
                pass
            self._ss_index_dirty = False
        if getattr(self, "_ss_page_status_dirty", False):
            try:
                self._ss_rebuild_page_status()
            except Exception:
                pass
            self._ss_page_status_dirty = False
        _save_secs = _time.time() - _t_save
        self._ss_rebuild_table()
        # Totals are recomputed from the main-thread-applied _ss_stats for the
        # current session (the worker no longer carries counts).
        tot = self._ss_totals_dict()
        cur_failed = sum(1 for st in self._ss_stats.values()
                         if st.get("last_status") == "failed")
        cancelled = summary.get("cancelled")
        folder = summary.get("folder") or self.SS_BASE_DIR
        cap_secs = summary.get("capture_secs")
        started = summary.get("batch_started")
        total_secs = (_time.time() - started) if started else None
        fail_txt = f"failed devices={cur_failed}" + (
            f" (events={tot['failed']})" if tot['failed'] != cur_failed else "")
        if cancelled:
            msg = (f"Screenshot batch cancelled (saved={tot['saved']} "
                   f"duplicate={tot['dups']} {fail_txt})")
        else:
            msg = (f"Screenshot batch complete: saved={tot['saved']} "
                   f"duplicate={tot['dups']} {fail_txt}")
        self._ss_set_status(msg)
        self._ss_refresh_retry_button()
        _multi_log.info(f"[SCREENSHOT] batch save/hash phase done in {_save_secs:.2f}s")
        if total_secs is not None:
            _multi_log.info(
                f"[SCREENSHOT] batch done total={total_secs:.2f}s "
                f"(capture={cap_secs}s save={_save_secs:.2f}s) "
                f"saved={tot['saved']} duplicate={tot['dups']} failed={cur_failed}")
        self._log(
            f"[SCREENSHOT] batch {'cancelled' if cancelled else 'complete'}: "
            f"saved={tot['saved']} duplicate={tot['dups']} "
            f"failed={tot['failed']} folder={folder}", "dim")

    # ── open folder ───────────────────────────────────────────────────────────
    def _ss_open_folder(self):
        import os as _os
        path = _os.path.abspath(self.SS_BASE_DIR)
        try:
            _os.makedirs(path, exist_ok=True)
        except Exception:
            pass
        try:
            if hasattr(_os, "startfile"):
                _os.startfile(path)            # Windows only
            else:
                self._ss_set_status(f"Folder: {path} (open not supported on this OS)")
        except Exception as exc:
            self._ss_set_status(f"could not open folder: {exc}")

    # ── floating mini window ────────────────────────────────────────────────
    def _ss_open_mini_window(self):
        # If it already exists, just bring it to front.
        if self._ss_mini_window is not None:
            try:
                self._ss_mini_window.deiconify()
                self._ss_mini_window.lift()
                self._ss_mini_window.focus_force()
                return
            except Exception:
                self._ss_mini_window = None

        if not self._ss_page_names:
            self._ss_load_page_names()

        win = tk.Toplevel(self)
        win.title("📸 Screenshotor")
        win.configure(bg=BG_BASE)
        win.geometry("280x150")
        win.minsize(220, 120)
        try:
            win.attributes("-topmost", True)
        except Exception:
            pass

        def _on_mini_close():
            try:
                win.destroy()
            except Exception:
                pass
            self._ss_mini_window = None
            self._ss_mini_lbl = None
            # Do NOT clear _ss_page_var — it is the shared selection var.
            self._ss_mini_page_var = None
            self._ss_mini_page_combo = None
            self._ss_mini_retry_btn = None
        win.protocol("WM_DELETE_WINDOW", _on_mini_close)

        # Scroll support: a Canvas + inner frame keeps controls reachable when
        # the window is shrunk.
        outer = tk.Frame(win, bg=BG_BASE)
        outer.pack(fill=tk.BOTH, expand=True)
        canvas = tk.Canvas(outer, bg=BG_BASE, highlightthickness=0)
        vsb = ttk.Scrollbar(outer, orient="vertical", command=canvas.yview)
        canvas.configure(yscrollcommand=vsb.set)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        body = tk.Frame(canvas, bg=BG_BASE)
        body_id = canvas.create_window((0, 0), window=body, anchor="nw")
        def _on_cfg(event):
            canvas.configure(scrollregion=canvas.bbox("all"))
            try:
                canvas.itemconfigure(body_id, width=canvas.winfo_width())
            except Exception:
                pass
        body.bind("<Configure>", _on_cfg)
        canvas.bind("<Configure>",
                    lambda e: canvas.itemconfigure(body_id, width=e.width))

        # Page selector (compact) + '+' to add a new page via small dialog.
        # Uses the SHARED _ss_page_var so the main tab and mini window always
        # reflect the same selection (no sync callbacks / no recursion).
        prow = tk.Frame(body, bg=BG_BASE)
        prow.pack(fill=tk.X, padx=6, pady=(8, 2))
        tk.Label(prow, text="Page:", font=FS, bg=BG_BASE, fg=FG_MAIN).pack(side=tk.LEFT)
        if self._ss_page_var is None:
            self._ss_page_var = tk.StringVar(
                value=self._ss_page_names[0] if self._ss_page_names else "")
        # Alias kept for backward-compat with existing references.
        self._ss_mini_page_var = self._ss_page_var
        self._ss_mini_page_combo = ttk.Combobox(
            prow, textvariable=self._ss_page_var, state="readonly", width=16,
            values=list(self._ss_page_names) + [self.SS_ENTER_SENTINEL])
        self._ss_mini_page_combo.pack(side=tk.LEFT, padx=(4, 2), fill=tk.X, expand=True)
        self._ss_mini_page_combo.bind("<<ComboboxSelected>>", self._ss_mini_on_page_selected)
        _btn(prow, "+", self._ss_mini_add_page_dialog, bg=BG_CELL, fg=FG_MAIN,
             font=FS, padx=6, pady=1).pack(side=tk.LEFT, padx=2)

        btns = tk.Frame(body, bg=BG_BASE)
        btns.pack(fill=tk.X, padx=6, pady=(2, 4))
        _btn(btns, "▶", self._ss_start, bg=BG_CELL, fg=FG_MAIN, font=FNB,
             padx=8, pady=3).pack(side=tk.LEFT, padx=2)
        _btn(btns, "■", self._ss_stop, bg=BG_CELL, fg=FG_MAIN, font=FNB,
             padx=8, pady=3).pack(side=tk.LEFT, padx=2)
        # Icon-only camera button (keeps the window narrow).
        _btn(btns, "📸", lambda: self._ss_screenshot_all(mini=True), bg=BG_CELL,
             fg=FG_MAIN, font=FNB, padx=8, pady=3).pack(side=tk.LEFT, padx=2)
        # Compact Retry Failed (same logic as the main tab button).
        self._ss_mini_retry_btn = _btn(btns, "↻", self._ss_retry_failed, bg=BG_CELL,
                                       fg=FG_MAIN, font=FNB, padx=8, pady=3,
                                       state=tk.DISABLED)
        self._ss_mini_retry_btn.pack(side=tk.LEFT, padx=2)

        self._ss_mini_lbl = tk.Label(body, text=self._ss_mini_summary(),
                                     font=FS, bg=BG_BASE, fg=FG_DIM, wraplength=250,
                                     justify=tk.LEFT)
        self._ss_mini_lbl.pack(fill=tk.X, padx=8, pady=(2, 6))

        # S while mini window focused → screenshot (guarded against entries)
        win.bind("<KeyPress-s>", self._ss_hotkey_screenshot)
        win.bind("<KeyPress-S>", self._ss_hotkey_screenshot)

        self._ss_mini_window = win
        # Reflect current failed-device state on the freshly-created mini button
        # and show the compact summary.
        self._ss_refresh_retry_button()
        try:
            self._ss_mini_lbl.configure(text=self._ss_mini_summary())
        except Exception:
            pass
        try:
            win.focus_force()
        except Exception:
            pass

    def _ss_mini_on_page_selected(self, event=None):
        """Mini dropdown: handle the 'Enter name:' sentinel by opening the dialog."""
        try:
            if self._ss_mini_page_var.get() == self.SS_ENTER_SENTINEL:
                self._ss_mini_add_page_dialog()
        except Exception:
            pass

    def _ss_mini_add_page_dialog(self):
        """Small modal to type a new page name from the mini window."""
        try:
            from tkinter import simpledialog
            name = simpledialog.askstring("Add page", "New page name:",
                                          parent=self._ss_mini_window)
        except Exception:
            name = None
        canon = self._ss_add_page_name(name) if name else ""
        if canon:
            try:
                self._ss_mini_page_var.set(canon)
            except Exception:
                pass
            self._ss_rebuild_page_status()
        elif self._ss_mini_page_var is not None:
            # Reset sentinel back to a real page if nothing was added.
            try:
                if self._ss_mini_page_var.get() == self.SS_ENTER_SENTINEL and self._ss_page_names:
                    self._ss_mini_page_var.set(self._ss_page_names[0])
            except Exception:
                pass

    # ══════════════════════════════════════════════════════════════════════════
    # TAB: DATA EXTRACTOR  (trial — manual image → page detect → OCR extract)
    # Controller-side only.  Never touches devices, run, cache, sheets, or the bot.
    # ══════════════════════════════════════════════════════════════════════════
    DE_PAGES_JSON = "pages.json"
    DE_CONFIG_JSON = "data_extractors.json"
    DE_DEBUG_DIR = "data_extractor_debug"
    DE_BASE_W = 1920
    DE_BASE_H = 1080
    DE_PAGE_THRESHOLD = 0.50
    DE_PIXEL_PREFILTER = 0.45       # min pixel score to bother OCR-scoring a page in Auto
    DE_TESS_TIMEOUT = 1.2           # per-call tesseract timeout (seconds) — fast passes
    DE_TESS_TIMEOUT_DEEP = 2.0      # per-call timeout for deep/fallback passes
    DE_MAX_TESS_ATTEMPTS_PER_FIELD = 10  # cap for normal fields (gold, clean resources)
    DE_MAX_TESS_ATTEMPTS_HARD = 14       # cap for hard fields (power has 6 rects)
    DE_HARD_FIELDS = ("power", "food", "parts")  # fields allowed the higher cap
    DE_CONFIG_VERSION = 4          # bump when default rects change → triggers upgrade

    # OCR engine mode for target-app-main extraction.
    DE_OCR_MODES = ["EasyOCR primary", "Tesseract primary", "Auto"]
    DE_OCR_MODE_DEFAULT = "EasyOCR primary"
    # Top UI band (base coords) for the single EasyOCR primary pass.
    DE_TOP_BAND = [0, 0, 1920, 135]

    # Target-page dropdown values (Auto + dummy placeholder list).  Only
    # 'target app main' has a real extractor; the rest are placeholders for now.
    DE_TARGET_PAGES = [
        "Auto", "target app main", "game main map", "app level", "monster",
        "server", "speedup", "resources", "inventory other",
    ]
    DE_GMA_FIELDS = ["gold", "power", "food", "parts", "electric", "gas", "cash"]

    # ── Final output schema (exact column order for the combined row) ──────────
    DE_OUTPUT_COLUMNS = [
        "power", "gold", "food_top", "parts_top", "electric_top", "gas_top",
        "cash_top", "ark_map_coordinate", "app_level", "monster_killed", "server",
        "speedup_5min", "speedup_15min", "speedup_30min", "speedup_1hour",
        "speedup_3hour", "speedup_8hour", "speedup_24hour", "speedup_3days",
        "speedup_30days", "speedup_180days",
        "food_1_2m", "food_10m", "food_400k", "food_200k",
        "parts_1_2m", "parts_10m", "parts_400k", "parts_200k",
        "electric_1_2m", "electric_10m", "electric_200k",
        "gas_1_2m", "gas_10m", "gas_200k",
        "cash_1_2m", "cash_10m", "cash_200k",
        "melange", "melange_10k", "melange_100k",
        "honor_medals", "shining_medals", "ether_medals",
        "level_15", "level_20", "level_30", "level_40",
        "optional_chest_200k", "optional_chest_1_2m",
    ]

    # Which output columns each page is responsible for filling.
    DE_PAGE_COLUMN_MAP = {
        "target app main": ["power", "gold", "food_top", "parts_top",
                          "electric_top", "gas_top", "cash_top"],
        "game main map": ["ark_map_coordinate"],
        "app level": ["app_level"],
        "monster": ["monster_killed"],
        "server": ["server"],
        "speedup": ["speedup_5min", "speedup_15min", "speedup_30min",
                    "speedup_1hour", "speedup_3hour", "speedup_8hour",
                    "speedup_24hour", "speedup_3days", "speedup_30days",
                    "speedup_180days"],
        "resources": ["food_1_2m", "food_10m", "food_400k", "food_200k",
                      "parts_1_2m", "parts_10m", "parts_400k", "parts_200k",
                      "electric_1_2m", "electric_10m", "electric_200k",
                      "gas_1_2m", "gas_10m", "gas_200k",
                      "cash_1_2m", "cash_10m", "cash_200k"],
        "inventory other": ["melange", "melange_10k", "melange_100k",
                            "honor_medals", "shining_medals", "ether_medals",
                            "level_15", "level_20", "level_30", "level_40",
                            "optional_chest_200k", "optional_chest_1_2m"],
    }

    # Columns whose default is blank (non-count fields) rather than "0".
    DE_BLANK_DEFAULT_COLUMNS = {
        "power", "gold", "food_top", "parts_top", "electric_top", "gas_top",
        "cash_top", "ark_map_coordinate", "app_level", "server", "monster_killed",
    }
    # monster_killed stays blank until the monster page is extracted; that
    # extractor sets 'no' when the page was detected but the kill state wasn't
    # confirmed, and 'yes' when it was — never guessed on failure.

    # Pages that currently have a real extractor implementation.  Others are
    # placeholders — detected/scored if possible but not yet extracting (no fake
    # values).  This list grows as templates are added to pages.json.
    DE_IMPLEMENTED_PAGES = {
        "target app main", "game main map", "app level", "server",
        "monster", "speedup", "resources", "inventory other",
    }

    # ── Per-page OCR regions (base 1920×1080 coords) ──────────────────────────
    # Single-value pages calibrated from sample screenshots.
    DE_MAP_COORD_RECT = [0, 6, 305, 85]          # "X 536  Y 385" top-left badge
    DE_ARK_LEVEL_RECT = [870, 175, 1180, 230]    # "BridgeLv. 18" floating label
    DE_SERVER_RECT = [380, 360, 760, 470]        # pinned-planet "#1705" label area
    DE_MONSTER_RECT = [560, 60, 1280, 760]       # search/result modal body
    # Inventory grid (3-column card area in the Shop→Inventory panel).  The grid
    # scrolls, so a single screenshot shows only part of the full item set.
    DE_INV_GRID_RECT = [560, 250, 1240, 1080]
    # Calibrated 3-column card geometry (base 1920×1080), measured from the
    # resources / inventory-other calibration screenshots.  Card icons are ~160px;
    # the white "xN" count sits ~112px below each icon centre.
    DE_INV_COL_CX = [663, 908, 1153]          # column centres (x)
    DE_INV_ROW_CY = [345, 585, 825, 1065]     # visible row centres (y)
    DE_INV_ICON_HALF = 80                     # icon half-size
    DE_INV_COUNT_DY = 112                     # count-text centre offset below icon
    DE_INV_COUNT_HALF_W = 82                  # count crop half-width
    # Legacy (kept for back-compat with any external refs; no longer used).
    DE_INV_COL_X = [(415, 590), (607, 778), (797, 968)]
    DE_INV_ROW_Y = [200, 380, 560, 740]
    DE_INV_CARD_H = 150
    # Speedup duration badge text → output column.
    DE_SPEEDUP_DURATION_COL = {
        "5M": "speedup_5min", "15M": "speedup_15min", "30M": "speedup_30min",
        "1H": "speedup_1hour", "3H": "speedup_3hour", "8H": "speedup_8hour",
        "24H": "speedup_24hour", "3D": "speedup_3days", "30D": "speedup_30days",
        "180D": "speedup_180days",
    }

    DE_DEFAULT_CONFIG = {
        "version": 4,
        "target app main": {
            "base_size": [1920, 1080],
            "fields": {
                # Number slots; power is widened left to catch the leading '1'
                # in values like 1,686,752.
                "gold":     {"rect": [1710, 17, 1915, 78], "type": "number",
                             "ocr": ["tesseract", "easyocr"], "whitelist": "0123456789,"},
                "power":    {"rect": [170, 68, 430, 122], "type": "number",
                             "ocr": ["tesseract", "easyocr"], "whitelist": "0123456789,"},
                "food":     {"rect": [625, 5, 775, 70], "type": "resource",
                             "ocr": ["tesseract", "easyocr"], "whitelist": "0123456789.KkMmBb"},
                "parts":    {"rect": [820, 5, 985, 70], "type": "resource",
                             "ocr": ["tesseract", "easyocr"], "whitelist": "0123456789.KkMmBb"},
                "electric": {"rect": [1050, 5, 1195, 70], "type": "resource",
                             "ocr": ["tesseract", "easyocr"], "whitelist": "0123456789.KkMmBb"},
                "gas":      {"rect": [1245, 5, 1410, 70], "type": "resource",
                             "ocr": ["tesseract", "easyocr"], "whitelist": "0123456789.KkMmBb"},
                "cash":     {"rect": [1465, 5, 1600, 70], "type": "resource",
                             "ocr": ["tesseract", "easyocr"], "whitelist": "0123456789.KkMmBb"},
            },
        },
        # ── Placeholder pages (structure only; no rects/values until tuned) ──
        # 'enabled': False → detected/scored if a template exists in pages.json,
        # but extraction reports 'no extractor yet' rather than faking values.
        "game main map": {"base_size": [1920, 1080], "enabled": False,
                          "columns": ["ark_map_coordinate"], "fields": {}},
        "app level": {"base_size": [1920, 1080], "enabled": False,
                      "columns": ["app_level"], "fields": {}},
        "monster": {"base_size": [1920, 1080], "enabled": False,
                    "columns": ["monster_killed"], "fields": {}},
        "server": {"base_size": [1920, 1080], "enabled": False,
                   "columns": ["server"], "fields": {}},
        "speedup": {"base_size": [1920, 1080], "enabled": False,
                    "columns": ["speedup_5min", "speedup_15min", "speedup_30min",
                                "speedup_1hour", "speedup_3hour", "speedup_8hour",
                                "speedup_24hour", "speedup_3days", "speedup_30days",
                                "speedup_180days"], "fields": {}},
        "resources": {"base_size": [1920, 1080], "enabled": False,
                      "columns": ["food_1_2m", "food_10m", "food_400k", "food_200k",
                                  "parts_1_2m", "parts_10m", "parts_400k", "parts_200k",
                                  "electric_1_2m", "electric_10m", "electric_200k",
                                  "gas_1_2m", "gas_10m", "gas_200k",
                                  "cash_1_2m", "cash_10m", "cash_200k"], "fields": {}},
        "inventory other": {"base_size": [1920, 1080], "enabled": False,
                            "columns": ["melange", "melange_10k", "melange_100k",
                                        "honor_medals", "shining_medals", "ether_medals",
                                        "level_15", "level_20", "level_30", "level_40",
                                        "optional_chest_200k", "optional_chest_1_2m"],
                            "fields": {}},
    }

    # Old rects (any prior version) — used to detect & auto-upgrade a stale
    # data_extractors.json to the current default rects.
    DE_OLD_V1_RECTS = {
        "gold": [1663, 17, 1915, 78], "power": [186, 58, 504, 126],
        "food": [580, 5, 770, 70], "parts": [785, 5, 970, 70],
        "electric": [1000, 5, 1180, 70], "gas": [1205, 5, 1400, 70],
        "cash": [1425, 5, 1590, 70],
    }
    # v2 power rect (so a v2 → v3 upgrade refreshes it to the wider slot).
    DE_OLD_V2_POWER_RECT = [190, 74, 395, 116]

    def _build_data_extractor_tab(self):
        tab = self._tab_data_extractor
        for w in tab.winfo_children():
            w.destroy()
        tab.columnconfigure(0, weight=1)
        tab.rowconfigure(4, weight=1)

        ctl = tk.Frame(tab, bg=BG_MID)
        ctl.grid(row=0, column=0, sticky="ew", padx=6, pady=(6, 2))
        _btn(ctl, "📂 Upload Image", self._de_upload_image,
             bg=BG_CELL, fg=FG_MAIN, font=FNB, padx=8, pady=4).pack(side=tk.LEFT, padx=2)
        self._de_detect_btn = _btn(ctl, "🔍 Detect Page", self._de_detect_page,
                                   bg=BG_CELL, fg=FG_MAIN, font=FNB, padx=8, pady=4,
                                   state=tk.DISABLED)
        self._de_detect_btn.pack(side=tk.LEFT, padx=2)
        self._de_extract_btn = _btn(ctl, "🧾 Extract Data", self._de_extract_data,
                                    bg=BG_CELL, fg=FG_MAIN, font=FNB, padx=8, pady=4,
                                    state=tk.DISABLED)
        self._de_extract_btn.pack(side=tk.LEFT, padx=2)
        _btn(ctl, "🗑 Clear", self._de_clear,
             bg=BG_CELL, fg=FG_DIM, font=FS, padx=8, pady=4).pack(side=tk.LEFT, padx=2)
        self._de_debug_var = tk.BooleanVar(value=False)
        tk.Checkbutton(ctl, text="Save debug crops", variable=self._de_debug_var,
                       font=FS, bg=BG_MID, fg=FG_DIM, selectcolor=BG_CELL,
                       activebackground=BG_MID).pack(side=tk.RIGHT, padx=8)

        # ── Target page + field selection row ──
        sel = tk.Frame(tab, bg=BG_MID)
        sel.grid(row=1, column=0, sticky="ew", padx=6, pady=(0, 2))
        tk.Label(sel, text="Target page:", font=FSB, bg=BG_MID, fg=FG_MAIN).pack(
            side=tk.LEFT, padx=(4, 4))
        self._de_target_var = tk.StringVar(value="target app main")  # default
        self._de_target_combo = ttk.Combobox(
            sel, textvariable=self._de_target_var, state="readonly", width=20,
            values=list(self.DE_TARGET_PAGES))
        self._de_target_combo.pack(side=tk.LEFT, padx=2)

        tk.Label(sel, text="OCR:", font=FSB, bg=BG_MID, fg=FG_MAIN).pack(
            side=tk.LEFT, padx=(14, 4))
        self._de_ocr_mode_var = tk.StringVar(value=self.DE_OCR_MODE_DEFAULT)
        self._de_ocr_mode_combo = ttk.Combobox(
            sel, textvariable=self._de_ocr_mode_var, state="readonly", width=16,
            values=list(self.DE_OCR_MODES))
        self._de_ocr_mode_combo.pack(side=tk.LEFT, padx=2)

        tk.Label(sel, text="Fields:", font=FSB, bg=BG_MID, fg=FG_MAIN).pack(
            side=tk.LEFT, padx=(14, 4))
        self._de_field_all_var = tk.BooleanVar(value=True)
        def _on_all_toggle():
            on = self._de_field_all_var.get()
            for var in self._de_field_vars.values():
                if on:
                    var.set(True)
        tk.Checkbutton(sel, text="all", variable=self._de_field_all_var,
                       command=_on_all_toggle, font=FS, bg=BG_MID, fg=FG_MAIN,
                       selectcolor=BG_CELL, activebackground=BG_MID).pack(side=tk.LEFT)
        # Dynamic field checkboxes live in this frame; rebuilt per target page.
        self._de_fields_frame = tk.Frame(sel, bg=BG_MID)
        self._de_fields_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self._de_field_vars = {}
        # Build the initial field list for the default target page.
        self._de_rebuild_field_checks(self._de_target_var.get())
        # Rebuild whenever the target page changes.
        self._de_target_combo.bind(
            "<<ComboboxSelected>>",
            lambda _e: self._de_on_target_changed())

        info = tk.Frame(tab, bg=BG_BASE)
        info.grid(row=2, column=0, sticky="ew", padx=6, pady=(0, 2))
        self._de_path_lbl = tk.Label(info, text="No image selected", font=FS,
                                     bg=BG_BASE, fg=FG_DIM, anchor="w")
        self._de_path_lbl.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self._de_page_lbl = tk.Label(info, text="Detected page: —", font=FNB,
                                     bg=BG_BASE, fg=FG_MAIN)
        self._de_page_lbl.pack(side=tk.RIGHT, padx=8)

        self._de_status = tk.Label(tab, text="Data Extractor ready (trial).", font=FS,
                                   bg=BG_BASE, fg=FG_DIM, anchor="w")
        self._de_status.grid(row=3, column=0, sticky="ew", padx=8, pady=(0, 2))

        tf = tk.LabelFrame(tab, text=" Extracted Values ", font=FSB, bg=BG_PANEL,
                           fg=FG_DIM, bd=1, relief=tk.SOLID, labelanchor="nw")
        tf.grid(row=4, column=0, sticky="nsew", padx=6, pady=(2, 4))
        tf.columnconfigure(0, weight=1)
        tf.rowconfigure(0, weight=1)
        cols = ("field", "value", "raw", "engine", "status", "region")
        self._de_tv = ttk.Treeview(tf, columns=cols, show="headings", style="Sheet.Treeview")
        for c, w, t, anchor in [
            ("field", 110, "Field", tk.W), ("value", 130, "Value", tk.W),
            ("raw", 160, "Raw OCR", tk.W), ("engine", 100, "OCR Engine", tk.W),
            ("status", 130, "Confidence/Status", tk.W), ("region", 200, "Region", tk.W),
        ]:
            self._de_tv.heading(c, text=t, anchor=anchor)
            self._de_tv.column(c, width=w, minwidth=40,
                               stretch=(c in ("raw", "region")), anchor=anchor)
        self._de_tv.grid(row=0, column=0, sticky="nsew", padx=4, pady=4)
        _sb = ttk.Scrollbar(tf, orient="vertical", command=self._de_tv.yview)
        self._de_tv.configure(yscrollcommand=_sb.set)
        _sb.grid(row=0, column=1, sticky="ns")

        # ── Combined output row (final schema, tab-separated for Sheets) ──
        of = tk.LabelFrame(tab, text=" Final Output Row (tab-separated) ", font=FSB,
                           bg=BG_PANEL, fg=FG_DIM, bd=1, relief=tk.SOLID,
                           labelanchor="nw")
        of.grid(row=5, column=0, sticky="ew", padx=6, pady=(0, 4))
        of.columnconfigure(0, weight=1)
        btns = tk.Frame(of, bg=BG_PANEL)
        btns.grid(row=0, column=0, sticky="ew", padx=4, pady=(4, 2))
        tk.Button(btns, text="Copy Row", font=FS, command=self._de_copy_row,
                  bg=BG_CELL, fg=FG_MAIN, bd=0, padx=8).pack(side=tk.LEFT, padx=2)
        tk.Button(btns, text="Copy Headers", font=FS, command=self._de_copy_headers,
                  bg=BG_CELL, fg=FG_MAIN, bd=0, padx=8).pack(side=tk.LEFT, padx=2)
        tk.Button(btns, text="Copy JSON", font=FS, command=self._de_copy_json,
                  bg=BG_CELL, fg=FG_MAIN, bd=0, padx=8).pack(side=tk.LEFT, padx=2)
        tk.Button(btns, text="Copy Row+Headers", font=FS, command=self._de_copy_both,
                  bg=BG_CELL, fg=FG_MAIN, bd=0, padx=8).pack(side=tk.LEFT, padx=2)
        tk.Button(btns, text="Reset Row", font=FS, command=self._de_reset_row,
                  bg=BG_CELL, fg="#e0a05a", bd=0, padx=8).pack(side=tk.LEFT, padx=(12, 2))
        self._de_row_banner = tk.Label(
            of, text="", font=("", 9, "italic"), bg=BG_PANEL, fg="#e0a05a",
            anchor="w")
        self._de_row_banner.grid(row=1, column=0, sticky="ew", padx=6)
        self._de_outrow = scrolledtext.ScrolledText(of, height=3, bg=BG_CELL,
                                                     fg=FG_MAIN, font=FMS,
                                                     wrap=tk.NONE, bd=0)
        self._de_outrow.grid(row=2, column=0, sticky="ew", padx=4, pady=(0, 4))
        self._de_outrow.configure(state=tk.DISABLED)

        lf = tk.LabelFrame(tab, text=" Status / Debug ", font=FSB, bg=BG_PANEL,
                           fg=FG_DIM, bd=1, relief=tk.SOLID, labelanchor="nw")
        lf.grid(row=6, column=0, sticky="ew", padx=6, pady=(0, 6))
        lf.columnconfigure(0, weight=1)
        self._de_log = scrolledtext.ScrolledText(lf, height=8, bg=BG_CELL, fg=FG_MAIN,
                                                  font=FMS, wrap=tk.WORD, bd=0)
        self._de_log.grid(row=0, column=0, sticky="ew", padx=4, pady=4)

        # Initialise persistent combined row + render it.
        self._de_ensure_row()
        self._de_refresh_output_row()
        self._de_update_row_banner()
        # Wire optional drag-and-drop (graceful if tkinterdnd2 missing).
        self._de_setup_dnd(tab)

    def _de_clip_set(self, text, label):
        try:
            self.clipboard_clear(); self.clipboard_append(text)
            self._de_set_status(f"Copied {label} to clipboard.")
        except Exception as exc:
            self._de_set_status(f"Copy failed: {exc}")

    def _de_copy_row(self):
        self._de_clip_set(self._de_row_tsv(with_headers=False), "row")

    def _de_copy_headers(self):
        self._de_clip_set("\t".join(self.DE_OUTPUT_COLUMNS), "headers")

    def _de_copy_json(self):
        self._de_clip_set(self._de_row_json(), "JSON")

    def _de_copy_both(self):
        self._de_clip_set(self._de_row_tsv(with_headers=True), "headers+row")

    def _de_reset_row(self):
        """Reset ONLY the combined output row (not the loaded image / log)."""
        self._de_current_row = self._de_default_row()
        self._de_filled_pages = []
        self._de_refresh_output_row()
        self._de_update_row_banner()
        self._de_set_status("Combined output row reset.")
        self._de_log_line("[row] combined output row reset to defaults.")

    def _de_update_row_banner(self):
        """Show which pages currently contribute to the combined row."""
        lbl = getattr(self, "_de_row_banner", None)
        if lbl is None:
            return
        pages = getattr(self, "_de_filled_pages", []) or []
        if pages:
            txt = ("Combined row contains values from previously extracted page(s): "
                   + ", ".join(pages) + ".  Use Reset Row to clear.")
        else:
            txt = "Combined row is empty (defaults). Extract a page to fill it."
        try:
            lbl.configure(text=txt)
        except Exception:
            pass

    def _de_setup_dnd(self, widget):
        """
        Enable drag-and-drop of an image onto the Data Extractor tab when
        tkinterdnd2 is installed AND the root is DnD-capable (the controller base
        class becomes TkinterDnD.Tk when the package is present).  Degrades
        gracefully — never a hard dependency.
        """
        if not _DND_AVAILABLE or DND_FILES is None:
            self._de_log_line("Drag and drop unavailable; use Upload Image.")
            return
        try:
            widget.drop_target_register(DND_FILES)
            widget.dnd_bind("<<Drop>>", self._de_on_drop)
            self._de_log_line("Drag-and-drop ready: drop an image onto this tab.")
        except Exception:
            # Root was not created via TkinterDnD.Tk(); DND not active.
            self._de_log_line("Drag and drop unavailable; use Upload Image.")

    def _de_on_drop(self, event):
        # event.data is a brace/space-separated list of paths.
        import re as _re
        raw = getattr(event, "data", "") or ""
        paths = _re.findall(r"\{[^}]*\}|\S+", raw)
        paths = [p.strip("{}") for p in paths]
        imgs = [p for p in paths
                if p.lower().endswith((".png", ".jpg", ".jpeg", ".bmp", ".webp"))]
        if not imgs:
            self._de_set_status("Dropped item is not an image; use Upload Image.")
            self._de_log_line("[dnd] dropped item is not a supported image file.")
            return
        if len(imgs) > 1:
            self._de_log_line(
                f"[dnd] {len(imgs)} files dropped; loading the first only for now.")
        self._de_load_image_path(imgs[0])

    def _de_set_status(self, text):
        try:
            self._de_status.configure(text=text)
        except Exception:
            pass

    def _de_log_line(self, text):
        try:
            self._de_log.insert(tk.END, text + "\n")
            self._de_log.see(tk.END)
        except Exception:
            pass

    def _de_upload_image(self):
        path = filedialog.askopenfilename(
            title="Select a screenshot",
            filetypes=[("Images", "*.png *.jpg *.jpeg *.webp *.bmp"), ("All files", "*.*")])
        if not path:
            return
        self._de_load_image_path(path)

    def _de_load_image_path(self, path):
        """Load an image from a path (used by Upload Image and drag-and-drop)."""
        if not _PIL_OK:
            self._de_set_status("PIL not available — cannot load images.")
            return
        try:
            img = Image.open(path).convert("RGB")
            img.load()
        except Exception as exc:
            self._de_set_status(f"Could not load image: {exc}")
            try:
                messagebox.showwarning("Data Extractor", f"Could not load image:\n{exc}")
            except Exception:
                pass
            return
        self._de_image_path = path
        self._de_image = img
        self._de_detected_page = None
        self._de_last_result = None
        try:
            self._de_path_lbl.configure(text=f"{path}   ({img.width}×{img.height})")
            self._de_page_lbl.configure(text="Detected page: —")
            self._de_detect_btn.configure(state=tk.NORMAL)
            self._de_extract_btn.configure(state=tk.NORMAL)
            self._de_tv.delete(*self._de_tv.get_children())
        except Exception:
            pass
        self._de_set_status("Image loaded. Click Detect Page or Extract Data.")
        self._de_log_line(f"[upload] {path} ({img.width}×{img.height})")

    def _de_load_config(self):
        path = self.DE_CONFIG_JSON
        try:
            if os.path.exists(path):
                with open(path, "r", encoding="utf-8") as fh:
                    data = json.load(fh)
                if isinstance(data, dict) and data:
                    data = self._de_maybe_upgrade_config(data, path)
                    return data
        except Exception as exc:
            self._de_log_line(f"[config] unreadable ({exc}); recreating default")
        try:
            with open(path, "w", encoding="utf-8") as fh:
                json.dump(self.DE_DEFAULT_CONFIG, fh, indent=2)
            self._de_log_line(f"[config] created {path} with default 'target app main' (v{self.DE_CONFIG_VERSION})")
        except Exception as exc:
            self._de_log_line(f"[config] could not write default ({exc}); using in-memory")
        return dict(self.DE_DEFAULT_CONFIG)

    def _de_maybe_upgrade_config(self, data, path):
        """
        If data_extractors.json is stale (no version, or still using the old v1
        target-app-main rects), upgrade the target-app-main field rects to the
        improved v2 values and rewrite the file.  Other pages/fields the user
        may have added are preserved.  Returns the (possibly upgraded) config.
        """
        try:
            ver = data.get("version")
            gma = data.get("target app main", {})
            fields = gma.get("fields", {}) if isinstance(gma, dict) else {}
            # Detect "still on old v1 rects": any field whose rect matches v1.
            looks_old = False
            for fname, old_rect in self.DE_OLD_V1_RECTS.items():
                fr = fields.get(fname, {}).get("rect")
                if fr and list(fr) == old_rect:
                    looks_old = True
                    break
            if ver == self.DE_CONFIG_VERSION and not looks_old:
                return data   # already current

            if looks_old or ver != self.DE_CONFIG_VERSION:
                new_fields = self.DE_DEFAULT_CONFIG["target app main"]["fields"]
                if isinstance(gma, dict):
                    gma.setdefault("base_size", [1920, 1080])
                    gma_fields = gma.setdefault("fields", {})
                    for fname, fspec in new_fields.items():
                        # Upgrade rect (and ensure type/ocr/whitelist exist).
                        cur = gma_fields.get(fname, {})
                        cur["rect"] = list(fspec["rect"])
                        cur.setdefault("type", fspec["type"])
                        cur.setdefault("ocr", list(fspec["ocr"]))
                        cur.setdefault("whitelist", fspec["whitelist"])
                        gma_fields[fname] = cur
                    data["target app main"] = gma
                else:
                    data["target app main"] = dict(self.DE_DEFAULT_CONFIG["target app main"])
                # Merge in any default pages missing from the user's config
                # (placeholder pages added in newer versions).  Never overwrite a
                # page the user already has.
                for pname, pspec in self.DE_DEFAULT_CONFIG.items():
                    if pname == "version":
                        continue
                    if pname not in data:
                        data[pname] = dict(pspec)
                data["version"] = self.DE_CONFIG_VERSION
                try:
                    with open(path, "w", encoding="utf-8") as fh:
                        json.dump(data, fh, indent=2)
                    self._de_log_line(
                        f"[config] upgraded target-app-main rects to v{self.DE_CONFIG_VERSION} "
                        f"(old/region config detected)")
                except Exception as exc:
                    self._de_log_line(f"[config] upgrade write failed ({exc}); using in-memory upgrade")
        except Exception as exc:
            self._de_log_line(f"[config] upgrade check failed ({exc}); using config as-is")
        return data

    def _de_load_pages(self, use_cache=True):
        """
        Load & parse pages.json into {name: spec}.  Cached after first load
        (cache key = file path + mtime) so repeated detections don't re-read /
        re-parse the (large) file.
        """
        path = self.DE_PAGES_JSON
        try:
            mtime = os.path.getmtime(path)
        except Exception:
            mtime = 0
        cache = getattr(self, "_de_pages_cache", None)
        if use_cache and cache is not None and cache[0] == (path, mtime):
            return cache[1]
        try:
            with open(path, "r", encoding="utf-8") as fh:
                data = json.load(fh)
        except Exception as exc:
            self._de_log_line(f"[pages] could not load {path}: {exc}")
            return {}
        result = {}
        if isinstance(data, list):
            # Format 1: list of page objects [{"page": name, ...}, ...]
            for entry in data:
                if isinstance(entry, dict):
                    nm = (entry.get("page") or "").strip()
                    if nm:
                        result[nm] = entry
        elif isinstance(data, dict):
            # Format 3: a SINGLE page object {"page": name, "regions": ..., ...}
            if "page" in data and isinstance(data.get("page"), str):
                nm = data["page"].strip()
                if nm:
                    result[nm] = data
            else:
                # Format 2: mapping {page_name: spec, ...}
                for k, v in data.items():
                    if isinstance(v, dict):
                        result[str(k)] = v
        self._de_pages_cache = ((path, mtime), result)
        return result

    @staticmethod
    def _de_scale_rect(rect, sx, sy):
        x1, y1, x2, y2 = rect
        return [int(round(x1 * sx)), int(round(y1 * sy)),
                int(round(x2 * sx)), int(round(y2 * sy))]

    def _de_score_pixels(self, img_rgb_np, regions, sx, sy, tol=12):
        import math as _math
        ih, iw = img_rgb_np.shape[:2]
        total = matched = 0
        for region in regions or []:
            grid = region.get("pixel_grid")
            if not grid:
                continue
            x = region.get("x", 0); y = region.get("y", 0)
            w = region.get("w", region.get("width", 1))
            h = region.get("h", region.get("height", 1))
            step_x = max(1, _math.ceil(w / 40))
            step_y = max(1, _math.ceil(h / 40))
            for row_idx, row in enumerate(grid):
                py = int(round((y + row_idx * step_y) * sy))
                if py >= ih or py < 0:
                    continue
                for col_idx, ref in enumerate(row):
                    px = int(round((x + col_idx * step_x) * sx))
                    if px >= iw or px < 0:
                        continue
                    if not (isinstance(ref, (list, tuple)) and len(ref) == 3):
                        continue
                    total += 1
                    live = img_rgb_np[py, px]
                    if (abs(int(live[0]) - ref[0]) <= tol and
                            abs(int(live[1]) - ref[1]) <= tol and
                            abs(int(live[2]) - ref[2]) <= tol):
                        matched += 1
        return ((matched / total) if total else 0.0), matched, total

    @staticmethod
    def _de_fuzzy(expected, found, threshold=0.80):
        from difflib import SequenceMatcher
        e = (expected or "").strip().lower()
        f = (found or "").strip().lower()
        if not e:
            return False
        if e in f:
            return True
        return SequenceMatcher(None, e, f).ratio() >= threshold

    def _de_score_texts(self, pil_img, texts, sx, sy):
        """
        OCR each text anchor and fuzzy-match.  Returns
        (score, matched, total, req_matched, req_total) where the req_* counts
        cover anchors flagged required.  A single required miss no longer forces
        a hard fail — the caller decides based on how many required anchors hit.
        """
        try:
            import numpy as _np, cv2 as _cv2, pytesseract as _pt
        except Exception:
            return 0.0, 0, 0, 0, 0
        matched = total = 0
        req_matched = req_total = 0
        for t_spec in texts or []:
            expected = (t_spec.get("text") or "").strip()
            if not expected:
                continue
            rect = t_spec.get("rect")
            if not rect or len(rect) != 4:
                tx, ty = t_spec.get("x"), t_spec.get("y")
                tw, th = t_spec.get("w"), t_spec.get("h")
                if None in (tx, ty, tw, th):
                    continue
                rect = [tx, ty, tx + tw, ty + th]
            total += 1
            is_req = bool(t_spec.get("required"))
            if is_req:
                req_total += 1
            sr = self._de_scale_rect(rect, sx, sy)
            try:
                crop = pil_img.crop((sr[0], sr[1], sr[2], sr[3])).convert("L")
                arr = _np.array(crop)
                _, binr = _cv2.threshold(arr, 0, 255, _cv2.THRESH_BINARY + _cv2.THRESH_OTSU)
                txt = _pt.image_to_string(Image.fromarray(binr), config="--oem 1 --psm 6").strip()
            except Exception:
                txt = ""
            if self._de_fuzzy(expected, txt):
                matched += 1
                if is_req:
                    req_matched += 1
        return ((matched / total) if total else 0.0), matched, total, req_matched, req_total

    def _de_score_one_page(self, name, spec, img_np, pil_img, sx, sy, pixel_only=False):
        """
        Score a single page spec against the image.  When pixel_only=True, skip
        the (expensive) OCR text scoring and return just the pixel component —
        used as a cheap pre-filter before committing to OCR.
        Returns the score dict (same shape the detector aggregates).
        """
        regions = spec.get("regions", [])
        texts = spec.get("texts", [])
        has_px = bool(regions)
        if has_px:
            px_score, _pm, _pt2 = self._de_score_pixels(img_np, regions, sx, sy)
        else:
            px_score = 0.0
        if pixel_only:
            return {"final": round(px_score, 4), "pixel": round(px_score, 4),
                    "text": 0.0, "text_matched": 0, "text_total": 0,
                    "req_matched": 0, "req_total": 0, "pixel_only": True}
        if texts:
            tx_score, tmatch, ttot, req_matched, req_total = \
                self._de_score_texts(pil_img, texts, sx, sy)
        else:
            tx_score, tmatch, ttot, req_matched, req_total = 0.0, 0, 0, 0, 0
        has_tx = ttot > 0
        req_zero = (req_total > 0 and req_matched == 0)
        if has_tx and req_total > 0:
            req_rate = req_matched / req_total
            text_component = req_rate * 0.70 + tx_score * 0.30
        else:
            text_component = tx_score
        if req_zero:
            final = 0.0
        elif has_px and has_tx:
            if px_score < 0.10:
                final = px_score * 0.30 + text_component * 0.70 * (px_score / 0.10)
            else:
                final = px_score * 0.30 + text_component * 0.70
        elif has_tx:
            final = text_component
        elif has_px:
            final = px_score
        else:
            final = 0.0
        return {"final": round(final, 4), "pixel": round(px_score, 4),
                "text": round(tx_score, 4), "text_matched": tmatch,
                "text_total": ttot, "req_matched": req_matched,
                "req_total": req_total}

    def _de_detect_page_for_image(self, pil_img, target_pages=None):
        """
        Detect the page for an image.

        target_pages:
          * None or ['Auto']   → evaluate ALL pages in pages.json (parallel,
                                  pixel-pre-filter then OCR), highest score wins.
          * [single page name] → evaluate ONLY that page (fast path); returns it
                                  if score >= threshold, else 'unknown'.  Does NOT
                                  compare against any other page (so a slightly
                                  higher-scoring 'gold chest' can never override a
                                  deliberately-selected 'target app main').
          * [several names]    → evaluate only those, highest among them wins.

        Returns (page_or_unknown, confidence, scores_dict).  Logs timing.
        """
        import numpy as _np, time as _time
        from concurrent.futures import ThreadPoolExecutor, as_completed

        pages = self._de_load_pages()
        if not pages:
            return "unknown", 0.0, {}
        sx = pil_img.width / float(self.DE_BASE_W)
        sy = pil_img.height / float(self.DE_BASE_H)
        img_np = _np.array(pil_img.convert("RGB"))

        # Resolve the candidate set.
        auto = (not target_pages) or ("Auto" in target_pages)
        if auto:
            candidates = list(pages.keys())
            target_label = "Auto"
        else:
            candidates = [p for p in target_pages if p in pages]
            target_label = ", ".join(target_pages)
            # A selected placeholder page that isn't in pages.json can't be scored.
            if not candidates:
                _multi_log.info(
                    f"[DATA-EXTRACTOR] page detect target={target_label}: "
                    f"no matching page definition in pages.json")
                return "unknown", 0.0, {}

        t0 = _time.time()
        _multi_log.info(f"[DATA-EXTRACTOR] page detect started target={target_label}")
        _multi_log.info(f"[DATA-EXTRACTOR] page detect candidates={len(candidates)}")

        scores = {}

        # ── Single-/few-page fast path: score directly, no pool overhead ──
        if not auto or len(candidates) <= 3:
            for name in candidates:
                scores[name] = self._de_score_one_page(
                    name, pages[name], img_np, pil_img, sx, sy)
        else:
            # ── Auto over many pages: cheap pixel pre-filter, then OCR only the
            # plausible ones (in parallel).  Pages with NO visual anchors must be
            # OCR'd (can't pre-filter), so they go straight to the OCR set.
            pre = {}
            ocr_set = []
            for name in candidates:
                spec = pages[name]
                if spec.get("regions"):
                    ps = self._de_score_one_page(name, spec, img_np, pil_img, sx, sy,
                                                 pixel_only=True)
                    pre[name] = ps
                    # Keep pages whose pixel score is at least plausible.
                    if ps["pixel"] >= self.DE_PIXEL_PREFILTER:
                        ocr_set.append(name)
                else:
                    ocr_set.append(name)
            # Always include the current best pixel pages even if few pass, so we
            # never prune away the real page on a noisy pixel match.
            if not ocr_set:
                ocr_set = sorted(pre, key=lambda k: pre[k]["pixel"],
                                 reverse=True)[:8] or candidates[:8]
            _multi_log.info(
                f"[DATA-EXTRACTOR] page detect pixel pre-filter kept {len(ocr_set)}"
                f"/{len(candidates)} for OCR")

            def _full(name):
                return name, self._de_score_one_page(
                    name, pages[name], img_np, pil_img, sx, sy)
            with ThreadPoolExecutor(max_workers=min(len(ocr_set), 8) or 1) as pool:
                for fut in as_completed([pool.submit(_full, n) for n in ocr_set]):
                    try:
                        nm, sc = fut.result()
                        scores[nm] = sc
                    except Exception:
                        pass
            # Pages we pixel-scored but didn't OCR keep their pixel-only score.
            for nm, ps in pre.items():
                scores.setdefault(nm, ps)

        if not scores:
            return "unknown", 0.0, {}
        best = max(scores, key=lambda k: scores[k]["final"])
        best_final = scores[best]["final"]
        dt = _time.time() - t0
        _multi_log.info(
            f"[DATA-EXTRACTOR] page detect done page={best} "
            f"score={best_final:.3f} time={dt:.2f}s")
        top = sorted(scores.items(), key=lambda kv: kv[1]["final"], reverse=True)[:5]
        _multi_log.info("[DATA-EXTRACTOR] top candidates: " +
                        ", ".join(f"{nm}={sc['final']:.3f}" for nm, sc in top))
        if best_final < self.DE_PAGE_THRESHOLD:
            return "unknown", best_final, scores
        return best, best_final, scores

    def _de_get_easyocr(self):
        if self._de_easyocr_reader is not None:
            return self._de_easyocr_reader or None
        # Parallel field workers may all reach here at once; build once under a lock.
        lock = getattr(self, "_de_easyocr_lock", None)
        if lock is None:
            import threading as _th
            lock = self._de_easyocr_lock = _th.Lock()
        with lock:
            if self._de_easyocr_reader is not None:
                return self._de_easyocr_reader or None
            import time as _time
            try:
                self.q.put(("de_status", "Loading EasyOCR model…"))
            except Exception:
                pass
            t0 = _time.time()
            try:
                import easyocr
                self._de_easyocr_reader = easyocr.Reader(["en"], gpu=False, verbose=False)
                dt = _time.time() - t0
                _multi_log.info(f"[DATA-EXTRACTOR] EasyOCR model load time={dt:.2f}s")
            except Exception as exc:
                self._de_easyocr_reader = False
                _multi_log.info(f"[DATA-EXTRACTOR] EasyOCR unavailable: {exc}")
                try:
                    self.q.put(("de_status", f"EasyOCR unavailable: {exc}"))
                except Exception:
                    pass
        return self._de_easyocr_reader or None

    def _de_easyocr_top_band(self, pil_img, sx=1.0, sy=1.0):
        """
        Run ONE EasyOCR pass over the top UI band (DE_TOP_BAND, scaled to the
        image).  Returns (boxes, elapsed) where each box is a dict:
            {text, conf, x0, y0, x1, y1, cx, cy}   (full-image coordinates)
        Returns ([], 0.0) if EasyOCR is unavailable.  This is the PRIMARY pass for
        target-app-main: a single detection over the whole top strip instead of many
        per-field Tesseract calls.
        """
        import numpy as _np, time as _time
        reader = self._de_get_easyocr()
        if reader is None:
            return [], 0.0
        bx0 = int(self.DE_TOP_BAND[0] * sx); by0 = int(self.DE_TOP_BAND[1] * sy)
        bx1 = int(self.DE_TOP_BAND[2] * sx); by1 = int(self.DE_TOP_BAND[3] * sy)
        bx0 = max(0, bx0); by0 = max(0, by0)
        bx1 = min(pil_img.width, bx1); by1 = min(pil_img.height, by1)
        crop = pil_img.crop((bx0, by0, bx1, by1)).convert("RGB")
        t0 = _time.time()
        try:
            results = reader.readtext(_np.array(crop), detail=1, paragraph=False)
        except Exception as exc:
            _multi_log.info(f"[DATA-EXTRACTOR] EasyOCR top-band error: {exc}")
            return [], _time.time() - t0
        elapsed = _time.time() - t0
        boxes = []
        for item in results:
            try:
                bbox, text, conf = item[0], item[1], (item[2] if len(item) > 2 else 0.0)
            except Exception:
                continue
            xs = [p[0] for p in bbox]; ys = [p[1] for p in bbox]
            x0 = min(xs) + bx0; x1 = max(xs) + bx0
            y0 = min(ys) + by0; y1 = max(ys) + by0
            boxes.append({"text": text, "conf": float(conf),
                          "x0": x0, "y0": y0, "x1": x1, "y1": y1,
                          "cx": (x0 + x1) / 2.0, "cy": (y0 + y1) / 2.0})
        _multi_log.info(
            f"[DATA-EXTRACTOR] EasyOCR top-band time={elapsed:.2f}s boxes={len(boxes)}")
        return boxes, elapsed

    @staticmethod
    def _de_box_overlap_frac(box, rect):
        """Fraction of the box's area that lies inside rect [x0,y0,x1,y1]."""
        ix0 = max(box["x0"], rect[0]); iy0 = max(box["y0"], rect[1])
        ix1 = min(box["x1"], rect[2]); iy1 = min(box["y1"], rect[3])
        iw = max(0.0, ix1 - ix0); ih = max(0.0, iy1 - iy0)
        inter = iw * ih
        barea = max(1.0, (box["x1"] - box["x0"]) * (box["y1"] - box["y0"]))
        return inter / barea

    def _de_assign_boxes_to_fields(self, boxes, field_rects):
        """
        Assign each EasyOCR box to the best-matching field.  A box matches a field
        when its center is inside the field rect (score 1.0) or it overlaps the
        rect by enough area.  Returns {field: [box, ...]} (best field per box).
        """
        assigned = {f: [] for f in field_rects}
        for box in boxes:
            best_f = None; best_score = 0.0
            for f, rect in field_rects.items():
                center_in = (rect[0] <= box["cx"] <= rect[2]
                             and rect[1] <= box["cy"] <= rect[3])
                frac = self._de_box_overlap_frac(box, rect)
                score = 1.0 if center_in else frac
                if score > best_score:
                    best_score = score; best_f = f
            if best_f is not None and best_score >= 0.40:
                assigned[best_f].append(box)
        return assigned

    def _de_pick_from_boxes(self, fname, ftype, boxes):
        """
        Choose the best parsed value for a field from its assigned EasyOCR boxes.
        Returns (value, raw, status).  raw is the EasyOCR text that produced the
        value.  status is ok / suspicious; None value → caller runs fallback.
        """
        from collections import Counter
        if not boxes:
            return None, "", "missing"
        # Prefer higher-confidence boxes first.
        boxes = sorted(boxes, key=lambda b: b["conf"], reverse=True)
        votes = Counter(); raw_by = {}
        for b in boxes:
            raw = b["text"]
            if ftype == "number":
                for val in (self._de_parse_number(raw, all_candidates=True) or []):
                    if 5 <= len(val) <= 7:
                        votes[val] += 1
                        raw_by.setdefault(val, raw)
            else:
                val = self._de_parse_resource(raw)
                if val:
                    votes[val] += 1
                    raw_by.setdefault(val, raw)
        if not votes:
            return None, (boxes[0]["text"] if boxes else ""), "suspicious"
        if ftype == "number":
            # Prefer the longest strongly-supported numeric reading.
            maxv = max(votes.values())
            strong = [v for v, n in votes.items() if n >= maxv]
            best = sorted(strong, key=len, reverse=True)[0]
        else:
            # Prefer suffixed, then decimal, then votes.
            def _k(v):
                return (1 if v[-1] in "KMB" else 0, 1 if "." in v else 0, votes[v])
            best = max(votes, key=_k)
        status = "ok"
        if ftype == "resource" and best[-1] not in "KMB":
            status = "suspicious"
        return best, raw_by.get(best, best), status

    # ══════════════════════════════════════════════════════════════════════
    # Per-page extractors (controller-only).  Each returns an ordered dict
    # {column: field_dict}, where field_dict = {value, raw, engine, status,
    # region, reason, time}.  None of these fabricate values: a field that
    # cannot be read is left at its default with status 'suspicious'/'failed'
    # and a reason, and count-like fields default to '0'.
    # ══════════════════════════════════════════════════════════════════════
    def _de_ocr_region(self, pil_img, rect, sx, sy, whitelist="", psm=7,
                       engine="auto"):
        """
        OCR a single base-coord region.  Tries EasyOCR first when engine is
        'auto'/'easyocr' and the reader is available, else Tesseract.  Returns
        (text, used_engine).  Never raises.
        """
        r = self._de_scale_rect(rect, sx, sy)
        try:
            crop = pil_img.crop((r[0], r[1], r[2], r[3])).convert("RGB")
        except Exception:
            return "", "none"
        # EasyOCR primary when available.
        if engine in ("auto", "easyocr"):
            reader = self._de_get_easyocr()
            if reader is not None:
                try:
                    import numpy as _np
                    res = reader.readtext(_np.array(crop), detail=0, paragraph=False)
                    txt = " ".join(res).strip() if res else ""
                    if txt:
                        return txt, "easyocr"
                except Exception:
                    pass
        # Tesseract fallback.
        try:
            txt = self._de_tess_read(crop, whitelist, psm=psm,
                                     timeout=self.DE_TESS_TIMEOUT_DEEP)
            return (txt or ""), "tesseract"
        except Exception:
            return "", "tesseract"

    @staticmethod
    def _de_parse_coordinate(text):
        """Parse a map coordinate to '[X,Y]'.  Accepts X:123 Y:456 / 123,456 /
        [123,456] / noisy 'X 536 Y 385'.  Returns '' if not confidently parsed."""
        import re as _re
        if not text:
            return ""
        t = text.replace("：", ":").replace("，", ",")
        # X:.. Y:.. form
        m = _re.search(r"[Xx]\D{0,3}(\d{1,4}).{0,6}?[Yy]\D{0,3}(\d{1,4})", t)
        if not m:
            m = _re.search(r"\[?\s*(\d{1,4})\s*[,xX]\s*(\d{1,4})\s*\]?", t)
        if not m:
            nums = _re.findall(r"\d{1,4}", t)
            if len(nums) >= 2:
                return f"[{nums[0]},{nums[1]}]"
            return ""
        return f"[{m.group(1)},{m.group(2)}]"

    @staticmethod
    def _de_parse_bridge_level(text):
        """Extract the bridge/app level number from 'BridgeLv. 18' style text."""
        import re as _re
        if not text:
            return ""
        m = _re.search(r"[Bb]ridge\s*[Ll]v\.?\s*(\d{1,2})", text)
        if m:
            return m.group(1)
        # Fallback: a lone 'Lv. NN' (avoid requirement 'Lv. 18/Lv. 17' double form)
        m2 = _re.search(r"[Ll]v\.?\s*(\d{1,2})(?!\s*/)", text)
        return m2.group(1) if m2 else ""

    @staticmethod
    def _de_parse_server_number(text):
        """Extract a server number (3-5 digits, optional leading '#')."""
        import re as _re
        if not text:
            return ""
        m = _re.search(r"#\s*(\d{3,5})", text)
        if m:
            return m.group(1)
        nums = _re.findall(r"\d{3,5}", text)
        return nums[0] if nums else ""

    @staticmethod
    def _de_parse_inventory_count(text):
        """Parse an inventory count like 'x291' / '×291' / '291'."""
        import re as _re
        if not text:
            return ""
        m = _re.search(r"[x×X]\s*(\d{1,5})", text)
        if m:
            return m.group(1)
        nums = _re.findall(r"\d{1,5}", text.replace(",", ""))
        return nums[-1] if nums else ""

    def _de_field(self, value, raw, engine, status, region, reason="", t=0.0):
        return {"value": value if value is not None else "", "raw": raw,
                "engine": engine, "status": status, "rect": region,
                "reason": reason, "time": round(t, 2), "candidates": []}

    def _de_extract_game_main_map(self, img, sx, sy):
        import time as _t
        t0 = _t.time()
        rect = self.DE_MAP_COORD_RECT
        region = self._de_scale_rect(rect, sx, sy)
        # First try a single OCR of the whole badge.
        txt, eng = self._de_ocr_region(img, rect, sx, sy,
                                       whitelist="0123456789XYxy:,[] ")
        coord = self._de_parse_coordinate(txt)
        # If the whole-badge read didn't yield two clean numbers (e.g. Tesseract
        # glued '536385'), OCR the X and Y halves separately and combine.
        if not coord or txt.replace(" ", "").isdigit():
            # Explicit X / Y number sub-regions (the badge is "Xicon NNN  Yicon NNN";
            # the icons sit at the left of each half).  Numbers occupy roughly the
            # right ~60% of each half, so crop generously to avoid clipping.
            x0, y0, x1, y1 = rect
            w = x1 - x0
            lrect = [x0 + int(w * 0.27), y0, x0 + int(w * 0.52), y1]   # X number
            rrect = [x0 + int(w * 0.72), y0, x1, y1]                   # Y number
            lx, _ = self._de_ocr_region(img, lrect, sx, sy, whitelist="0123456789 ")
            ry, _ = self._de_ocr_region(img, rrect, sx, sy, whitelist="0123456789 ")
            import re as _re
            lxn = _re.findall(r"\d{1,4}", lx); ryn = _re.findall(r"\d{1,4}", ry)
            if lxn and ryn:
                coord = f"[{lxn[-1]},{ryn[-1]}]"
                txt = f"{lx} | {ry}"
        if coord:
            return {"ark_map_coordinate": self._de_field(
                coord, txt, eng, "ok", region, "", _t.time() - t0)}
        return {"ark_map_coordinate": self._de_field(
            "", txt, eng, "suspicious", region,
            "coordinate not parsed from region", _t.time() - t0)}

    def _de_extract_app_level(self, img, sx, sy):
        import time as _t
        t0 = _t.time()
        txt, eng = self._de_ocr_region(img, self.DE_ARK_LEVEL_RECT, sx, sy,
                                       whitelist="BridgeLvabcdefg.0123456789 ", psm=7)
        lvl = self._de_parse_bridge_level(txt)
        region = self._de_scale_rect(self.DE_ARK_LEVEL_RECT, sx, sy)
        if lvl:
            return {"app_level": self._de_field(
                lvl, txt, eng, "ok", region, "", _t.time() - t0)}
        return {"app_level": self._de_field(
            "", txt, eng, "suspicious", region,
            "BridgeLv not found in region", _t.time() - t0)}

    def _de_find_green_label_rects(self, img):
        """
        Return a list of candidate green text-line rects (base coords), ordered
        top-to-bottom.  The selected server's name+number and its Lord line are
        both green; the server number lives on the upper (name) line.  Caller OCRs
        each and picks the one with a valid '#NNNN'.
        """
        try:
            import numpy as _np
            arr = _np.array(img.convert("RGB"))
        except Exception:
            return []
        H, W, _ = arr.shape
        R = arr[:, :, 0].astype(int); G = arr[:, :, 1].astype(int); B = arr[:, :, 2].astype(int)
        mask = (G > 140) & (G - R > 40) & (G - B > 40)
        top = int(H * 0.11); bot = int(H * 0.70)
        mask[:top, :] = False; mask[bot:, :] = False
        ys, xs = _np.where(mask)
        if len(xs) < 50:
            return []
        order = _np.argsort(ys); ys_s = ys[order]
        raw_bands = []
        start = ys_s[0]; prev = ys_s[0]
        for y in ys_s[1:]:
            if y - prev > 10:
                raw_bands.append((start, prev)); start = y
            prev = y
        raw_bands.append((start, prev))
        rects = []
        for (a, b) in raw_bands:
            sel = (ys >= a) & (ys <= b)
            if sel.sum() < 120:
                continue
            bx0, bx1 = xs[sel].min(), xs[sel].max()
            if bx1 - bx0 < 70:        # skip the small pin marker blob
                continue
            pad = 30
            # The server number ('#1347') is rendered in WHITE just to the RIGHT
            # of the green name, so extend the rect rightward to include it.
            rects.append([max(0, int(bx0 - pad)), max(0, int(a - 10)),
                          min(W, int(bx1 + 220)), min(H, int(b + 12))])
        rects.sort(key=lambda r: r[1])   # top to bottom
        return rects

    def _de_extract_server(self, img, sx, sy):
        import time as _t, re as _re
        t0 = _t.time()
        reader = self._de_get_easyocr()

        def _ocr(rect):
            crop = img.crop((rect[0], rect[1], rect[2], rect[3])).convert("RGB")
            try:
                crop = crop.resize((crop.width * 3, crop.height * 3))
            except Exception:
                pass
            if reader is not None:
                try:
                    import numpy as _np
                    res = reader.readtext(_np.array(crop), detail=0, paragraph=False)
                    if res:
                        return " ".join(res).strip(), "easyocr"
                except Exception:
                    pass
            return self._de_tess_read(crop, "0123456789#Ll:ordNoam ", psm=7,
                                      timeout=self.DE_TESS_TIMEOUT_DEEP), "tesseract"

        # Primary: green selected-server label lines (top line carries the server
        # number; the lower 'Lord:...#NN' line is skipped by preferring a #NNNN
        # with 3-5 digits on the uppermost qualifying line).
        for grect in self._de_find_green_label_rects(img):
            txt, eng = _ocr(grect)
            # A 'Lord' line would contain 'Lord' / 'ord' — skip it for the number.
            if _re.search(r"[Ll]ord", txt or ""):
                continue
            num = self._de_parse_server_number(txt)
            if num and 3 <= len(num) <= 5:
                return {"server": self._de_field(
                    num, txt, eng, "ok", grect,
                    "green selected-server label", _t.time() - t0)}
        # Fallback: fixed pinned-planet region.
        txt, eng = self._de_ocr_region(img, self.DE_SERVER_RECT, sx, sy,
                                       whitelist="0123456789# ", psm=6)
        num = self._de_parse_server_number(txt)
        region = self._de_scale_rect(self.DE_SERVER_RECT, sx, sy)
        if num:
            return {"server": self._de_field(
                num, txt, eng, "ok", region, "fixed-region fallback",
                _t.time() - t0)}
        return {"server": self._de_field(
            "", txt, eng, "suspicious", region,
            "server number not found (green label + fixed region both failed)",
            _t.time() - t0)}

    def _de_extract_monster(self, img, sx, sy):
        """
        monster_killed: 'yes' when a clear kill/victory cue is present, else 'no'
        when the page is detected but no kill cue is seen.  When the page text is
        unreadable, mark suspicious rather than guessing.
        """
        import time as _t
        t0 = _t.time()
        txt, eng = self._de_ocr_region(img, self.DE_MONSTER_RECT, sx, sy, psm=6)
        region = self._de_scale_rect(self.DE_MONSTER_RECT, sx, sy)
        low = (txt or "").lower()
        if not low.strip():
            return {"monster_killed": self._de_field(
                "", txt, eng, "suspicious", region,
                "monster page text unreadable", _t.time() - t0)}
        kill_cues = ("victory", "defeated", "killed", "reward", "claim", "win")
        if any(c in low for c in kill_cues):
            return {"monster_killed": self._de_field(
                "yes", txt, eng, "ok", region, "kill/reward cue found",
                _t.time() - t0)}
        # Page detected, readable, but no kill cue → 'no' per spec default.
        return {"monster_killed": self._de_field(
            "no", txt, eng, "ok", region,
            "no kill/reward cue seen on detected page", _t.time() - t0)}

    # Resource body-colour → type (HSV hue ranges, degrees).  Crate/coin body.
    DE_RES_TYPE_HUES = {
        "food": (75, 160),       # green crate
        "parts": (175, 250),     # blue crate
        "electric": (250, 300),  # purple crate
        "gas": (0, 20),          # red flame crate (also wraps 340-360)
        "cash": (20, 50),        # orange/gold coins
    }
    # Border-glow rarity colour → pack-size tier (provided rules):
    #   purple = 10m, blue = 200k, yellow = 1.2m or 400k (resolved per type),
    #   green / grey = low-value packs → ignore unless explicitly mapped.
    DE_BORDER_SIZE = {"purple": "10m", "blue": "200k", "yellow": "yellow"}
    # Output-column lookup: (type, size) → column.  400k only for food/parts.
    DE_RES_COLUMN = {
        ("food", "1.2m"): "food_1_2m", ("food", "10m"): "food_10m",
        ("food", "400k"): "food_400k", ("food", "200k"): "food_200k",
        ("parts", "1.2m"): "parts_1_2m", ("parts", "10m"): "parts_10m",
        ("parts", "400k"): "parts_400k", ("parts", "200k"): "parts_200k",
        ("electric", "1.2m"): "electric_1_2m", ("electric", "10m"): "electric_10m",
        ("electric", "200k"): "electric_200k",
        ("gas", "1.2m"): "gas_1_2m", ("gas", "10m"): "gas_10m",
        ("gas", "200k"): "gas_200k",
        ("cash", "1.2m"): "cash_1_2m", ("cash", "10m"): "cash_10m",
        ("cash", "200k"): "cash_200k",
    }

    def _de_cell_count(self, img, cx, cy):
        """OCR the white 'xN' count below an icon centre.  EasyOCR primary (the
        stylised thin digits), Tesseract+threshold fallback.  Returns (count,raw,
        engine)."""
        import numpy as _np
        cy2 = cy + self.DE_INV_COUNT_DY
        x0 = cx - self.DE_INV_COUNT_HALF_W; x1 = cx + self.DE_INV_COUNT_HALF_W
        y0 = cy2 - 28; y1 = cy2 + 30
        try:
            crop = img.crop((x0, y0, x1, y1)).convert("RGB")
        except Exception:
            return "", "", "none"
        reader = self._de_get_easyocr()
        if reader is not None:
            try:
                res = reader.readtext(_np.array(crop), detail=0, paragraph=False,
                                      allowlist="x×0123456789")
                raw = (" ".join(res)).strip() if res else ""
                val = self._de_parse_inventory_count(raw)
                if val:
                    return val, raw, "easyocr"
            except Exception:
                pass
        # Tesseract on a thresholded, upscaled crop.
        try:
            g = _np.array(crop.convert("L"))
            bw = (g > 150).astype("uint8") * 255
            from PIL import Image as _Im
            pil = _Im.fromarray(bw).resize((crop.width * 4, crop.height * 4))
            for psm in (7, 8, 13):
                raw = self._de_tess_read(pil, "x×0123456789", psm=psm,
                                         timeout=self.DE_TESS_TIMEOUT)
                val = self._de_parse_inventory_count(raw)
                if val:
                    return val, raw, "tesseract"
        except Exception:
            pass
        return "", "", "tesseract"

    def _de_cell_duration_badge(self, img, cx, cy):
        """
        OCR the speedup duration badge ('5M','15M','1H','3D','180D'…) which sits
        on the lower portion of the speedup icon.  EasyOCR primary (stylised text
        on a textured icon), Tesseract fallback.  Returns (raw_text, engine).
        """
        import numpy as _np
        # Badge band: lower ~third of the icon, slightly above the count strip.
        half = self.DE_INV_ICON_HALF
        x0 = cx - half + 6; x1 = cx + half - 6
        y0 = cy + int(half * 0.30); y1 = cy + half - 4
        try:
            crop = img.crop((x0, y0, x1, y1)).convert("RGB")
        except Exception:
            return "", "none"
        reader = self._de_get_easyocr()
        if reader is not None:
            try:
                res = reader.readtext(_np.array(crop), detail=0, paragraph=False,
                                      allowlist="0123456789MHDmhd")
                raw = (" ".join(res)).strip() if res else ""
                if raw:
                    return raw, "easyocr"
            except Exception:
                pass
        # Tesseract fallback on an upscaled crop.
        try:
            up = crop.resize((crop.width * 3, crop.height * 3))
            raw = self._de_tess_read(up, "0123456789MHDmhd", psm=7,
                                     timeout=self.DE_TESS_TIMEOUT)
            return (raw or "").strip(), "tesseract"
        except Exception:
            return "", "tesseract"

    def _de_cell_body_hue(self, img, cx, cy):
        """Dominant hue/sat/val of the icon body centre (for type classification)."""
        import numpy as _np, colorsys
        try:
            crop = img.crop((cx - 36, cy - 36, cx + 36, cy + 36)).convert("RGB")
        except Exception:
            return None
        px = _np.array(crop).reshape(-1, 3).astype(float)
        # weight toward saturated pixels (ignore grey background bleed)
        mx = px.max(axis=1); mn = px.min(axis=1)
        sel = px[(mx - mn) > 30]
        use = sel if len(sel) > 30 else px
        r, g, b = use.mean(axis=0) / 255.0
        h, s, v = colorsys.rgb_to_hsv(r, g, b)
        return (int(h * 360), round(s, 2), round(v, 2))

    def _de_icon_ahash(self, img, icon_rect):
        """
        8x8 average-hash of an icon crop → 16-char hex string.  Matches the
        template-pack 'ahash_icon' format so detected cards can be compared to /
        labelled against the pack signatures.  Returns '' on failure.
        """
        try:
            import numpy as _np
            crop = img.crop((icon_rect[0], icon_rect[1],
                             icon_rect[2], icon_rect[3])).convert("L").resize((8, 8))
            a = _np.asarray(crop, dtype=float)
            bits = (a > a.mean()).flatten()
            val = 0
            for bit in bits:
                val = (val << 1) | int(bit)
            return f"{val:016x}"
        except Exception:
            return ""

    @staticmethod
    def _de_ahash_hamming(h1, h2):
        """Hamming distance between two 16-hex ahash strings (0-64); 999 if bad."""
        try:
            return bin(int(h1, 16) ^ int(h2, 16)).count("1")
        except Exception:
            return 999

    def _de_load_inv_other_labels(self):
        """
        Load an optional inventory-other label key that maps a card signature to
        an output field.  Searched (first found wins), relative to the controller
        dir and CWD:
            inventory_other_labels.csv / .json
            inventory_other_label_template.csv
            inventory_other_templates.json
        CSV columns (flexible): one of {ahash_icon|ahash|signature} plus
        {mapped_field|field|label}; optional body_hue.  JSON: list of
        {ahash, field, body_hue?} or a {ahash: field} dict.
        Returns a list of {"ahash","field","body_hue"} (body_hue may be None).
        Cached on self._de_inv_other_labels.  Never raises.
        """
        cached = getattr(self, "_de_inv_other_labels", None)
        if cached is not None:
            return cached
        import os, csv, json
        labels = []
        names = ["inventory_other_labels.csv", "inventory_other_labels.json",
                 "inventory_other_label_template.csv",
                 "inventory_other_templates.json",
                 "inventory_other_label_me.csv"]
        dirs = []
        try:
            dirs.append(os.path.dirname(os.path.abspath(__file__)))
        except Exception:
            pass
        dirs.append(os.getcwd())
        # also look in a 'tp' / template-pack subfolder if present
        for base in list(dirs):
            dirs.append(os.path.join(base, "tp"))
            dirs.append(os.path.join(base, "templates"))
        seen_paths = []
        for d in dirs:
            for nm in names:
                p = os.path.join(d, nm)
                if os.path.isfile(p):
                    seen_paths.append(p)
        for p in seen_paths:
            try:
                if p.lower().endswith(".json"):
                    data = json.load(open(p, encoding="utf-8"))
                    items = (data.items() if isinstance(data, dict)
                             else [(x.get("ahash") or x.get("ahash_icon"),
                                    x.get("field") or x.get("mapped_field"),
                                    x.get("body_hue")) for x in data])
                    for it in items:
                        if isinstance(it, tuple) and len(it) == 2:
                            ah, fld = it; bh = None
                        else:
                            ah, fld, bh = it
                        if ah and fld:
                            labels.append({"ahash": str(ah), "field": str(fld),
                                           "body_hue": bh})
                else:
                    rows = list(csv.DictReader(open(p, encoding="utf-8")))
                    for r in rows:
                        ah = (r.get("ahash_icon") or r.get("ahash")
                              or r.get("signature") or "").strip()
                        fld = (r.get("mapped_field") or r.get("field")
                               or r.get("label") or "").strip()
                        if ah and fld:
                            bh = r.get("body_hue")
                            try:
                                bh = float(bh) if bh not in (None, "") else None
                            except Exception:
                                bh = None
                            labels.append({"ahash": ah, "field": fld,
                                           "body_hue": bh})
            except Exception:
                continue
        self._de_inv_other_labels = labels
        return labels

    def _de_match_inv_other_card(self, ahash, body_hue):
        """
        Match a detected inventory-other card to a labelled template by ahash
        Hamming distance (tie-broken by body-hue closeness).  Returns
        (field, distance, label_ahash) or (None, None, None) if no confident
        match.  Confident = Hamming distance <= 8 (of 64 bits).
        """
        labels = self._de_load_inv_other_labels()
        if not labels or not ahash:
            return None, None, None
        best = None; best_d = 999
        bh = body_hue[0] if isinstance(body_hue, (list, tuple)) else None
        for lab in labels:
            d = self._de_ahash_hamming(ahash, lab["ahash"])
            # small body-hue penalty to break ties
            if bh is not None and lab.get("body_hue") is not None:
                if abs(((bh - lab["body_hue"] + 180) % 360) - 180) > 40:
                    d += 3
            if d < best_d:
                best_d = d; best = lab
        if best is not None and best_d <= 8:
            return best["field"], best_d, best["ahash"]
        return None, None, None

    def _de_cell_border_hue(self, img, cx, cy):
        """Dominant hue of the bright border glow (size/rarity signature)."""
        import numpy as _np, colorsys
        half = self.DE_INV_ICON_HALF
        try:
            reg = _np.array(img.crop((cx - half, cy - half, cx + half, cy + half))
                            .convert("RGB")).astype(int)
        except Exception:
            return None
        h, w, _ = reg.shape
        ring = _np.ones((h, w), bool); ring[12:h - 12, 12:w - 12] = False
        px = reg[ring]
        mx = px.max(axis=1); mn = px.min(axis=1)
        sel = px[((mx - mn) > 40) & (mx > 110)]
        if len(sel) < 20:
            return None
        r, g, b = sel.mean(axis=0) / 255.0
        hh, ss, vv = colorsys.rgb_to_hsv(r, g, b)
        return (int(hh * 360), round(ss, 2), round(vv, 2), len(sel))

    def _de_classify_resource_type(self, body_hue):
        """Map a body hue to a resource type, or None if ambiguous."""
        if not body_hue:
            return None
        h, s, v = body_hue[0], body_hue[1], body_hue[2]
        if s < 0.15:
            return None                         # greyscale → ambiguous
        if h >= 340 or h <= 20:
            return "gas" if s > 0.55 and v < 0.6 else "cash" if 20 <= h <= 50 else "gas"
        for t, (lo, hi) in self.DE_RES_TYPE_HUES.items():
            if lo <= h <= hi:
                return t
        return None

    @staticmethod
    def _de_border_name(border_hue):
        """
        Classify the card's border-glow colour into a rarity name used by the
        pack-size rules: purple / blue / yellow / green / grey / other.
        Hue boundaries are aligned to the template-pack calibration:
            purple 264-322 (=10m), blue 191-245 (=200k), yellow 38-69 (=1.2m/400k),
            green 77-142 (low-value, ignore).  Hues that fall between bands
            (e.g. 176-189 cyan, or orange coin-body bleed) are 'other' → suspicious.
        border_hue is (hue, sat, val, npix) from _de_cell_border_hue.
        """
        if not border_hue:
            return "none"
        h, s = border_hue[0], border_hue[1]
        if 264 <= h <= 322:
            return "purple"          # → 10m
        if 191 <= h <= 245:
            return "blue"            # → 200k
        if 38 <= h <= 69:
            return "yellow"          # → 1.2m or 400k
        if 77 <= h <= 142:
            return "green"           # low-value → ignore
        # Low-saturation bluish frames not caught above read as grey (ignore).
        if 142 < h < 191 and s < 0.45:
            return "grey"
        return "other"

    def _de_resolve_pack_size(self, rtype, border_name, count, order_hint=None):
        """
        Resolve a pack size ('1.2m'/'10m'/'400k'/'200k') from the border colour
        per the provided rules, or (None, reason) when it should be ignored or is
        ambiguous.  `order_hint` (optional) resolves yellow food/parts by
        inventory ordering: '1.2m' if the yellow card precedes the type's
        purple/10m card, '400k' if it follows.  Falls back to the count>50
        heuristic only when no ordering context is available.
        Returns (size_or_None, reason).
        """
        if border_name in ("green", "grey", "none", "other"):
            return None, f"{border_name} border = low-value/ignored pack"
        if border_name == "purple":
            return "10m", "purple border = 10m"
        if border_name == "blue":
            return "200k", "blue border = 200k"
        if border_name == "yellow":
            # electric/gas/cash have no 400k → yellow is always 1.2m.
            if rtype in ("electric", "gas", "cash"):
                return "1.2m", "yellow + electric/gas/cash = 1.2m (no 400k for these)"
            # food/parts: ordering context first.
            if order_hint in ("1.2m", "400k"):
                why = ("before type's 10m in order" if order_hint == "1.2m"
                       else "after type's 10m in order")
                return order_hint, f"yellow food/parts resolved by ordering ({why})"
            # Fallback: count heuristic (1.2m packs usually held in larger numbers).
            try:
                n = int(str(count))
            except Exception:
                n = -1
            if n < 0:
                return None, "yellow food/parts but count unreadable → ambiguous"
            if n > 50:
                return "1.2m", f"yellow food/parts, no ordering ctx, count {n}>50 → 1.2m"
            return "400k", f"yellow food/parts, no ordering ctx, count {n}<=50 → 400k"
        return None, f"{border_name} border unmapped"

    def _de_detect_grid_cards(self, img, sx, sy):
        """
        Attempt DYNAMIC detection of card cells inside the grid region
        (DE_INV_GRID_RECT).  Cards are bright, near-square blobs on a dark panel.
        Returns (centers, used_dynamic): centers is a list of (cx,cy) in image
        coords; used_dynamic is True only when detection produced a plausible
        3-column grid.  On any doubt returns ([], False) so the caller falls back
        to the calibrated anchors.  Never raises.
        """
        try:
            import numpy as _np
            r = self._de_scale_rect(self.DE_INV_GRID_RECT, sx, sy)
            arr = _np.array(img.convert("RGB")).astype(int)
            H, W, _ = arr.shape
            x0, y0, x1, y1 = max(0, r[0]), max(0, r[1]), min(W, r[2]), min(H, r[3])
            sub = arr[y0:y1, x0:x1]
            bright = (sub.max(axis=2) > 70)
            # Column profile → expect 3 strong bands.
            col = bright.sum(axis=0).astype(float)
            row = bright.sum(axis=1).astype(float)

            def bands(prof, thr, minw):
                on = prof > thr; out = []; s = None
                for i, v in enumerate(on):
                    if v and s is None:
                        s = i
                    if not v and s is not None:
                        if i - s >= minw:
                            out.append((s, i))
                        s = None
                if s is not None and len(on) - s >= minw:
                    out.append((s, len(on)))
                return out

            cb = bands(col, col.max() * 0.35, 70)
            rb = bands(row, row.max() * 0.35, 70)
            if len(cb) != 3 or len(rb) < 2:
                return [], False
            cxs = [x0 + (a + b) // 2 for a, b in cb]
            cys = [y0 + (a + b) // 2 for a, b in rb]
            # Sanity: roughly even column spacing.
            gaps = [cxs[i + 1] - cxs[i] for i in range(len(cxs) - 1)]
            if max(gaps) - min(gaps) > 60:
                return [], False
            centers = [(cx, cy) for cy in cys for cx in cxs]
            # Safety: the count crop offset is calibrated against the anchor
            # centres.  If a detected centre is close to a calibrated anchor,
            # snap to the anchor so the count/badge crops stay aligned; only keep
            # a purely-dynamic centre when it is far from every anchor (genuinely
            # different scroll/layout).  This keeps dynamic detection from quietly
            # degrading the well-calibrated common case.
            ax = [int(v * sx) for v in self.DE_INV_COL_CX]
            ay = [int(v * sy) for v in self.DE_INV_ROW_CY]
            snapped = []
            for (cx, cy) in centers:
                nx = min(ax, key=lambda a: abs(a - cx))
                ny = min(ay, key=lambda a: abs(a - cy))
                sx_ok = abs(nx - cx) <= 30
                sy_ok = abs(ny - cy) <= 30
                snapped.append((nx if sx_ok else cx, ny if sy_ok else cy))
            return snapped, True
        except Exception:
            return [], False

    def _de_read_grid_cells(self, img, sx, sy, read_badge=False):
        """
        Read the visible inventory grid cells.  Tries DYNAMIC card detection
        first (inside DE_INV_GRID_RECT); if that doesn't yield a clean 3-column
        grid, falls back to the CALIBRATED anchors (DE_INV_COL_CX × DE_INV_ROW_CY).
        Returns (cells, dynamic_used).  Each cell:
            {row,col,cx,cy, count, count_raw, count_engine,
             body_hue, border_hue, icon_rect, [badge, badge_engine]}
        Row/col are visible-slot anchors for DEBUG ONLY — never item identity.
        A cell with a coloured body but unreadable count is kept with count=''
        (caller marks it suspicious).  When read_badge is True the speedup
        duration badge is also OCR'd.
        """
        centers, dynamic_used = self._de_detect_grid_cards(img, sx, sy)
        if dynamic_used and centers:
            ncols = 3
            anchor_iter = [(i // ncols, i % ncols, cx, cy)
                           for i, (cx, cy) in enumerate(centers)]
        else:
            anchor_iter = []
            for ri, cy0 in enumerate(self.DE_INV_ROW_CY):
                for ci, cx0 in enumerate(self.DE_INV_COL_CX):
                    anchor_iter.append((ri, ci, int(cx0 * sx), int(cy0 * sy)))
        cells = []
        for (ri, ci, cx, cy) in anchor_iter:
            body = self._de_cell_body_hue(img, cx, cy)
            populated = bool(body and (body[1] > 0.18 and body[2] > 0.2))
            count, craw, ceng = self._de_cell_count(img, cx, cy)
            if not populated and not count:
                continue
            border = self._de_cell_border_hue(img, cx, cy)
            ir = [cx - self.DE_INV_ICON_HALF, cy - self.DE_INV_ICON_HALF,
                  cx + self.DE_INV_ICON_HALF, cy + self.DE_INV_ICON_HALF]
            cell = {"row": ri, "col": ci, "cx": cx, "cy": cy,
                    "count": count, "count_raw": craw,
                    "count_engine": ceng, "body_hue": body,
                    "border_hue": border, "icon_rect": ir}
            if read_badge:
                braw, beng = self._de_cell_duration_badge(img, cx, cy)
                cell["badge"] = braw; cell["badge_engine"] = beng
            cells.append(cell)
        return cells, dynamic_used

    @staticmethod
    def _de_badge_to_speedup_col(badge):
        """
        Map a speedup duration badge to its output column.  Accepts the many
        variants the badge/label can take: '5m','5min','5 min','5M','1h','1hour',
        '3d','3 days','180d','180day', etc.  Returns (column, normalized) or
        (None, '') if no duration is recognised.
        Unit letters on the in-game badge: M = minutes, H = hours, D = days.
        """
        import re as _re
        if not badge:
            return None, ""
        b = badge.lower().replace(" ", "")
        # number + unit (min/m, hour/h, day/d).  'min'/'hour'/'day' checked first.
        m = _re.search(r"(\d{1,3})\s*(min|m|hour|hr|h|days?|d)", b)
        if not m:
            return None, ""
        n = int(m.group(1)); u = m.group(2)
        if u in ("min", "m"):
            unit = "min"
        elif u in ("hour", "hr", "h"):
            unit = "hour"
        else:
            unit = "day"
        table = {
            (5, "min"): "speedup_5min", (15, "min"): "speedup_15min",
            (30, "min"): "speedup_30min", (1, "hour"): "speedup_1hour",
            (3, "hour"): "speedup_3hour", (8, "hour"): "speedup_8hour",
            (24, "hour"): "speedup_24hour", (3, "day"): "speedup_3days",
            (30, "day"): "speedup_30days", (180, "day"): "speedup_180days",
        }
        col = table.get((n, unit))
        return col, f"{n}{unit}"

    def _de_extract_inventory_grid(self, img, sx, sy, page):
        """
        Real-pass extractor for the scrolling 3-column inventory grids
        (speedup / resources / inventory other).

        Card identity comes from each card itself (icon/body colour, border-glow
        rarity, OCR count) — NOT from its grid row/col, since the page scrolls and
        the same item can appear in different cells.  For `resources`, type
        (body colour) + pack size (border colour, per the provided rules) map to
        an output column and the OCR'd count is written when confident.  Cards
        that are visible but unreadable/ambiguous are marked suspicious with a
        debug signature — never assigned to a possibly-wrong column, never faked.
        Missing items keep the '0' default.
        """
        import time as _t
        t0 = _t.time()
        cols = self.DE_PAGE_COLUMN_MAP.get(page, [])
        region = self._de_scale_rect(self.DE_INV_GRID_RECT, sx, sy)
        cells, dynamic_used = self._de_read_grid_cells(
            img, sx, sy, read_badge=(page == "speedup"))
        out = {col: self._de_field("0", "", "none", "suspicious", region,
                                   "not seen in this screenshot (default 0)", 0.0)
               for col in cols}

        matched = 0
        matched_cols = set()
        suspicious_cards = []

        if page == "resources":
            # First pass: classify every visible card (type + border) in reading
            # order (row-major).  Reading order approximates inventory order, used
            # to resolve yellow food/parts (1.2m before the type's 10m, 400k after).
            classified = []
            for idx, c in enumerate(cells):
                rtype = self._de_classify_resource_type(c["body_hue"])
                bname = self._de_border_name(c["border_hue"])
                classified.append((idx, c, rtype, bname))
            # Per food/parts type, find the reading-order index of the 10m (purple).
            purple_idx = {}
            for t in ("food", "parts"):
                idxs = [i for (i, c, rt, bn) in classified
                        if rt == t and bn == "purple"]
                if idxs:
                    purple_idx[t] = min(idxs)
            for (idx, c, rtype, bname) in classified:
                rc = f"r{c['row']}c{c['col']}"
                if not c["count"]:
                    suspicious_cards.append(
                        f"{rc} type={rtype or '?'} border={bname} count=UNREADABLE")
                    _multi_log.info(
                        f"[DATA-EXTRACTOR] grid resources {rc} resource_type={rtype} "
                        f"border_color={bname} count_raw={c['count_raw']!r} "
                        f"status=suspicious reason=count unreadable")
                    continue
                if rtype is None:
                    suspicious_cards.append(f"{rc} type=? count={c['count']}")
                    _multi_log.info(
                        f"[DATA-EXTRACTOR] grid resources {rc} body={c['body_hue']} "
                        f"count={c['count']} status=suspicious reason=type unclear")
                    continue
                order_hint = None
                if bname == "yellow" and rtype in ("food", "parts") \
                        and rtype in purple_idx:
                    order_hint = "1.2m" if idx < purple_idx[rtype] else "400k"
                size, reason = self._de_resolve_pack_size(
                    rtype, bname, c["count"], order_hint)
                col = self.DE_RES_COLUMN.get((rtype, size)) if size else None
                if col and col in out:
                    out[col] = self._de_field(
                        c["count"], c["count_raw"], c["count_engine"], "ok",
                        c["icon_rect"],
                        f"type={rtype} border={bname} size={size}; {reason}",
                        _t.time() - t0)
                    matched += 1; matched_cols.add(col)
                    _multi_log.info(
                        f"[DATA-EXTRACTOR] grid resources {rc} resource_type={rtype} "
                        f"border_color={bname} resolved_size={size} "
                        f"count_raw={c['count_raw']!r} count={c['count']} "
                        f"mapped_field={col} status=ok reason={reason}")
                else:
                    suspicious_cards.append(
                        f"{rc} type={rtype} border={bname} count={c['count']} "
                        f"(size={size or '?'})")
                    _multi_log.info(
                        f"[DATA-EXTRACTOR] grid resources {rc} resource_type={rtype} "
                        f"border_color={bname} resolved_size={size or 'unknown'} "
                        f"count={c['count']} status=suspicious reason={reason}")

        elif page == "speedup":
            # Identify each card by its DURATION BADGE (not row/col) and map to the
            # matching speedup column; count comes from the same card.
            for c in cells:
                rc = f"r{c['row']}c{c['col']}"
                badge_raw = c.get("badge", "")
                col, dur_norm = self._de_badge_to_speedup_col(badge_raw)
                if not col:
                    suspicious_cards.append(
                        f"{rc} duration_raw={badge_raw!r} count={c['count'] or '?'} "
                        f"(duration unrecognised)")
                    _multi_log.info(
                        f"[DATA-EXTRACTOR] grid speedup {rc} duration_raw={badge_raw!r} "
                        f"duration=unknown count_raw={c['count_raw']!r} "
                        f"mapped_field=none status=suspicious "
                        f"reason=duration badge not recognised")
                    continue
                if not c["count"]:
                    suspicious_cards.append(
                        f"{rc} duration={col} count=UNREADABLE")
                    _multi_log.info(
                        f"[DATA-EXTRACTOR] grid speedup {rc} duration_raw={badge_raw!r} "
                        f"duration={col} count_raw={c['count_raw']!r} "
                        f"mapped_field={col} status=suspicious "
                        f"reason=duration ok but count unreadable")
                    continue
                if col in out:
                    out[col] = self._de_field(
                        c["count"], c["count_raw"], c["count_engine"], "ok",
                        c["icon_rect"],
                        f"duration badge {dur_norm} ({c.get('badge_engine','')})",
                        _t.time() - t0)
                    matched += 1; matched_cols.add(col)
                    _multi_log.info(
                        f"[DATA-EXTRACTOR] grid speedup {rc} "
                        f"duration_raw={badge_raw!r} duration={col} "
                        f"count_raw={c['count_raw']!r} count={c['count']} "
                        f"mapped_field={col} status=ok reason=duration badge OCR")

        else:
            # inventory other: match each card to a LABELLED template by signature.
            # If no label key is present (or no confident match), keep suspicious
            # and expose the signature so the user can label it later — never guess.
            labels = self._de_load_inv_other_labels()
            have_labels = bool(labels)
            for c in cells:
                rc = f"r{c['row']}c{c['col']}"
                sig = self._de_icon_ahash(img, c["icon_rect"])
                field, dist, _lab = (self._de_match_inv_other_card(sig, c["body_hue"])
                                     if have_labels else (None, None, None))
                if field and field in out:
                    if not c["count"]:
                        suspicious_cards.append(
                            f"{rc} sig={sig} matched={field} count=UNREADABLE")
                        _multi_log.info(
                            f"[DATA-EXTRACTOR] grid inventory_other {rc} "
                            f"template_id={field} ahash={sig} count_raw="
                            f"{c['count_raw']!r} matched_field={field} "
                            f"status=suspicious reason=matched but count unreadable")
                        continue
                    out[field] = self._de_field(
                        c["count"], c["count_raw"], c["count_engine"], "ok",
                        c["icon_rect"],
                        f"template label match (ahash dist {dist})", _t.time() - t0)
                    matched += 1; matched_cols.add(field)
                    _multi_log.info(
                        f"[DATA-EXTRACTOR] grid inventory_other {rc} "
                        f"ahash={sig} count_raw={c['count_raw']!r} count={c['count']} "
                        f"matched_field={field} status=ok "
                        f"reason=template label match dist={dist}")
                else:
                    reason = ("no confident template match for signature"
                              if have_labels
                              else "no inventory_other label file found for signature")
                    suspicious_cards.append(
                        f"{rc} sig={sig} body_hue={c['body_hue']} "
                        f"count={c['count'] or '?'} (unmatched)")
                    _multi_log.info(
                        f"[DATA-EXTRACTOR] grid inventory_other {rc} "
                        f"template_id=unknown ahash={sig} body_hue={c['body_hue']} "
                        f"count_raw={c['count_raw']!r} count={c['count']} "
                        f"matched_field=none status=suspicious reason={reason}")

        n_cards = len(cells)
        n_susp = len([col for col in cols if col not in matched_cols])
        fallback_used = (not dynamic_used)
        summary = (f"page={page} cards detected={n_cards} matched fields={matched} "
                   f"missing fields={len(cols) - matched} "
                   f"suspicious fields={n_susp} "
                   f"dynamic_detect={dynamic_used} fallback_used={fallback_used}")
        if fallback_used:
            summary += " reason=fixed visible slot anchors used"
        detail = (" | " + "; ".join(suspicious_cards)) if suspicious_cards else ""
        _multi_log.info(f"[DATA-EXTRACTOR] grid {summary}{detail}")
        for col in cols:
            if out[col]["value"] == "0" and out[col]["status"] == "suspicious":
                out[col]["reason"] = summary + detail
                out[col]["time"] = round(_t.time() - t0, 2)
        return out

    def _de_filter_selected(self, fields_out, sel_fields):
        """Keep only user-selected fields (sel_fields None → keep all)."""
        if sel_fields is None:
            return fields_out
        return {k: v for k, v in fields_out.items() if k in sel_fields}

    def _de_selected_ocr_mode(self):
        try:
            return (self._de_ocr_mode_var.get() or self.DE_OCR_MODE_DEFAULT)
        except Exception:
            return self.DE_OCR_MODE_DEFAULT

    def _de_fields_for_page(self, page):
        """
        Return the list of selectable field names for a target page.

        For 'target app main' these are the internal extractor field names
        (gold/power/food/parts/electric/gas/cash).  For every other page they are
        the page's output-column names (from DE_PAGE_COLUMN_MAP).  'Auto' returns
        [] until a page is actually detected.
        """
        if not page or page == "Auto":
            return []
        if page == "target app main":
            return ["gold", "power", "food", "parts", "electric", "gas", "cash"]
        return list(self.DE_PAGE_COLUMN_MAP.get(page, []))

    def _de_rebuild_field_checks(self, page):
        """Rebuild the field checklist for the given page (called on page change)."""
        frame = getattr(self, "_de_fields_frame", None)
        if frame is None:
            return
        for w in frame.winfo_children():
            w.destroy()
        self._de_field_vars = {}
        implemented = page in self.DE_IMPLEMENTED_PAGES
        fields = self._de_fields_for_page(page)

        def _on_field_toggle():
            if self._de_field_vars and not all(
                    v.get() for v in self._de_field_vars.values()):
                self._de_field_all_var.set(False)

        if not fields:
            msg = ("select Detect to choose fields" if page == "Auto"
                   else "no fields for this page")
            tk.Label(frame, text=msg, font=("", 9, "italic"),
                     bg=frame["bg"], fg="#888").pack(side=tk.LEFT, padx=4)
        self._de_field_all_var.set(True)
        # Placeholder (unimplemented) pages: show fields but greyed/disabled so the
        # user sees the schema without implying extraction works yet.
        state = tk.NORMAL if implemented else tk.DISABLED
        for fname in fields:
            var = tk.BooleanVar(value=True)
            self._de_field_vars[fname] = var
            try:
                cb = tk.Checkbutton(
                    frame, text=fname, variable=var, command=_on_field_toggle,
                    font=("", 9), bg=frame["bg"],
                    fg=("#cfcfcf" if implemented else "#777"),
                    selectcolor="#2a2a2a", activebackground=frame["bg"],
                    state=state)
                cb.pack(side=tk.LEFT)
            except Exception:
                pass

    def _de_on_target_changed(self):
        page = self._de_target_var.get()
        self._de_rebuild_field_checks(page)
        if page in self.DE_IMPLEMENTED_PAGES:
            self._de_set_status(f"Target page: {page}.")
        elif page == "Auto":
            self._de_set_status("Target page: Auto (fields shown after detection).")
        else:
            self._de_set_status(
                f"Target page: {page} — no extractor configured yet "
                f"(schema fields shown for reference).")

    @staticmethod
    def _de_resource_to_million(value):
        """
        Convert a displayed resource string to its value in MILLIONS.
            370K  -> 0.37     30.5K -> 0.0305
            383M  -> 383      9.4M  -> 9.4      57.0M -> 57
            140K  -> 0.14     1.6M  -> 1.6
        Returns a trimmed string (no trailing zeros), or "" if unparseable.
        """
        import re as _re
        if value is None:
            return ""
        s = str(value).strip().upper().replace(",", "")
        m = _re.match(r"^(\d+(?:\.\d+)?)([KMB])?$", s)
        if not m:
            return ""
        num = float(m.group(1)); suf = m.group(2) or ""
        if suf == "K":
            millions = num / 1000.0
        elif suf == "M":
            millions = num
        elif suf == "B":
            millions = num * 1000.0
        else:
            # bare number = raw units → convert to millions
            millions = num / 1_000_000.0
        # Trim to a clean string: drop trailing zeros but keep precision.
        out = f"{millions:.6f}".rstrip("0").rstrip(".")
        return out if out else "0"

    def _de_default_row(self):
        """Fresh combined output row: counts default to '0', non-count fields ''."""
        row = {}
        for col in self.DE_OUTPUT_COLUMNS:
            row[col] = "" if col in self.DE_BLANK_DEFAULT_COLUMNS else "0"
        return row

    def _de_ensure_row(self):
        if self._de_current_row is None:
            self._de_current_row = self._de_default_row()
        return self._de_current_row

    def _de_row_tsv(self, with_headers=False):
        """Tab-separated current row (optionally a header line too)."""
        row = self._de_ensure_row()
        vals = "\t".join(str(row.get(c, "")) for c in self.DE_OUTPUT_COLUMNS)
        if with_headers:
            return "\t".join(self.DE_OUTPUT_COLUMNS) + "\n" + vals
        return vals

    def _de_row_json(self):
        import json as _json
        return _json.dumps(self._de_ensure_row(), indent=2)

    @staticmethod
    def _de_tess_read(pil_crop, whitelist, psm=7, timeout=None):
        """
        Run Tesseract on a crop with a hard timeout so a single slow call cannot
        freeze extraction.  On timeout (or any tesseract error) returns "".
        """
        import pytesseract as _pt
        cfg = f"--oem 1 --psm {psm}"
        if whitelist:
            cfg += f" -c tessedit_char_whitelist={whitelist}"
        if timeout is None:
            timeout = ControllerUI.DE_TESS_TIMEOUT
        try:
            return _pt.image_to_string(pil_crop, config=cfg, timeout=timeout).strip()
        except RuntimeError:
            # pytesseract raises RuntimeError("Tesseract process timeout") on timeout
            return ""
        except Exception:
            return ""

    # Extra OCR rect CANDIDATES per target-app-main field (base 1920×1080).
    # The configured rect is always tried first; these widen/shift to recover
    # clipped leading digits (power "1,") and avoid icons on resource bars.
    DE_FIELD_RECTS = {
        "power":    [[190, 74, 395, 116], [148, 74, 400, 118], [170, 66, 430, 122],
                     [186, 58, 504, 126], [160, 64, 450, 126]],
        "gold":     [[1700, 12, 1918, 80], [1690, 16, 1916, 80]],
        "food":     [[600, 5, 795, 74], [610, 3, 800, 76]],
        "parts":    [[800, 5, 1005, 74], [810, 3, 1008, 76]],
        "electric": [[1035, 5, 1212, 74], [1040, 3, 1216, 76]],
        "gas":      [[1230, 5, 1425, 74], [1235, 3, 1420, 76]],
        "cash":     [[1450, 5, 1618, 74], [1455, 3, 1612, 76]],
    }

    @staticmethod
    def _de_preprocs(crop, scale=4):
        """
        Yield (tag, PIL) preprocessing variants for a crop.  Includes:
          gray (plain), otsu, whitemask (bright-luminance), whitemin (white =
          high min(R,G,B) — cracks white-on-RED/orange resource bars), clahe.
        Pure CPU work; safe to call from the OCR worker thread.
        """
        import numpy as _np
        try:
            import cv2 as _cv2
        except Exception:
            _cv2 = None
        g = crop.convert("L")
        big = g.resize((max(1, g.width * scale), max(1, g.height * scale)))
        arr = _np.array(big)
        out = [("gray", big)]
        if _cv2 is not None:
            _, o = _cv2.threshold(arr, 0, 255, _cv2.THRESH_BINARY + _cv2.THRESH_OTSU)
            if o.mean() < 127:
                o = 255 - o
            out.append(("otsu", Image.fromarray(o)))
            _, wt = _cv2.threshold(arr, 165, 255, _cv2.THRESH_BINARY)
            out.append(("whitemask", Image.fromarray(255 - wt)))
            a = _np.array(crop.convert("RGB")).astype(_np.int16)
            mn = a.min(axis=2)
            m = (mn > 150).astype("uint8") * 255
            out.append(("whitemin",
                        Image.fromarray(255 - m).resize(
                            (max(1, crop.width * scale), max(1, crop.height * scale)))))
            try:
                cl = _cv2.createCLAHE(3.0, (8, 8)).apply(arr)
                _, co = _cv2.threshold(cl, 0, 255, _cv2.THRESH_BINARY + _cv2.THRESH_OTSU)
                if co.mean() < 127:
                    co = 255 - co
                out.append(("clahe", Image.fromarray(co)))
            except Exception:
                pass
        return out

    def _de_ocr_field(self, pil_img, rect, whitelist, engines, ftype, debug_dir, field,
                      sx=1.0, sy=1.0):
        """
        Progressive, budgeted OCR for one field.

        Stage 1 — primary rect, light preprocessing.  If a CLEAN, well-supported
                  value is found (and no close rival disagrees), return at once.
        Stage 2 — only if unconfident: extra rects + full preprocessing, until the
                  per-field tesseract attempt budget (DE_MAX_TESS_ATTEMPTS_PER_FIELD)
                  is exhausted.
        Stage 3 — only if still unconfident/suspicious and EasyOCR is enabled.

        Every tesseract call has a hard timeout (DE_TESS_TIMEOUT) so no single
        crop can hang.  Close rivals (e.g. 383M vs 393M) are never silently
        accepted — a near-tie yields 'suspicious' and triggers EasyOCR.

        Returns (value, raw, engine, status, meta) where meta carries
        {time, attempts, candidates} for per-field logging.
        """
        from collections import Counter
        import re as _re, time as _time

        t_start = _time.time()
        base_rects = self.DE_FIELD_RECTS.get(field, [])
        primary = [list(rect)]
        extra = []
        for br in base_rects:
            sr = self._de_scale_rect(br, sx, sy)
            if sr not in primary and sr not in extra:
                extra.append(sr)
        engines = engines or ["tesseract"]
        saved_crop = {"done": False}   # per-call (parallel-safe); crop is field-named
        max_attempts = (self.DE_MAX_TESS_ATTEMPTS_HARD
                        if field in self.DE_HARD_FIELDS
                        else self.DE_MAX_TESS_ATTEMPTS_PER_FIELD)
        budget = {"n": max_attempts}

        parse_num = lambda r: (self._de_parse_number(r, all_candidates=True) or [])
        parse_res = self._de_parse_resource
        CLEAN_RES = _re.compile(r"^\d+(\.\d+)?[KMB]$")

        def _run_tess(rects, mode, timeout):
            """
            Accumulate votes/raw over rects until the attempt budget runs out.
            mode: 'quick' = otsu+whitemin @ PSM 7 only (one cheap pass per rect,
            so every rect — including the wider ones that recover clipped leading
            digits — gets a vote within a small budget); 'light' = gray/otsu/
            whitemin @ PSM 7&6; 'full' = all preprocs @ PSM 7&6.
            """
            votes = Counter(); raw_by_value = {}
            for r in rects:
                if budget["n"] <= 0:
                    break
                try:
                    crop = pil_img.crop((r[0], r[1], r[2], r[3]))
                except Exception:
                    continue
                if debug_dir and not saved_crop["done"]:
                    try:
                        os.makedirs(debug_dir, exist_ok=True)
                        crop.save(os.path.join(debug_dir, f"{field}.png"))
                        saved_crop["done"] = True
                    except Exception:
                        pass
                variants = self._de_preprocs(crop)
                if mode == "quick":
                    variants = [v for v in variants if v[0] in ("otsu", "whitemin")]
                    psms = (7,)
                elif mode == "light":
                    variants = [v for v in variants
                                if v[0] in ("gray", "otsu", "whitemin")]
                    psms = (7, 6)
                else:
                    psms = (7, 6)
                for tag, v in variants:
                    for psm in psms:
                        if budget["n"] <= 0:
                            return votes, raw_by_value
                        raw = self._de_tess_read(v, whitelist, psm=psm, timeout=timeout)
                        budget["n"] -= 1
                        if not raw:
                            continue
                        if ftype == "number":
                            for val in parse_num(raw):
                                if 5 <= len(val) <= 7:
                                    votes[val] += 1
                                    raw_by_value.setdefault(val, raw)
                        else:
                            val = parse_res(raw)
                            if val:
                                votes[val] += 1
                                raw_by_value.setdefault(val, raw)
            return votes, raw_by_value

        def _merge(dst_v, dst_r, sv, sr):
            for k, n in sv.items():
                dst_v[k] += n
                dst_r.setdefault(k, sr.get(k))

        def _choose_number(votes):
            if not votes:
                return None
            maxv = max(votes.values())
            strong = [v for v, n in votes.items() if n >= maxv * 0.4]
            longest = max(len(v) for v in strong)
            finalists = [v for v in strong if len(v) == longest]
            return sorted(finalists, key=lambda v: votes[v], reverse=True)[0]

        def _choose_resource(votes):
            cands = list(votes.elements())
            if not cands:
                return None, cands
            suf = [c for c in set(cands) if c[-1] in "KMB"]
            pool = suf or list(set(cands))

            def _digits(v):
                return v[:-1].replace(".", "") if v[-1] in "KMB" else v.replace(".", "")

            def _key(val):
                dec = 1 if "." in val else 0
                sfx = 1 if val[-1] in "KMB" else 0
                return (votes[val], dec, sfx)
            best = max(pool, key=_key)

            # Leading-digit recovery: when the winner has no decimal and a LONGER
            # same-suffix candidate ends with the winner's digits (winner looks
            # clipped, e.g. 06K → 106K, 25M → 259M) with >= 40% support, prefer
            # the longer reading.  Decimal winners (3.5M) are complete and exempt.
            bd = _digits(best)
            if "." not in best:
                longer = [c for c in pool
                          if c != best and c[-1] == best[-1]
                          and len(_digits(c)) > len(bd)
                          and _digits(c).endswith(bd)
                          and votes[c] >= max(2, votes[best] * 0.4)]
                if longer:
                    best = sorted(longer, key=lambda c: (votes[c], len(_digits(c))),
                                  reverse=True)[0]

            # Prefer an equivalent decimal reading if the winner has none
            # (e.g. 70M → 7.0M only when same digits; 305K → 30.5K).
            if "." not in best and best[-1] in "KMB":
                for c in pool:
                    if ("." in c and c[-1] == best[-1]
                            and c[:-1].replace(".", "") == best[:-1].replace(".", "")
                            and votes[c] >= votes[best] * 0.5):
                        best = c
                        break
            return best, cands

        def _resource_ambiguous(best, votes):
            """
            True when a competing resource candidate makes `best` uncertain: a
            longer same-suffix reading (possible dropped leading digit) or a
            decimal/non-decimal counterpart with comparable support.  Such cases
            are marked suspicious (and sent to EasyOCR) rather than accepted.
            """
            if best is None:
                return False
            def _digits(v):
                return v[:-1].replace(".", "") if v[-1] in "KMB" else v.replace(".", "")
            bd = _digits(best); bn = votes[best]
            for c, n in votes.items():
                if c == best or not c or n < 2:
                    continue
                if c[-1] != best[-1]:
                    continue
                if len(c) == len(best) and \
                        sum(1 for a, b in zip(c, best) if a != b) == 1:
                    return True   # same-length 1-char rival (e.g. 383M/393M)
                cd = _digits(c)
                if cd != bd and (cd.endswith(bd) or bd.endswith(cd)):
                    return True   # leading-digit drop/insert rival (25M/259M)
                if ("." in c) != ("." in best):
                    # decimal counterpart (1M/1.6M, 305K/30.5K).  Only ambiguous
                    # when the winner is NOT a well-supported decimal: a strong
                    # decimal reading (e.g. 30.5K with many votes) is trustworthy
                    # and a weak non-decimal twin (305K) should not flag it.
                    if "." in best and bn >= 4 and n < bn * 0.6:
                        continue
                    return True   # decimal counterpart conflict
            return False

        def _close_rival(best, votes):
            """
            Detect a confusable rival: same length & suffix, differing by a single
            character (e.g. 383M vs 393M), with meaningful support relative to the
            winner (>= 2 votes and >= 30% of the winner's votes).  Such a near-tie
            must not be accepted as 'ok'.  This bar is safe: across the real
            reference screenshots, NO correct value has any same-length one-char
            rival, so clean fields are never falsely flagged — only genuine
            digit-confusions (the Bat food 383M/393M case) trip it.
            """
            if best is None:
                return None
            bn = votes[best]
            for c, n in votes.items():
                if c == best or len(c) != len(best) or c[-1] != best[-1]:
                    continue
                diff = sum(1 for a, b in zip(c, best) if a != b)
                if diff == 1 and n >= 2 and n >= bn * 0.30:
                    return c
            return None

        def _finish(value, raw, engine, status, votes):
            meta = {"time": round(_time.time() - t_start, 2),
                    "attempts": max_attempts - budget["n"],
                    "candidates": [v for v, _ in
                                   Counter(votes).most_common(4)] if votes else []}
            return value, raw, engine, status, meta

        # ── Stage 1: ONE cheap pass across ALL rects (primary + extra) ──
        # This guarantees the wider rects (which recover clipped leading digits)
        # get a vote even under a small budget, instead of spending it all on the
        # primary rect that often clips.
        all_rects = primary + extra
        votes, raw_by = _run_tess(all_rects, mode="quick", timeout=self.DE_TESS_TIMEOUT)

        if ftype == "number":
            best = _choose_number(votes)
            if best is not None and votes[best] >= 4:
                maxlen = max(len(v) for v, n in votes.items() if n >= votes[best] * 0.5)
                if maxlen <= len(best) and _close_rival(best, votes) is None:
                    return _finish(best, raw_by.get(best, best), "tesseract", "ok", votes)
        else:
            best, cands = _choose_resource(votes)
            if (best is not None and CLEAN_RES.match(best)
                    and self._de_res_stage1_confident(best, votes)
                    and not self._de_resource_decimal_suspect(best, cands)
                    and _close_rival(best, votes) is None):
                return _finish(best, raw_by.get(best, best), "tesseract", "ok", votes)

        # ── Stage 2: deepen with full preprocessing across all rects (budget) ──
        if budget["n"] > 0:
            v2, r2 = _run_tess(all_rects, mode="full", timeout=self.DE_TESS_TIMEOUT)
            _merge(votes, raw_by, v2, r2)

        if ftype == "number":
            best = _choose_number(votes)
            if best is not None:
                rival = _close_rival(best, votes)
                status = "ok" if (votes[best] >= 3 and rival is None) else "suspicious"
                if status == "ok" or "easyocr" not in engines:
                    return _finish(best, raw_by.get(best, best), "tesseract", status, votes)
                tess_best = (best, raw_by.get(best, best))
            else:
                tess_best = None
        else:
            best, cands = _choose_resource(votes)
            if best is not None:
                status = "ok"
                if best[-1] not in "KMB":
                    status = "suspicious"
                rival = _close_rival(best, votes)
                decimal_suspect = self._de_resource_decimal_suspect(best, cands)
                ambiguous = _resource_ambiguous(best, votes)
                has_easy = "easyocr" in engines and self._de_get_easyocr() is not None
                # A confusable near-tie (383M/393M), a dropped-decimal suspicion,
                # or a leading-digit drop/insert conflict is NEVER a clean ok —
                # mark suspicious so it is not silently accepted, and let EasyOCR
                # (if any) arbitrate below.
                if rival is not None or decimal_suspect or ambiguous:
                    status = "suspicious"
                if status == "ok" or not has_easy:
                    return _finish(best, raw_by.get(best, best), "tesseract", status, votes)
                tess_best = (best, raw_by.get(best, best))
            else:
                tess_best = None

        # ── Stage 3: EasyOCR fallback (lazy, deeper timeout) ──
        if "easyocr" in engines:
            reader = self._de_get_easyocr()
            if reader is not None:
                import numpy as _np
                parse = parse_num if ftype == "number" else (lambda r: parse_res(r))
                try:
                    r0 = primary[0]
                    crop = pil_img.crop((r0[0], r0[1], r0[2], r0[3]))
                    for _tag, v in self._de_preprocs(crop):
                        res = reader.readtext(_np.array(v.convert("RGB")), detail=0)
                        raw3 = " ".join(res).strip() if res else ""
                        if ftype == "number":
                            cs = parse(raw3) or []
                            val3 = next((c for c in cs if 5 <= len(c) <= 7), None)
                        else:
                            val3 = parse(raw3)
                        if val3 is not None and not self._de_suspicious_number(val3, ftype):
                            # If EasyOCR agrees with the tesseract winner, upgrade
                            # to ok; otherwise report easyocr's value as fallback.
                            return _finish(val3, raw3, "easyocr", "fallback", votes)
                except Exception:
                    pass

        if tess_best is not None:
            return _finish(tess_best[0], tess_best[1], "tesseract", "suspicious", votes)
        return _finish(None, "", "tesseract", "failed", votes)

    def _de_res_stage1_confident(self, best, votes):
        """
        Stage-1 resource early-exit guard: require a suffix, solid consensus
        (>= 4 votes), a mantissa that isn't suspiciously short (clipped leading
        digit), and no decimal/longer same-suffix rival.
        """
        if best is None or best[-1] not in "KMB":
            return False
        if votes[best] < 4:
            return False
        mant = best[:-1].replace(".", "")
        if len(mant) < 3 and "." not in best:
            return False
        suffix = best[-1]
        best_digits = best[:-1].replace(".", "")
        for c, n in votes.items():
            if c == best or not c or c[-1] != suffix:
                continue
            rival_digits = c[:-1].replace(".", "")
            if n >= max(2, votes[best] * 0.5) and (
                    ("." in c and "." not in best) or
                    len(rival_digits) > len(best_digits)):
                return False
        return True

    @staticmethod
    def _de_resource_decimal_suspect(value, cands):
        """
        Flag a likely-DROPPED decimal ONLY when there is actual evidence of one —
        i.e. some candidate reading for the same field DID contain a decimal that
        parsed to a value with the same digits as the chosen (decimal-less) value.
        A clean reading like 370K / 383M / 313M / 259M / 140K / 190K with NO
        decimal candidate anywhere is NOT suspicious and must not trigger EasyOCR.
        """
        import re as _re
        if "." in value:
            return False
        m = _re.match(r"^(\d+)([KMB])$", value)
        if not m:
            return False
        digits, suffix = m.group(1), m.group(2)
        # Only consider it suspect if a decimal-bearing candidate exists with the
        # SAME suffix and the SAME digit sequence (e.g. value '305K' while '30.5K'
        # was also read).  Otherwise the value is taken at face value.
        for c in cands:
            if "." in c and c[-1] == suffix:
                cdigits = c[:-1].replace(".", "")
                if cdigits == digits:
                    return True
        return False


    @staticmethod
    def _de_clean_digits(raw):
        s = (raw or "").strip()
        s = s.replace("O", "0").replace("o", "0")
        s = s.replace("l", "1").replace("I", "1").replace("|", "1")
        s = s.replace("S", "5").replace("B", "8")
        return s

    @staticmethod
    def _de_parse_number(raw, all_candidates=False):
        """
        Parse a plain/comma integer (gold/power).
        - strip spaces; OCR-correct letters→digits in numeric context
        - if comma grouping is well-formed (e.g. 1,686,752) → join the groups
        - otherwise strip commas and take the LONGEST run of digits, so a
          malformed '1686,75204' yields the full digit run rather than a short
          partial like '1686'
        Returns the digit string (or, if all_candidates=True, the list of all
        plausible digit-string candidates for consensus voting).
        """
        import re as _re
        if raw is None:
            return [] if all_candidates else None
        s = ControllerUI._de_clean_digits(raw.replace(" ", ""))

        # Well-formed grouped number: 1-3 digits then groups of exactly 3.
        grouped = _re.findall(r"\d{1,3}(?:,\d{3})+", s)
        candidates = []
        for g in grouped:
            parts = g.split(",")
            # valid grouping = first 1-3 digits, rest exactly 3
            if 1 <= len(parts[0]) <= 3 and all(len(p) == 3 for p in parts[1:]):
                candidates.append(g.replace(",", ""))

        # All plain digit runs (commas removed) as fallback candidates.
        for run in _re.findall(r"\d+", s.replace(",", "")):
            candidates.append(run)

        candidates = [c for c in candidates if c.isdigit()]
        if all_candidates:
            return candidates
        if not candidates:
            return None
        # Prefer the longest candidate (full value, not a partial group).
        best = max(candidates, key=len)
        return best if best.isdigit() else None

    @staticmethod
    def _de_parse_resource(raw):
        """
        Parse a resource value (30.5K, 370K, 57.0M, 383M, 9.4M, 140K) or plain
        digits.  Handles common OCR icon junk:
          - lowercase k/m/b → uppercase
          - leading icon letter before the number, e.g. 'B30.5K' → '30.5K'
          - stray leading single digit + space from an icon, e.g. '4 380K' → '380K'
          - choose the candidate that carries a K/M/B suffix when present
        Returns the token, or None.
        """
        import re as _re
        if raw is None:
            return None
        s = raw.strip()
        # Normalise suffix case and a couple of safe digit confusions.
        s = (s.replace("k", "K").replace("m", "M").replace("b", "B")
               .replace("|", "1"))
        # '4 380K' (icon digit + space) → drop a lone leading digit chunk if a
        # stronger suffixed token follows.
        # Collect all resource-like tokens.
        toks = _re.findall(r"\d+(?:\.\d+)?[KMB]?", s.replace(",", ""))
        if not toks:
            # Maybe an icon letter is glued to the front (e.g. 'B30.5K' after
            # B→8 would corrupt it, so handle BEFORE digit-correction): retry by
            # stripping leading non-digit, non-sign chars.
            s2 = _re.sub(r"^[^\d]+", "", raw.strip())
            s2 = (s2.replace("k", "K").replace("m", "M").replace("b", "B"))
            toks = _re.findall(r"\d+(?:\.\d+)?[KMB]?", s2.replace(",", ""))
            if not toks:
                return None
        # Prefer a token that has a K/M/B suffix (resources almost always do at
        # the displayed scale); else take the longest numeric token.
        suffixed = [t for t in toks if t[-1] in "KMB"]
        if suffixed:
            # If several, prefer the longest (covers 'B' icon glued: '830.5K'
            # would be one token, but a leading lone digit '4' '380K' yields two
            # tokens and we pick the suffixed '380K').
            token = max(suffixed, key=len)
        else:
            token = max(toks, key=len)
        if not _re.search(r"\d", token):
            return None
        return token

    @staticmethod
    def _de_suspicious_number(value, ftype):
        """Heuristic: is a parsed value implausible enough to warrant fallback?"""
        if value is None:
            return True
        if ftype == "number":
            # Gold/power are usually 4+ digits; a 1-2 digit result is suspect.
            return len(value) < 3
        # resource: a bare number with no suffix and very few digits is suspect.
        if value[-1] not in "KMB":
            return len(value) < 3
        return False


    def _de_selected_target_pages(self):
        """Return the target-page selection as a list for _de_detect_page_for_image."""
        try:
            val = (self._de_target_var.get() or "").strip()
        except Exception:
            val = ""
        if not val:
            val = "target app main"
        return [val]   # "Auto" or a specific page name

    def _de_selected_fields(self):
        """Return the set of selected target-app-main fields, or None for all."""
        sel = getattr(self, "_de_field_vars", None)
        if not sel:
            return None
        try:
            if self._de_field_all_var.get():
                return None   # all
            chosen = [f for f, var in sel.items() if var.get()]
            return chosen or None
        except Exception:
            return None

    def _de_detect_page(self):
        if self._de_image is None:
            self._de_set_status("Upload an image first.")
            return
        if self._de_busy:
            self._de_set_status("busy — please wait.")
            return
        self._de_busy = True
        targets = self._de_selected_target_pages()
        self._de_set_status(f"Detecting page (target={targets[0]})…")
        img = self._de_image.copy()

        def _worker():
            try:
                import time as _time
                t = _time.time()
                page, conf, scores = self._de_detect_page_for_image(img, target_pages=targets)
                self.q.put(("de_page_detected", {"page": page, "confidence": conf,
                                                 "scores": scores, "target": targets[0],
                                                 "detect_secs": round(_time.time() - t, 2)}))
            except Exception as exc:
                self.q.put(("de_error", f"detect error: {exc}"))
        threading.Thread(target=_worker, daemon=True).start()

    def _de_extract_data(self):
        if self._de_image is None:
            self._de_set_status("Upload an image first.")
            return
        if self._de_busy:
            self._de_set_status("busy — please wait.")
            return
        self._de_busy = True
        targets = self._de_selected_target_pages()
        sel_fields = self._de_selected_fields()
        self._de_set_status("Extracting…")
        img = self._de_image.copy()
        debug = bool(self._de_debug_var.get())

        def _worker():
            try:
                import time as _time
                ocr_mode = self._de_selected_ocr_mode()
                auto = (targets[0] == "Auto")

                t_detect = _time.time()
                if auto:
                    # Auto: full detection across enabled pages.
                    page, conf, _scores = self._de_detect_page_for_image(
                        img, target_pages=targets)
                else:
                    # Fix 5: a specific target page skips expensive page detection.
                    page = targets[0]; conf = 1.0; _scores = {}
                    _multi_log.info(
                        f"[DATA-EXTRACTOR] using selected page '{page}' "
                        f"(skipped full detection)")
                detect_secs = round(_time.time() - t_detect, 2)
                self.q.put(("de_page_detected", {"page": page, "confidence": conf,
                                                 "scores": _scores, "target": targets[0],
                                                 "detect_secs": detect_secs}))

                cfg = self._de_load_config()
                if page not in cfg or page not in self.DE_IMPLEMENTED_PAGES:
                    note = (f"No extractor configured for page '{page}' yet."
                            if page in self.DE_PAGE_COLUMN_MAP or page not in cfg
                            else f"Page '{page}' has no extractor yet.")
                    self.q.put(("de_extract_result", {
                        "page": page, "page_confidence": conf, "fields": {},
                        "detect_secs": detect_secs, "extract_secs": 0.0,
                        "note": note}))
                    return

                spec = cfg[page]
                base = spec.get("base_size", [self.DE_BASE_W, self.DE_BASE_H])
                sx = img.width / float(base[0] or self.DE_BASE_W)
                sy = img.height / float(base[1] or self.DE_BASE_H)
                debug_dir = ""
                if debug:
                    debug_dir = os.path.join(self.DE_DEBUG_DIR,
                                             datetime.now().strftime("%Y%m%d_%H%M%S"))

                # ── Dispatch the non-target-app-main pages to their extractors ──
                _page_extractors = {
                    "game main map": self._de_extract_game_main_map,
                    "app level": self._de_extract_app_level,
                    "server": self._de_extract_server,
                    "monster": self._de_extract_monster,
                }
                if page in _page_extractors:
                    t_ext = _time.time()
                    fields_out = _page_extractors[page](img, sx, sy)
                    fields_out = self._de_filter_selected(fields_out, sel_fields)
                    for fname, fd in fields_out.items():
                        _multi_log.info(
                            f"[DATA-EXTRACTOR] page={page} field={fname} "
                            f"time={fd.get('time')}s engine={fd.get('engine')} "
                            f"status={fd.get('status')} value={fd.get('value')} "
                            f"raw={fd.get('raw','')!r} "
                            f"reason={fd.get('reason','')}")
                    extract_secs = round(_time.time() - t_ext, 2)
                    _multi_log.info(
                        f"[DATA-EXTRACTOR] total extraction time={extract_secs}s "
                        f"(page={page})")
                    self.q.put(("de_extract_result", {
                        "page": page, "page_confidence": conf, "fields": fields_out,
                        "debug_dir": debug_dir, "detect_secs": detect_secs,
                        "extract_secs": extract_secs}))
                    return
                if page in ("speedup", "resources", "inventory other"):
                    t_ext = _time.time()
                    fields_out = self._de_extract_inventory_grid(img, sx, sy, page)
                    fields_out = self._de_filter_selected(fields_out, sel_fields)
                    for fname, fd in fields_out.items():
                        _multi_log.info(
                            f"[DATA-EXTRACTOR] page={page} field={fname} "
                            f"status={fd.get('status')} value={fd.get('value')} "
                            f"reason={fd.get('reason','')}")
                    extract_secs = round(_time.time() - t_ext, 2)
                    _multi_log.info(
                        f"[DATA-EXTRACTOR] total extraction time={extract_secs}s "
                        f"(page={page})")
                    self.q.put(("de_extract_result", {
                        "page": page, "page_confidence": conf, "fields": fields_out,
                        "debug_dir": debug_dir, "detect_secs": detect_secs,
                        "extract_secs": extract_secs}))
                    return

                # Ordered field list (stable UI order from config).
                todo = []
                for fname, fspec in spec.get("fields", {}).items():
                    if sel_fields is not None and fname not in sel_fields:
                        continue
                    rect = fspec.get("rect")
                    if not rect or len(rect) != 4:
                        continue
                    todo.append((fname, fspec))
                order = [fn for fn, _ in todo]

                t_ext = _time.time()
                use_easy = (page == "target app main"
                            and ocr_mode in ("EasyOCR primary", "Auto"))

                fields_out = {}
                easy_done = set()

                if use_easy:
                    # ── Fix 1/2/3: ONE EasyOCR top-band pass → assign → parse ──
                    field_rects = {fn: self._de_scale_rect(fs.get("rect"), sx, sy)
                                   for fn, fs in todo}
                    boxes, eo_secs = self._de_easyocr_top_band(img, sx, sy)
                    if boxes:
                        assigned = self._de_assign_boxes_to_fields(boxes, field_rects)
                        for fname, fspec in todo:
                            ftype = fspec.get("type", "number")
                            value, raw, status = self._de_pick_from_boxes(
                                fname, ftype, assigned.get(fname, []))
                            if value is not None and status == "ok":
                                fields_out[fname] = {
                                    "value": value, "raw": raw, "engine": "easyocr",
                                    "status": "ok",
                                    "rect": field_rects[fname], "time": round(eo_secs, 2),
                                    "attempts": 1, "candidates": []}
                                easy_done.add(fname)
                                _multi_log.info(
                                    f"[DATA-EXTRACTOR] field={fname} engine=easyocr "
                                    f"value={value} raw={raw} status=ok")
                    else:
                        _multi_log.info(
                            "[DATA-EXTRACTOR] EasyOCR top-band returned no boxes; "
                            "falling back to Tesseract for all fields")

                # ── Fix 4/6: Tesseract fallback ONLY for missing/suspicious fields ──
                fallback = [(fn, fs) for fn, fs in todo if fn not in easy_done]
                if fallback:
                    from concurrent.futures import ThreadPoolExecutor

                    def _fb_one(fname, fspec):
                        if use_easy:
                            _multi_log.info(
                                f"[DATA-EXTRACTOR] field={fname} missing/suspicious "
                                f"from top-band; running fallback")
                        srect = self._de_scale_rect(fspec.get("rect"), sx, sy)
                        # In EasyOCR-primary mode, allow easyocr inside the field
                        # fallback too (crop-level), then tesseract.
                        engines = fspec.get("ocr", ["tesseract"])
                        value, raw, engine, status, meta = self._de_ocr_field(
                            img, srect, fspec.get("whitelist", ""),
                            engines, fspec.get("type", "number"),
                            debug_dir, fname, sx, sy)
                        return fname, {
                            "value": value if value is not None else "",
                            "raw": raw, "engine": engine, "status": status,
                            "rect": srect, "time": meta.get("time"),
                            "attempts": meta.get("attempts"),
                            "candidates": meta.get("candidates", [])}

                    self.q.put(("de_status",
                                f"Fallback OCR {len(fallback)} field(s)…"))
                    with ThreadPoolExecutor(max_workers=min(len(fallback), 7)) as pool:
                        for fname, fd in pool.map(lambda a: _fb_one(*a), fallback):
                            fields_out[fname] = fd

                # Assemble in stable order + per-field logs.
                ordered = {}
                for fname in order:
                    fd = fields_out.get(fname)
                    if fd is None:
                        continue
                    ordered[fname] = fd
                    cand_txt = ""
                    if fd["status"] in ("suspicious", "failed") and fd.get("candidates"):
                        cand_txt = " candidates=" + ",".join(str(c) for c in fd["candidates"])
                    _multi_log.info(
                        f"[DATA-EXTRACTOR] field={fname} time={fd.get('time')}s "
                        f"engine={fd.get('engine')} status={fd.get('status')} "
                        f"value={fd.get('value')}{cand_txt}")
                fields_out = ordered

                extract_secs = round(_time.time() - t_ext, 2)
                _multi_log.info(
                    f"[DATA-EXTRACTOR] total extraction time={extract_secs}s "
                    f"(mode={ocr_mode})")

                self.q.put(("de_extract_result", {
                    "page": page, "page_confidence": conf, "fields": fields_out,
                    "debug_dir": debug_dir, "detect_secs": detect_secs,
                    "extract_secs": extract_secs}))
            except Exception as exc:
                import traceback as _tb
                self.q.put(("de_error", f"extract error: {exc}\n{_tb.format_exc()}"))
        threading.Thread(target=_worker, daemon=True).start()

    def _de_clear(self):
        self._de_image_path = ""
        self._de_image = None
        self._de_detected_page = None
        self._de_page_confidence = 0.0
        self._de_last_result = None
        self._de_busy = False
        self._de_current_row = self._de_default_row()   # reset combined output row
        self._de_filled_pages = []
        try:
            self._de_tv.delete(*self._de_tv.get_children())
            self._de_path_lbl.configure(text="No image selected")
            self._de_page_lbl.configure(text="Detected page: —")
            self._de_detect_btn.configure(state=tk.DISABLED)
            self._de_extract_btn.configure(state=tk.DISABLED)
            self._de_log.delete("1.0", tk.END)
            self._de_refresh_output_row()
            self._de_update_row_banner()
        except Exception:
            pass
        self._de_set_status("Cleared.")

    def _de_on_page_detected(self, info):
        self._de_busy = False
        page = info.get("page", "unknown")
        conf = info.get("confidence", 0.0)
        target = info.get("target", "")
        detect_secs = info.get("detect_secs")
        self._de_detected_page = page if page != "unknown" else None
        self._de_page_confidence = conf
        try:
            self._de_page_lbl.configure(text=f"Detected page: {page}  ({conf*100:.1f}%)")
            cfg = self._de_load_config()
            self._de_extract_btn.configure(
                state=tk.NORMAL if page in cfg else tk.DISABLED)
        except Exception:
            pass
        self._de_set_status(f"Detected page: {page} (confidence {conf*100:.1f}%)")
        # If the user is in Auto mode, surface the detected page's fields now so
        # the checklist isn't left showing a stale/empty set.
        try:
            if (self._de_target_var.get() == "Auto"
                    and self._de_detected_page):
                self._de_rebuild_field_checks(self._de_detected_page)
        except Exception:
            pass
        scores = info.get("scores") or {}
        tsec = f" time={detect_secs}s" if detect_secs is not None else ""
        self._de_log_line(
            f"[detect] target={target} candidates={len(scores)} → page={page} "
            f"confidence={conf:.3f}{tsec}")
        if scores:
            top = sorted(scores.items(), key=lambda kv: kv[1]["final"], reverse=True)[:5]
            self._de_log_line("  top candidates: " +
                              ", ".join(f"{nm}={sc['final']:.3f}" for nm, sc in top))

    def _de_on_extract_result(self, result):
        self._de_busy = False
        self._de_last_result = result
        page = result.get("page", "unknown")
        conf = result.get("page_confidence", 0.0)
        try:
            self._de_tv.delete(*self._de_tv.get_children())
        except Exception:
            pass
        note = result.get("note")
        if note:
            # No extractor for this page → leave the combined row exactly as-is.
            self._de_set_status(
                f"{note}  Combined row unchanged "
                f"(still holds previously extracted values).")
            self._de_log_line(f"[extract] {note} — combined row unchanged.")
            self._de_refresh_output_row()
            self._de_update_row_banner()
            return
        fields = result.get("fields", {})
        for fname, fd in fields.items():
            rect = fd.get("rect", [])
            status = fd.get("status", "")
            cands = fd.get("candidates", [])
            # For non-clean reads, surface the competing candidates inline.
            status_txt = status
            if status in ("suspicious", "failed") and cands:
                status_txt = f"{status} ({','.join(str(c) for c in cands)})"
            try:
                self._de_tv.insert("", tk.END, values=(
                    fname, fd.get("value", ""), f'raw="{fd.get("raw","")}"',
                    fd.get("engine", ""), status_txt, str(rect)))
            except Exception:
                pass
        ok = sum(1 for fd in fields.values() if fd.get("status") in ("ok", "fallback"))
        dsec = result.get("detect_secs"); esec = result.get("extract_secs")
        tmsg = ""
        if dsec is not None or esec is not None:
            tmsg = f"  [detect={dsec}s extract={esec}s]"
        self._de_set_status(
            f"Extracted {ok}/{len(fields)} fields from '{page}' "
            f"(page confidence {conf*100:.1f}%).{tmsg}")
        self._de_log_line(
            f"[extract] page={page} ok={ok}/{len(fields)} detect={dsec}s extract={esec}s")
        for fname, fd in fields.items():
            cand = fd.get("candidates", [])
            ctxt = (" candidates=" + ",".join(str(c) for c in cand)) if (
                fd.get("status") in ("suspicious", "failed") and cand) else ""
            self._de_log_line(
                f"    {fname}: {fd.get('value','')!r} time={fd.get('time')}s "
                f"[{fd.get('engine','')}/{fd.get('status','')}] "
                f"raw={fd.get('raw','')!r}{ctxt}")
        if result.get("debug_dir"):
            self._de_log_line(f"[debug] crops saved to {result['debug_dir']}")

        # ── Fold this page's fields into the persistent combined output row ──
        self._de_apply_fields_to_row(page, fields)
        if fields and page not in getattr(self, "_de_filled_pages", []):
            self._de_filled_pages = getattr(self, "_de_filled_pages", []) + [page]
        self._de_refresh_output_row()
        self._de_update_row_banner()

    def _de_apply_fields_to_row(self, page, fields):
        """
        Update only THIS page's mapped output columns in self._de_current_row,
        leaving all other columns at their existing/default value.  Applies the
        million-value conversion for target-app-main top resources.  Never fakes
        values for unimplemented pages (their column mapping simply isn't filled
        unless the extractor produced fields).
        """
        row = self._de_ensure_row()
        if page == "target app main":
            # field name → output column (+ million conversion for resources)
            top_map = {"food": "food_top", "parts": "parts_top",
                       "electric": "electric_top", "gas": "gas_top",
                       "cash": "cash_top"}
            for fname, fd in fields.items():
                val = fd.get("value", "")
                status = fd.get("status", "")
                if fname in ("gold", "power"):
                    if val and status in ("ok", "fallback"):
                        row[fname] = val
                elif fname in top_map:
                    col = top_map[fname]
                    if val and status in ("ok", "fallback"):
                        row[col] = self._de_resource_to_million(val)
                    # suspicious/failed → leave previous/default (blank), don't fake
            return
        # Other pages: fill a mapped column only with a CONFIDENT (ok/fallback)
        # value.  Never overwrite an existing non-zero/non-blank value with a 0 or
        # blank from a later screenshot (combined-row accumulation across the
        # scrolling grid); only Reset Row clears values.
        cols = self.DE_PAGE_COLUMN_MAP.get(page, [])
        for fname, fd in fields.items():
            if fname not in cols:
                continue
            val = fd.get("value", "")
            if not val or fd.get("status") not in ("ok", "fallback"):
                continue
            existing = row.get(fname, "")
            # Don't clobber an existing real value with a fresh '0'.
            if val in ("0", "") and existing not in ("", "0"):
                continue
            row[fname] = val

    def _de_refresh_output_row(self):
        """Update the tab-separated output box with the current combined row."""
        try:
            tsv = self._de_row_tsv(with_headers=False)
            self._de_outrow.configure(state=tk.NORMAL)
            self._de_outrow.delete("1.0", tk.END)
            self._de_outrow.insert("1.0", tsv)
            self._de_outrow.configure(state=tk.DISABLED)
        except Exception:
            pass

    def _de_on_error(self, msg):
        self._de_busy = False
        self._de_set_status("Error — see debug box.")
        self._de_log_line(f"[error] {msg}")

    # ══════════════════════════════════════════════════════════════════════════
    # DEMO INIT
    # ══════════════════════════════════════════════════════════════════════════
    def _demo_init(self):
        self.after(400, lambda: self.q.put(("devices_connected", DEMO_ACTIVE)))


# ==============================================================================
# ENTRY POINT
# ==============================================================================
if __name__ == "__main__":
    multiprocessing.freeze_support()
    default_path = str(Path(__file__).resolve().parent / SCRIPT_BASENAME)
    demo_mode = False
    try:
        if not Path(default_path).exists():
            raise FileNotFoundError
        spec = importlib.util.spec_from_file_location("_chk", default_path)
        if spec is None:
            raise ImportError
    except Exception:
        demo_mode = True

    app = ControllerUI(default_path, demo=demo_mode)
    app.mainloop()