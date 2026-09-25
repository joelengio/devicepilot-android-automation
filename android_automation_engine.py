# ==============================================================================
# TABLE OF CONTENTS
# ==============================================================================
# 1. IMPORTS
# 2. CONFIGURATION & LOGGING
# 3. ADB & BLUESTACKS INTERNALS
#    - Binary Location & Config Parsing
#    - ADB Connection & Device Management
#    - Package Management (Install/Uninstall)
# 4. WINDOWS OS CONTROL
# 5. IMAGING & SCREENSHOTS
# 6. OCR & TEXT DETECTION (Tesseract / EasyOCR)
# 7. INTERACTION PRIMITIVES (Taps, Swipes, Delays)
# 8. GOOGLE SHEETS & TIMING UTILS
# 9. PAGE DETECTION, NAVIGATION & STATE
# 10. WORKFLOW: VPN
# 11. TARGET APPLICATION WORKFLOW
# 12. MAIN EXECUTION & RUNNER
# ==============================================================================

# ------------------------------------------------------------
# 1. IMPORTS
# ------------------------------------------------------------

# ------------------------------------------------------------
# Standard library imports
# ------------------------------------------------------------

import logging   # For logging debug/info/error messages across the script
import threading as _threading
import subprocess  # To run external commands (adb, HD-Player.exe, etc.)
import time        # For sleeps/delays and timestamp handling
import random      # For random delays and jitter in taps/clicks
import os          # Filesystem operations: paths, existence checks, env vars
import re          # Regular expressions (used for parsing text, filenames, etc.)
import shutil      # High-level file operations (copying, moving, removing dirs)
import zipfile     # Handling .zip / .xapk archives during APK/XAPK processing
import tempfile    # Creating temporary working directories/files
import glob        # File pattern matching (e.g., finding APK/XAPK files)
import itertools

import datetime as _dt # Used in Sheets/Time utils
import io # Ensure this is present for the fast screenshot
# ── Google Sheets retry wrapper ──────────────────────────────────────────
import math
import functools as _functools
from difflib import SequenceMatcher
from concurrent.futures import ThreadPoolExecutor, as_completed, TimeoutError as FutureTimeoutError
# ------------------------------------------------------------
# Third-party / external library imports
# ------------------------------------------------------------

import cv2         # OpenCV: image processing, template matching, color masks, etc.
import pytesseract # Tesseract OCR wrapper: reading text from screenshots

import numpy as np # Numerical operations on image arrays (e.g., template matching)

from PIL import Image  # PIL (Pillow): loading, saving, and manipulating images

import gspread     # Google Sheets API client for reading/writing sheet data
from oauth2client.service_account import ServiceAccountCredentials
import socket
# ^ Used to authenticate gspread using a service account JSON
import difflib

import json
from dotenv import load_dotenv
load_dotenv()
# ...your other imports...


# ------------------------------------------------------------
# 2. CONFIGURATION & LOGGING
# ------------------------------------------------------------

# Resolve pages.json next to THIS script, not relative to the process cwd.
# Worker subprocesses do not necessarily inherit the controller's cwd, and a
# relative path there silently loaded an empty config — which is what produced
# the "is_on_page [loading_warning] no spec found" spam during Loading while the
# page was in fact defined.
def _resolve_pages_json() -> str:
    try:
        here = os.path.dirname(os.path.abspath(__file__))
        cand = os.path.join(here, "pages.json")
        if os.path.exists(cand):
            return cand
    except Exception:
        pass
    return "pages.json"


PAGES_JSON = _resolve_pages_json()

# Generic target-application configuration. These defaults are intentionally
# non-production placeholders for emulator testing. Override them in .env.
TARGET_APP_PACKAGE = os.getenv("TARGET_APP_PACKAGE", "com.example.targetapp").strip()
TARGET_APP_ACTIVITY = os.getenv("TARGET_APP_ACTIVITY", ".MainActivity").strip()
TARGET_APP_COMPONENT = f"{TARGET_APP_PACKAGE}/{TARGET_APP_ACTIVITY}"


# Pages the Loading flow cannot function without. Validated once at worker
# startup so a bad/missing config is reported loudly instead of degrading into a
# silent unknown-page loop.
REQUIRED_LOADING_PAGES = (
    "loading",
    "loading after update",
    "loading_warning",
    "loading_warning1",
    "google_signin",
    "connection issue",
    "login reward",
    "monthly reward",
    "target app main",
)


def validate_pages_config(log_fn=None) -> dict:
    """
    Check that every page the Loading flow depends on is present.

    Returns {"path", "loaded", "missing", "ok"}.  Logs one clear ERROR listing
    the resolved path and the missing names — a single loud message rather than
    a per-frame "no spec found" debug line nobody reads.
    """
    def _emit(msg, level="info"):
        getattr(logging, level, logging.info)(msg)
        if log_fn:
            try:
                log_fn(msg, {"error": "err", "warning": "warn"}.get(level, "dim"))
            except Exception:
                pass

    try:
        pages = load_pages_config(PAGES_JSON, force_reload=True)
    except Exception as exc:
        _emit(f"[PAGES] could not load pages.json at {PAGES_JSON}: {exc!r}", "error")
        return {"path": PAGES_JSON, "loaded": 0, "missing": list(REQUIRED_LOADING_PAGES),
                "ok": False}

    missing = [n for n in REQUIRED_LOADING_PAGES if n not in pages]
    result = {"path": PAGES_JSON, "loaded": len(pages), "missing": missing,
              "ok": not missing}

    if missing:
        _emit(f"[PAGES] ERROR — required page spec(s) MISSING from "
              f"{PAGES_JSON}: {missing}", "error")
        _emit(f"[PAGES] loaded {len(pages)} page(s) from {PAGES_JSON}; "
              f"Loading will not be able to detect the missing pages", "error")
    else:
        _emit(f"[PAGES] {len(pages)} page(s) loaded from {PAGES_JSON}; "
              f"all {len(REQUIRED_LOADING_PAGES)} required Loading pages present")
    return result

# ================== CONFIG ==================

DOC_NAME = os.getenv("CONTROL_SHEET_DOC", "android_automation")
# Name of the Google Sheets document.
# - Used whenever we open the sheet through gspread.
# - If you rename the sheet in Google Drive, update this string.

CONTROL_SHEET = "Controllap"
# Name of the worksheet/tab inside DOC_NAME that holds:
# - Device list
# - Checkbox flags (RunDailies, RunEvents, UpdateApps)
# - Control cells (RunAll, StartFrom, InputNames, Last Refresh, etc.)

# ── BlueStacks config location ───────────────────────────────────────────────
# The conf lives in different places depending on how BlueStacks was installed
# (custom data drive vs. the default ProgramData location).  Checked in order,
# first existing path wins, so a custom install takes precedence.
BLUESTACKS_CONF_CANDIDATES = [
    r"E:\BlueStacks_nxt\bluestacks.conf",
    r"C:\ProgramData\BlueStacks_nxt\bluestacks.conf",
]


def resolve_bluestacks_conf_path() -> str:
    """
    Return the first BlueStacks conf path that exists.

    Falls back to the first candidate when none exist, so the constant is always
    a usable string.  Callers must tolerate the file being absent — see
    parse_bluestacks_conf(), which returns [] rather than raising.
    """
    for path in BLUESTACKS_CONF_CANDIDATES:
        try:
            if os.path.exists(path):
                return path
        except Exception:
            continue
    return BLUESTACKS_CONF_CANDIDATES[0]


BLUESTACKS_CONF = resolve_bluestacks_conf_path()


def bluestacks_conf_status() -> dict:
    """
    Describe conf resolution for startup logging and error messages.

    Returns {"candidates": [(path, exists), ...], "selected": str, "found": bool}
    """
    cands = []
    for path in BLUESTACKS_CONF_CANDIDATES:
        try:
            cands.append((path, os.path.exists(path)))
        except Exception:
            cands.append((path, False))
    return {
        "candidates": cands,
        "selected":   BLUESTACKS_CONF,
        "found":      any(exists for _, exists in cands),
    }


def log_bluestacks_conf_status(log_fn=None) -> dict:
    """
    Emit the candidate list, each path's existence, and the selected path.

    `log_fn(msg, tag)` lets the controller route these into its own log; without
    it the lines go to the module logger.
    """
    status = bluestacks_conf_status()

    def _emit(msg, tag="dim"):
        logging.info(msg)
        if log_fn:
            try:
                log_fn(msg, tag)
            except Exception:
                pass

    _emit("Using BlueStacks config candidates:", "dim")
    for path, exists in status["candidates"]:
        _emit(f"  - {path} exists={exists}", "dim" if exists else "warn")

    if status["found"]:
        _emit(f"Selected BlueStacks config: {status['selected']}", "ok")
    else:
        _emit("BlueStacks config not found. Checked:", "err")
        for path, _ in status["candidates"]:
            _emit(f"  {path}", "err")
    return status
# Path to the Bluestacks configuration file.
# - Parsed to discover available instances, their ADB ports, and display names.
# - Also used to help locate HD-Player.exe (Bluestacks binary) if not found in defaults.

APK_FOLDER = os.getenv("APK_FOLDER", r"apk_download")
# Default folder where APK/XAPK files are stored.
# - Functions that auto-install or update apps look here to find install packages.

class FatalAPKError(Exception):
    """
    Raised when the installed TargetApp version is newer than the available version
    in sheets AND the matching APK is not present in APK_FOLDER.
    Caught by device_worker to trigger a stop-all signal to the controller.
    """
    pass

TESSERACT_PATH = r"C:\Program Files\Tesseract-OCR\tesseract.exe"
# Path to the Tesseract OCR executable.
# - Assigned to pytesseract so that OCR calls (reading text from screenshots) work.

CREDS_JSON = os.getenv("GOOGLE_SERVICE_ACCOUNT_JSON", "service-account.json")
# Service account credentials JSON for Google Sheets API (gspread).
# - Must exist in the working directory or be referenced with an absolute path.
# - Used to authenticate and get read/write access to the Control sheet.

# ================== LOGGING / OCR ==================
logging.basicConfig(
    filename='automation_log.log',          # Log file name (created in the current working directory)
    filemode='a',                           # 'a' = append to the file instead of overwriting each run
    format='%(asctime)s - %(levelname)s - %(message)s',  # Timestamp + level + message
    level=logging.DEBUG                     # Capture DEBUG and above (INFO, WARNING, ERROR, CRITICAL)
)
logging.info('Starting automation script...')
# Initial log entry so you can see when a new run starts in automation_log.log

LOGS_DIR              = "logs"            # Per-device log files go here
UNEXPECTED_PAGES_DIR  = "unexpected_pages"  # Screenshots of unexpected pages go here

_DEVICE_LOGGERS:           dict = {}   # cache: sanitized_id -> logging.Logger
_UNEXPECTED_PAGE_COUNTERS: dict = {}   # cache: device       -> int (incrementing counter)
# ── Per-device screenshot locks — prevents guard thread and workflow thread
# ── on the same device from screenshotting simultaneously
_screenshot_locks: dict = {}   # device_id → threading.Lock()
_screenshot_locks_mutex = _threading.Lock()   # protects the dict itself

def _get_screenshot_lock(device: str) -> _threading.Lock:
    with _screenshot_locks_mutex:
        if device not in _screenshot_locks:
            _screenshot_locks[device] = _threading.Lock()
        return _screenshot_locks[device]

# ── Single global sheets lock — one gspread client, one HTTP connection
_sheets_lock = _threading.Lock()

def _get_device_logger(device: str) -> logging.Logger:
    """
    Return a logger that writes ONLY to logs/<sanitized_device>.log.

    - Each device gets its own file so you can review one device at a time.
    - All files live in the LOGS_DIR folder (created automatically).
    - The logger is cached so the file is opened only once per run.
    - This does NOT interfere with the root logger (automation_log.log).
    """
    safe_id = _sanitize_device_id(device)          # e.g. "localhost_5555"

    if safe_id in _DEVICE_LOGGERS:
        return _DEVICE_LOGGERS[safe_id]

    # Create the logs folder if it doesn't exist yet
    os.makedirs(LOGS_DIR, exist_ok=True)

    log_path = os.path.join(LOGS_DIR, f"{safe_id}.log")

    # Use a NAMED logger (not the root logger) so the two never collide
    logger = logging.getLogger(f"device.{safe_id}")
    logger.setLevel(logging.DEBUG)

    # Avoid adding duplicate handlers if this somehow runs twice
    if not logger.handlers:
        fh = logging.FileHandler(log_path, mode="a", encoding="utf-8")
        fh.setLevel(logging.DEBUG)
        fh.setFormatter(logging.Formatter(
            "%(asctime)s  %(levelname)-8s  %(message)s",
            datefmt="%Y-%m-%d %H:%M:%S",
        ))
        logger.addHandler(fh)

    # Stop log records bubbling up to the root logger
    # (keeps device logs out of automation_log.log)
    logger.propagate = False

    _DEVICE_LOGGERS[safe_id] = logger
    return logger


# Point pytesseract at the installed Tesseract binary so OCR works correctly.
# If TESSERACT_PATH is wrong, all OCR-related functions will fail.
pytesseract.pytesseract.tesseract_cmd = TESSERACT_PATH


# ------------------------------------------------------------
# 3. ADB & BLUESTACKS INTERNALS
# ------------------------------------------------------------

# ================== ADB / BlueStacks helpers ==================
BLUESTACKS_BIN_CANDIDATES = [
    r"C:\Program Files\BlueStacks_nxt\HD-Player.exe",
    r"C:\Program Files (x86)\BlueStacks_nxt\HD-Player.exe",
    r"E:\Program Files\BlueStacks_nxt\HD-Player.exe",
    r"E:\BlueStacks_nxt\HD-Player.exe",
]
# Possible locations of the Bluestacks HD-Player.exe.
# - _find_hd_player() will scan this list and use the first one that exists.
# - If Bluestacks is installed in a different path/drive, add it here.


# Cache for the detected HD-Player path so we only search the filesystem once
_HD_PLAYER_CACHE = None


def _find_hd_player():
    """
    Locate the BlueStacks HD-Player executable, with simple in-memory caching.

    Search strategy (first call only):
        1. Check each candidate path listed in BLUESTACKS_BIN_CANDIDATES.
        2. If none of those exist:
             - Look in the directory that contains BLUESTACKS_CONF
               for 'HD-Player.exe'.

    Caching:
        - On the first successful (or unsuccessful) search, the result is
          stored in _HD_PLAYER_CACHE.
        - Subsequent calls return _HD_PLAYER_CACHE directly without hitting
          the filesystem again.

    Returns:
        - Full path to HD-Player.exe (string), if found.
        - None, if no candidate path exists.
    """
    global _HD_PLAYER_CACHE

    # If we've already looked for HD-Player before in this process,
    # return the cached result immediately (even if it's None).
    if _HD_PLAYER_CACHE is not None:
        return _HD_PLAYER_CACHE

    # 1) Try each hard-coded candidate path from BLUESTACKS_BIN_CANDIDATES
    for p in BLUESTACKS_BIN_CANDIDATES:
        if os.path.exists(p):
            _HD_PLAYER_CACHE = p
            return p

    # 2) Fallback: derive HD-Player.exe path from the Bluestacks config location
    base = os.path.dirname(BLUESTACKS_CONF)
    candidate = os.path.join(base, "HD-Player.exe")

    # Cache either the valid path or None (if it doesn't exist)
    _HD_PLAYER_CACHE = candidate if os.path.exists(candidate) else None
    return _HD_PLAYER_CACHE


def _adb_list():
    """
    Run 'adb devices' and return the raw stdout text.

    Example output:
        List of devices attached
        127.0.0.1:5555    device
        127.0.0.1:5557    offline
    """
    res = subprocess.run(["adb", "devices"], capture_output=True, text=True)
    return res.stdout


def _adb_connect_once(adb_id):
    """
    Try a single 'adb connect <adb_id>'.

    Returns:
        True  - if command output says 'connected to' or 'already connected',
                or if the device shows up in 'adb devices'.
        False - otherwise.
    """
    try:
        # Try to connect to the given ADB endpoint (e.g. '127.0.0.1:5555')
        out = subprocess.run(
            ["adb", "connect", adb_id],
            capture_output=True,
            text=True,
        ).stdout
    except Exception:
        # On any error (e.g. adb not found, connection error), treat as empty output
        out = ""

    low = out.lower()
    if "connected to" in low or "already connected" in low:
        # Direct success signal from adb output
        return True

    # If adb didn't explicitly say "connected", fall back to checking the device list
    return (adb_id in _adb_list())


def _adb_wait_for_device(adb_id, timeout=45, interval=3):
    """
    Keep trying to connect to <adb_id> until it is listed as 'device'
    in 'adb devices', or until timeout.

    Args:
        adb_id   : ADB endpoint, e.g. '127.0.0.1:5555'
        timeout  : Max time (in seconds) to wait.
        interval : Delay (in seconds) between attempts.

    Returns:
        True  - device is connected and in 'device' state.
        False - did not reach 'device' state before timeout.
    """
    t0 = time.time()
    while time.time() - t0 < timeout:
        # Try to connect once (quick attempt)
        if _adb_connect_once(adb_id):
            # If connect didn't error, re-check the full adb devices list
            out = _adb_list()
            # Skip the first line ("List of devices attached")
            for line in out.splitlines()[1:]:
                # Example line: "127.0.0.1:5555    device"
                parts = [p for p in line.strip().split("\t") if p]
                # Expect exactly two parts: <adb_id> and <state>
                if len(parts) == 2 and parts[0] == adb_id and parts[1] == "device":
                    return True  # Device is now online and ready

        # Not ready yet: wait a bit and try again
        time.sleep(interval)

    # Timed out waiting for the device to appear as 'device'
    return False


def _port_from_adb_id(adb_id):
    """
    Extract the TCP port from an adb_id like 'localhost:5555'.

    Args:
        adb_id : string or anything castable to string.

    Returns:
        '5555' (string) if adb_id matches 'localhost:<port>',
        None otherwise.
    """
    m = re.match(r"^localhost:(\d+)$", str(adb_id).strip(), re.I)
    return m.group(1) if m else None


# ---------- ADB base helpers ----------
def _adb(device, *args):
    """
    Run an adb command targeted at a specific device.

    Args:
        device: The ADB device ID (e.g. '127.0.0.1:5555').
        *args:  The rest of the adb command arguments, e.g.:
                ("shell", "input", "tap", "100", "200")

    Returns:
        subprocess.CompletedProcess with .stdout and .stderr as text.

    Examples:
        _adb("127.0.0.1:5555", "shell", "echo", "hello")
        _adb("127.0.0.1:5555", "shell", "input", "tap", "100", "200")
    """
    return subprocess.run(
        ["adb", "-s", device, *args],
        capture_output=True,
        text=True,
    )

def _adb_ping(device) -> bool:
    """
    Lightweight ADB connectivity check (similar to _adb_ok, but standalone).

    Runs:
        adb -s <device> shell echo ok

    Returns:
        True  - if return code is 0 and stdout contains 'ok' (case-insensitive).
        False - otherwise.
    """
    r = subprocess.run(
        ["adb", "-s", device, "shell", "echo", "ok"],
        capture_output=True,
        text=True,
    )
    return (r.returncode == 0) and ("ok" in (r.stdout or "").lower())
#toremove 
def _check_internet(device: str) -> bool:
    """
    Ping 8.8.8.8 through the Android device to confirm it has internet.
    Returns True if reachable, False otherwise.
    Only call when you have a specific reason to suspect no connectivity
    (e.g. VPN just connected but the game can't load).
    """
    try:
        result = subprocess.run(
            ["adb", "-s", device, "shell", "ping", "-c", "1", "-W", "2", "8.8.8.8"],
            capture_output=True, text=True, timeout=8
        )
        return result.returncode == 0 and "1 received" in result.stdout
    except Exception:
        return False
#toremove     
def _check_vpn_connected(device: str) -> bool:
    """
    Check if the VPN tunnel (tun0) is active on the device via ADB.
    Returns True if tun0 is UP, False otherwise.
    No screenshot needed — fast ADB shell call.
    """
    try:
        result = subprocess.run(
            ["adb", "-s", device, "shell", "ip", "link", "show", "tun0"],
            capture_output=True, text=True, timeout=5
        )
        return result.returncode == 0 and "tun0" in result.stdout
    except Exception:
        return False


_connection_issue_log: dict = {}   # device -> list of timestamps

def _handle_connection_issue_DEPRECATED(device: str, dlog) -> str:
    """
    DEPRECATED — all logic moved to _handle_connection_issue_v2().
    This stub forwards the call so accidental invocations still work but use
    the correct no-force-stop recovery path.  The old setup_vpn() / 5-in-30s
    logic is intentionally removed.
    """
    dlog.warning(
        "── _handle_connection_issue_DEPRECATED called — "
        "forwarding to _handle_connection_issue_v2()"
    )
    result = _handle_connection_issue_v2(
        device, dlog,
        in_loading=_loading_phase_active.get(device, False),
    )
    # v2 returns a dict; convert to legacy string for any stale callers
    if isinstance(result, dict):
        return result.get("status", "failed")
    return result

def close_all_apps(device: str) -> None:
    """
    Kill all killable background apps on the device (am kill-all).
    Gives the device a clean slate before launching a fresh app.
    Does NOT kill the foreground app.
    """
    dlog = _get_device_logger(device)
    dlog.info("── Closing background apps (am kill-all) ──")
    try:
        subprocess.run(
            ["adb", "-s", device, "shell", "am", "kill-all"],
            capture_output=True, timeout=5
        )
        time.sleep(0.5)
        dlog.info("── Background apps cleared ──")
    except Exception as e:
        dlog.warning(f"close_all_apps: {type(e).__name__}: {e}")

def _adb_shell(device: str, *args, timeout: int = 10) -> str:
    """
    Run an adb shell command on the given device and return stdout as a string.
    Returns an empty string on any error.
    """
    try:
        result = subprocess.run(
            ["adb", "-s", device, "shell", *args],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return result.stdout or ""
    except Exception:
        return ""


# ------------------------------------------------------------------------------
# 2. find_vpn
# ------------------------------------------------------------------------------

def find_vpn(device: str) -> bool:
    """
    Returns True if ProtonVPN (ch.protonvpn.android) is installed on the device.
    """
    dlog = _get_device_logger(device)
    dlog.debug("── find_vpn ── running pm path ch.protonvpn.android")
    out = _adb_shell(device, "pm", "path", "ch.protonvpn.android")
    result = "package:" in out
    dlog.info(
        f"── find_vpn ── {'FOUND ✓' if result else 'NOT FOUND'} "
        f"(pm output: {out.strip()[:80]!r})"
    )
    return result



# ------------------------------------------------------------------------------
# 3. find_target_app
# ------------------------------------------------------------------------------

def find_target_app(device: str) -> bool:
    """
    Returns True if Target Application (com.targetvendor.targetapp) is installed.
    """
    dlog = _get_device_logger(device)
    out = _adb_shell(device, "pm", "path", TARGET_APP_PACKAGE)
    found = "package:" in out
    dlog.debug(f"── find_target_app ── pm path output: {out.strip()!r} → {'installed' if found else 'NOT installed'}")
    return found


# ------------------------------------------------------------------------------
# 4. open_vpn
# ------------------------------------------------------------------------------


# ------------------------------------------------------------------------------
# 5. open_target_app
# ------------------------------------------------------------------------------

def open_target_app(device: str, context: str = "") -> bool:
    """
    Launches Target Application via am start. Returns True on success.

    Includes a debounce guard: if open_target_app was called within the last
    _TARGET_APP_OPEN_DEBOUNCE_SECS seconds, the duplicate call is skipped and
    True is returned so callers don't treat it as a failure.  This prevents
    TargetAppGuard / recovery code from hammering open_target_app while the first launch
    is still in its transition period.
    """
    dlog = _get_device_logger(device)
    _now = time.time()
    _until = _target_app_open_in_progress_until.get(device, 0)
    if _now < _until:
        dlog.info(
            f"[TARGET_APP-OPEN] launch already in progress — "
            f"skipping duplicate open_target_app "
            f"({_until - _now:.1f}s remaining)"
            + (f" context={context!r}" if context else "")
        )
        return True   # pretend success — TargetApp is still launching

    ctx_tag = f" context={context!r}" if context else ""
    dlog.info(f"[TARGET_APP-OPEN] launch requested{ctx_tag}")
    _target_app_open_in_progress_until[device] = _now + _TARGET_APP_OPEN_DEBOUNCE_SECS
    dlog.info("── open_target_app ── Launching TargetApp via am start")
    try:
        result = subprocess.run(
            ["adb", "-s", device, "shell", "am", "start",
             "-n", TARGET_APP_COMPONENT],
            capture_output=True,
            text=True,
            timeout=10,
        )
        out = (result.stdout or "") + (result.stderr or "")
        success = "Starting: Intent" in out or "brought to the front" in out
        dlog.info(f"── open_target_app ── am start result: {'success' if success else 'FAILED'} | output: {out.strip()!r}")
        if success:
            _loading_phase_active[device] = True
            _last_seen_page[device] = "loading"
            dlog.info("[TARGET_APP-OPEN] TargetApp launch command accepted ✓")
        else:
            # Clear debounce on failure so the next recovery attempt is not blocked
            _target_app_open_in_progress_until.pop(device, None)
        return success
    except Exception as e:
        dlog.error(f"── open_target_app ── Exception: {e}")
        _target_app_open_in_progress_until.pop(device, None)
        return False


# ------------------------------------------------------------------------------
# 7. internet
# ------------------------------------------------------------------------------

def internet(device: str) -> bool:
    """
    Returns True if the device has working internet connectivity.
    Pings 8.8.8.8 once with a 2 second timeout.
    """
    dlog = _get_device_logger(device)
    dlog.debug("── internet ── pinging 8.8.8.8")
    t0 = time.time()
    out = _adb_shell(device, "ping", "-c", "1", "-W", "2", "8.8.8.8", timeout=8)
    elapsed = time.time() - t0
    result = "1 received" in out and "0% packet loss" in out
    if result:
        dlog.info(f"── internet ── OK ({elapsed:.2f}s)")
    else:
        dlog.warning(
            f"── internet ── FAILED ({elapsed:.2f}s) | "
            f"output: {out.strip()[:120]!r}"
        )
    return result



# ------------------------------------------------------------------------------
# 8. device_online
# ------------------------------------------------------------------------------

def device_online(device: str) -> bool:
    """
    Returns True if the ADB daemon on the device is alive and responding.

    Runs a simple echo command and checks the response.

    Confirmed output: ok

    Note: this only confirms the ADB layer is alive.
    It does NOT detect frozen UI or unresponsive taps.
    """
    out = _adb_shell(device, "echo", "ok", timeout=5)
    return "ok" in out.lower()


def _device_exists_in_adb(device: str) -> bool:
    """
    Check if the device appears in `adb devices` output in a usable state.

    Returns True  — device is listed as 'device' or 'unauthorized'
    Returns False — device is absent OR listed as 'offline'

    When BlueStacks closes it stays listed as 'offline' in adb devices.
    We treat 'offline' the same as absent so the reconnect+verify path fires.
    Unauthorized is kept as True since that is a live device needing trust.
    """
    try:
        r = subprocess.run(
            ["adb", "devices"],
            capture_output=True, text=True, timeout=5,
        )
        port = device.split(":")[-1] if ":" in device else device
        for line in r.stdout.splitlines():
            line = line.strip()
            if not line or line.startswith("List"):
                continue
            if device not in line and port not in line:
                continue
            # Device found — check its state
            parts = line.split()
            state = parts[-1].lower() if len(parts) >= 2 else ""
            if state == "offline":
                # Listed as offline — treat as absent so verify path fires
                return False
            return True  # 'device', 'unauthorized', or any other live state
        return False
    except Exception:
        return False

def _adb_connect_quiet(adb_id: str) -> None:
    """
    Fire a silent 'adb connect <adb_id>' — ignores all output and errors.
    Used only as a reconnect nudge before a get-state verification.
    """
    try:
        subprocess.run(
            ["adb", "connect", adb_id],
            capture_output=True, text=True, timeout=5,
        )
    except Exception:
        pass


def _adb_get_state(device: str) -> str:
    """
    Run 'adb -s <device> get-state' and return the trimmed result.
    Returns 'device', 'offline', 'unauthorized', or '' on any error.

    Note: when device is offline adb writes "error: device offline"
    to stderr and stdout is empty — we check both.
    """
    try:
        r = subprocess.run(
            ["adb", "-s", device, "get-state"],
            capture_output=True, text=True, timeout=5,
        )
        out = (r.stdout or "").strip().lower()
        err = (r.stderr or "").strip().lower()
        if out:
            return out
        if "offline" in err:
            return "offline"
        if "unauthorized" in err:
            return "unauthorized"
        return ""
    except Exception:
        return ""

def _adb_verify_offline(device: str, dlog, guard_name: str, stage: int) -> bool:
    """
    Called when _device_exists_in_adb() first returns False.

    Flow:
        1. Fire _adb_connect_quiet — nudges the ADB server to re-register
           the device if the drop was transient.
        2. Call 'adb -s <device> get-state'.
        3. If get-state returns 'device' → transient drop, return False.
        4. Anything else (offline / empty / error) → truly offline, return True.

    Returns:
        True  — device is confirmed offline; caller should signal ("offline", stage).
        False — transient ADB blip; caller should continue the guard loop normally.
    """
    dlog.warning(
        f"── {guard_name} ── [stage {stage}] "
        f"Not found in 'adb devices' — attempting reconnect before confirming offline"
    )

    _adb_connect_quiet(device)

    state = _adb_get_state(device)
    dlog.info(
        f"── {guard_name} ── [stage {stage}] "
        f"post-reconnect get-state: '{state or '(empty)'}'"
    )

    if state == "device":
        dlog.info(
            f"── {guard_name} ── [stage {stage}] "
            f"get-state=device — transient ADB drop, continuing"
        )
        return False

    dlog.error(
        f"── {guard_name} ── [stage {stage}] "
        f"get-state='{state or '(empty)'}' — device confirmed offline"
    )
    return True


def is_emulator_process_alive(device_string: str) -> bool:
    """
    Check if the BlueStacks window is still open by asking Windows whether
    the ADB TCP port is still in LISTENING state via netstat.

    Bypasses ADB entirely — accurate even when the ADB connection is severed
    by a VPN routing-table shift.

    Returns True  — port is LISTENING → emulator window is open.
    Returns False — port absent → window closed or crashed.
    Returns True on any error (fail-open: avoid false crash detection).
    """
    try:
        port = device_string.split(":")[-1]
        result = subprocess.run(
            f'netstat -ano -p tcp | findstr ":{port}"',
            shell=True, capture_output=True, text=True, timeout=5,
        )
        alive = "LISTENING" in result.stdout
        _get_device_logger(device_string).debug(
            f"── is_emulator_process_alive ── port={port} "
            f"LISTENING={'yes' if alive else 'no'}"
        )
        return alive
    except Exception as e:
        _get_device_logger(device_string).warning(
            f"── is_emulator_process_alive ── netstat check failed: {e} — assuming alive"
        )
        return True  # fail-open: don't declare dead on a check error


def _guard_verify_offline(
    device: str,
    dlog,
    guard_name: str,
    stage: int,
) -> bool:
    """
    Shared second-opinion check used by VpnGuard and TargetAppGuard when ADB
    reports the device as offline or absent.

    Rules:
      • If netstat says the emulator is already closed → confirmed offline.
      • If the emulator is alive, ADB has just dropped (often due to VPN
        tunnel transition). We KEEP reconnecting until either:
            – ADB comes back              → return False (transient).
            – netstat says window closed  → return True  (Scenario D).
        No fixed timeout — VPN handshakes can take longer than 30s and
        failing on a short timeout produced false device-closed reports.

    Returns:
        False — ADB recovered; caller should continue normal monitoring.
        True  — device confirmed dead; caller should signal ("offline", stage).
    """
    dlog.warning(
        f"── {guard_name} ── [stage {stage}] ADB connection lost — "
        f"verifying via netstat before declaring offline..."
    )

    if not is_emulator_process_alive(device):
        dlog.error(
            f"── {guard_name} ── [stage {stage}] "
            f"netstat: port not LISTENING — emulator confirmed dead immediately"
        )
        return True

    dlog.info(
        f"[ADB-WAIT] ── {guard_name} ── [stage {stage}] "
        f"ADB lost but emulator alive by netstat — waiting"
    )
    print(f"[ADB-WAIT][{device}] ADB lost but emulator alive — waiting")

    start_wait = time.time()
    attempt    = 0
    last_log   = start_wait

    while True:
        if _stop_requested():
            elapsed = time.time() - start_wait
            dlog.info(
                f"[ADB-WAIT] ── {guard_name} ── [stage {stage}] "
                f"stop requested while waiting for ADB — exiting as stopped "
                f"(NOT device-closed; elapsed={elapsed:.1f}s)"
            )
            print(f"[ADB-WAIT][{device}] stop requested while waiting for ADB — exiting as stopped")
            return True   # treat as offline so caller exits cleanly; log above marks it stop-requested

        if not is_emulator_process_alive(device):
            elapsed = time.time() - start_wait
            dlog.error(
                f"[ADB-WAIT] ── {guard_name} ── [stage {stage}] "
                f"emulator closed during ADB wait — Scenario D "
                f"(elapsed={elapsed:.1f}s)"
            )
            print(f"[ADB-WAIT][{device}] emulator closed during ADB wait — Scenario D")
            return True

        try:
            subprocess.run(
                ["adb", "connect", device],
                capture_output=True, timeout=2,
            )
        except Exception:
            pass

        state = _adb_get_state(device)
        attempt += 1
        if state == "device":
            elapsed = time.time() - start_wait
            dlog.info(
                f"[ADB-WAIT] ── {guard_name} ── [stage {stage}] "
                f"ADB restored after {elapsed:.1f}s "
                f"({attempt} attempt(s)) — resuming monitoring ✓"
            )
            print(f"[ADB-WAIT][{device}] ADB restored after {elapsed:.1f}s")
            return False

        now = time.time()
        if now - last_log >= 10.0:
            dlog.info(
                f"[ADB-WAIT] ── {guard_name} ── [stage {stage}] "
                f"still waiting for ADB, emulator alive, "
                f"elapsed={now - start_wait:.0f}s "
                f"(attempt={attempt}, get-state={state!r})"
            )
            last_log = now

        time.sleep(0.5)

# ------------------------------------------------------------------------------
# 9. refresh_device
# ------------------------------------------------------------------------------

def refresh_device(device: str) -> bool:
    """
    Force-stops both ProtonVPN and Target Application to give a clean slate.

    Both commands are silent on success (no output = worked).
    Returns True if both commands completed without error.
    """
    dlog = _get_device_logger(device)
    dlog.info("── refresh_device ── Force-stopping VPN + TargetApp")
    try:
        subprocess.run(
            ["adb", "-s", device, "shell", "am", "force-stop", "ch.protonvpn.android"],
            capture_output=True, timeout=5,
        )
        dlog.debug("── refresh_device ── VPN force-stopped")
        subprocess.run(
            ["adb", "-s", device, "shell", "am", "force-stop", TARGET_APP_PACKAGE],
            capture_output=True, timeout=5,
        )
        dlog.debug("── refresh_device ── TargetApp force-stopped")
        dlog.info("── refresh_device ── Both apps stopped ✓")
        return True
    except Exception as e:
        dlog.error(f"── refresh_device ── Exception: {e}")
        return False


# ------------------------------------------------------------------------------
# 10. check_display
# ------------------------------------------------------------------------------

def check_display(device: str, dlog=None, return_details: bool = False):
    """
    Verify the device is running at the resolution and DPI the bot is calibrated for.

    The LIVE DEVICE is the source of truth here, not the BlueStacks config file.
    The config describes what the instance was configured to do; `wm size` and
    `wm density` describe what Android is actually rendering right now, and those
    two disagree often enough (mid-resize, a profile that did not apply, a
    manually overridden density) that trusting the config would let a device
    start a run with every coordinate silently offset.

    Expected: 1920x1080 @ 240dpi.

    `wm size` / `wm density` report an "Override" line when something has changed
    the value at runtime; when present, the override is what is actually in
    effect, so it wins over the Physical line.

    Returns bool by default, or the full detail dict when return_details=True:

        {
          "size_out", "density_out",          raw adb output, verbatim
          "width", "height", "density",       parsed ints, or None
          "size_str",                         e.g. "1920x1080" or "unreadable"
          "size_ok", "density_ok",
          "readable",                         True only if all three parsed
          "ok",                               readable AND both match
          "reason",                           human-readable pass/fail reason
        }
    """
    if dlog is None:
        dlog = _get_device_logger(device)

    details = {
        "size_out": "", "density_out": "",
        "width": None, "height": None, "density": None,
        "size_str": "unreadable", "density_str": "unreadable",
        "size_ok": False, "density_ok": False,
        "readable": False, "ok": False, "reason": "",
    }

    try:
        details["size_out"] = (_adb_shell(device, "wm", "size") or "").strip()
    except Exception as exc:
        details["reason"] = f"wm size raised: {exc!r}"
        dlog.error(f"[DISPLAY] {device} | wm size raised: {exc!r}")
        return details if return_details else False

    try:
        details["density_out"] = (_adb_shell(device, "wm", "density") or "").strip()
    except Exception as exc:
        details["reason"] = f"wm density raised: {exc!r}"
        dlog.error(f"[DISPLAY] {device} | wm density raised: {exc!r}")
        return details if return_details else False

    # ── Parse size: prefer "Override size:" over "Physical size:" ─────────────
    size_matches = re.findall(r"(Physical|Override)\s+size:\s*(\d+)\s*x\s*(\d+)",
                              details["size_out"], re.I)
    if size_matches:
        chosen = None
        for kind, w, h in size_matches:
            if kind.lower() == "override":
                chosen = (w, h)
                break
        if chosen is None:
            chosen = (size_matches[0][1], size_matches[0][2])
        details["width"], details["height"] = int(chosen[0]), int(chosen[1])
        details["size_str"] = f"{details['width']}x{details['height']}"

    # ── Parse density: same override-wins rule ────────────────────────────────
    den_matches = re.findall(r"(Physical|Override)\s+density:\s*(\d+)",
                             details["density_out"], re.I)
    if den_matches:
        chosen_d = None
        for kind, d in den_matches:
            if kind.lower() == "override":
                chosen_d = d
                break
        if chosen_d is None:
            chosen_d = den_matches[0][1]
        details["density"] = int(chosen_d)
        details["density_str"] = str(details["density"])

    details["readable"] = all(v is not None for v in
                              (details["width"], details["height"], details["density"]))
    details["size_ok"]    = (details["width"], details["height"]) == (EXPECTED_WIDTH, EXPECTED_HEIGHT)
    details["density_ok"] = details["density"] == EXPECTED_DENSITY
    details["ok"]         = details["readable"] and details["size_ok"] and details["density_ok"]

    if not details["readable"]:
        details["reason"] = "could not parse wm size and/or wm density output"
    elif details["ok"]:
        details["reason"] = (f"matches expected {EXPECTED_WIDTH}x{EXPECTED_HEIGHT} "
                             f"@ {EXPECTED_DENSITY}dpi")
    else:
        bits = []
        if not details["size_ok"]:
            bits.append(f"size {details['size_str']} != {EXPECTED_WIDTH}x{EXPECTED_HEIGHT}")
        if not details["density_ok"]:
            bits.append(f"density {details['density_str']} != {EXPECTED_DENSITY}")
        details["reason"] = "; ".join(bits)

    dlog.info(
        f"[DISPLAY] {device} | wm size raw={details['size_out']!r} | "
        f"wm density raw={details['density_out']!r} | "
        f"parsed={details['size_str']} @ {details['density_str']}dpi | "
        f"expected={EXPECTED_WIDTH}x{EXPECTED_HEIGHT} @ {EXPECTED_DENSITY}dpi | "
        f"{'PASS' if details['ok'] else 'FAIL'} — {details['reason']}"
    )

    return details if return_details else details["ok"]


def _preflight_display_from_config(device: str, dlog) -> None:
    """
    Optional extra logging only — never a pass/fail input.

    Reads the BlueStacks conf for this instance and logs whatever resolution and
    DPI keys it can confidently identify.  This is purely a breadcrumb for
    debugging a device that fails the live check: it tells you whether the
    instance was configured wrong or drifted at runtime.

    Deliberately never returns a verdict and never raises.  A device is failed
    only on the live `wm size` / `wm density` result.

    parse_bluestacks_conf() returns a LIST of instance dicts:

        [{"instance": "Nougat32", "name": "TARGET_APP1", "port": "5555"}, ...]

    so the device's ADB port is resolved to an instance id first, then that
    instance's display keys are read straight out of the conf text.  Anchoring
    the key lookup to a specific instance id is what makes the hint trustworthy
    — an unanchored scan would happily report another instance's resolution.
    """
    port = str(device).split(":")[-1]

    # ── Resolve this device's ADB port to a BlueStacks instance id ────────────
    try:
        devices = parse_bluestacks_conf()
    except Exception as exc:
        dlog.debug(f"[DISPLAY-PREFLIGHT] {device} | conf unreadable: {exc!r}")
        return

    if not isinstance(devices, list) or not devices:
        dlog.debug(f"[DISPLAY-PREFLIGHT] {device} | conf returned no instances")
        return

    match = None
    for entry in devices:
        try:
            if str(entry.get("port", "")).strip() == port:
                match = entry
                break
        except Exception:
            continue

    if match is None:
        dlog.debug(
            f"[DISPLAY-PREFLIGHT] {device} | no conf instance with adb port {port} "
            f"(known ports: "
            f"{[e.get('port') for e in devices if isinstance(e, dict)]}) — "
            f"skipping config hints"
        )
        return

    inst = str(match.get("instance", "")).strip()
    name = str(match.get("name", "")).strip()
    if not inst:
        dlog.debug(f"[DISPLAY-PREFLIGHT] {device} | matched entry has no instance id")
        return

    # ── Read that instance's display-related keys from the raw conf ───────────
    try:
        with open(BLUESTACKS_CONF, "r", encoding="utf-8", errors="ignore") as f:
            text = f.read()
    except Exception as exc:
        dlog.debug(f"[DISPLAY-PREFLIGHT] {device} | conf file unreadable: {exc!r}")
        return

    try:
        pat = re.compile(
            r'bst\.instance\.' + re.escape(inst) +
            r'\.([A-Za-z0-9_.]*(?:width|height|dpi|density|resolution)[A-Za-z0-9_.]*)'
            r'="([^"]*)"',
            re.I,
        )
        hits = {k: v for k, v in pat.findall(text)}
    except Exception as exc:
        dlog.debug(f"[DISPLAY-PREFLIGHT] {device} | key scan failed: {exc!r}")
        return

    if not hits:
        dlog.debug(
            f"[DISPLAY-PREFLIGHT] {device} | instance {inst!r} ({name!r}) has no "
            f"width/height/dpi keys in conf — skipping config hints"
        )
        return

    # Compare against expectations purely as a breadcrumb.  Disagreement here is
    # a hint about WHERE a live-check failure came from (configured wrong vs.
    # drifted at runtime), never a reason to fail the device.
    note = ""
    try:
        def _pick(*tags):
            for key, val in hits.items():
                kl = key.lower()
                if any(tg in kl for tg in tags):
                    return val
            return None

        cfg_w   = _pick("fb_width", "width")
        cfg_h   = _pick("fb_height", "height")
        cfg_dpi = _pick("dpi", "density")
        if cfg_w and cfg_h and cfg_dpi:
            agrees = (str(cfg_w) == str(EXPECTED_WIDTH)
                      and str(cfg_h) == str(EXPECTED_HEIGHT)
                      and str(cfg_dpi) == str(EXPECTED_DENSITY))
            note = (f" | config says {cfg_w}x{cfg_h} @ {cfg_dpi}dpi — "
                    f"{'agrees with' if agrees else 'DISAGREES with'} expected "
                    f"{EXPECTED_WIDTH}x{EXPECTED_HEIGHT} @ {EXPECTED_DENSITY}dpi")
    except Exception:
        note = ""

    dlog.info(
        f"[DISPLAY-PREFLIGHT] {device} | instance={inst!r} name={name!r} "
        f"config hints (informational only, never used for pass/fail): "
        f"{hits}{note}"
    )


def go_home(device: str) -> None:
    """
    Send the Android Home keyevent to return to the launcher.
    Silent on failure — caller continues regardless.
    """
    dlog = _get_device_logger(device)
    try:
        subprocess.run(
            ["adb", "-s", device, "shell", "input", "keyevent", "3"],
            capture_output=True, timeout=3
        )
        time.sleep(1)
        dlog.debug("── go_home ── Home keyevent sent")
    except Exception as e:
        dlog.warning(f"── go_home ── keyevent failed: {e}")



def _wait_for_activity(
    device: str,
    *activity_fragments: str,
    timeout: float = 30.0,
    interval: float = 1.0,
    dlog=None,
) -> str | None:
    """
    Poll mCurrentFocus until one of the given fragments appears, or timeout.

    Args:
        activity_fragments: Substrings to look for in the activity string, e.g.:
                            "RoutingActivity", "AddAccountActivity"
        timeout           : Max seconds to wait.
        interval          : Seconds between polls.

    Returns:
        The matching fragment string, or None on timeout.
    """
    t0 = time.time()
    while time.time() - t0 < timeout:
        current = _get_current_activity(device)
        for frag in activity_fragments:
            if frag in current:
                if dlog:
                    dlog.debug(f"_wait_for_activity: matched '{frag}' in '{current}'")
                return frag
        time.sleep(interval)
    return None

# =============================================================================
# 2. NEW HELPER: _check_device_offline
#    Place just above setup_vpn (around line 2985).
#    Used whenever a screenshot or when_on_page returns None — pings ONCE to
#    confirm offline, then triggers reopen if confirmed. No periodic pinging.
# =============================================================================

def _check_device_offline(device: str, stage_label: str, restart_fn, dlog):
    """
    Ping the device once. If offline, call reopen_device and return
    (True, reopen_result). If online, return (False, None).

    Usage pattern:
        offline, result = _check_device_offline(device, "── STAGE 4 ──", setup_vpn, dlog)
        if offline:
            return result

    Only call this when you already have evidence something went wrong
    (screenshot is None, when_on_page returned None). Not a polling tool.
    """
    if not _adb_ping(device):
        dlog.warning(f"{stage_label} ADB ping failed — device offline. Triggering reopen.")
        return True, reopen_device(device, restart_fn)
    dlog.debug(f"{stage_label} ADB ping OK — device is online.")
    return False, None


def run_adb_command(command):
    """
    Run a shell command (usually an adb command) and return stdout as text.

    Args:
        command: Full command string, e.g. "adb -s 127.0.0.1:5555 shell screencap -p /sdcard/screen.png"

    Returns:
        The command's stdout (string). Stderr is discarded here.
    """
    result = subprocess.run(command, shell=True, capture_output=True, text=True)
    return result.stdout


def adb_input_text(device, text):
    """
    Type text into the device using 'adb shell input text'.

    Notes:
        - Spaces are replaced with '%s'.
        - '!' is replaced with '%21'.
        These are common escapes needed for adb's 'input text' syntax.

    Args:
        device: ADB device id.
        text  : String to type.
    """
    escaped_text = text.replace(' ', '%s').replace('!', '%21')
    command = f"adb -s {device} shell input text '{escaped_text}'"
    subprocess.run(command, shell=True)


# ---------- Package listing & parsing ----------
def _list_packages_full(device) -> str:
    """
    List all installed packages for a given device, including their APK paths.

    This calls one of:
        adb -s <device> shell pm list packages -f
        adb -s <device> shell cmd package list packages -f  (fallback)

    Typical output line:
        package:/data/app/..../base.apk=com.targetvendor.targetapp

    Args:
        device: ADB device id (e.g. "127.0.0.1:5555").

    Returns:
        A single string with the full stdout from adb.
        Returns an empty string "" if listing fails.
    """
    # First try the classic 'pm list packages -f'
    r = _adb(device, "shell", "pm", "list", "packages", "-f")
    if r.returncode != 0 or not r.stdout.strip():
        # If that fails or returns nothing, fall back to
        # 'cmd package list packages -f' (newer Androids sometimes prefer this).
        r = _adb(device, "shell", "cmd", "package", "list", "packages", "-f")

    if r.returncode != 0:
        # Both attempts failed → print diagnostic info and return empty string
        print(f"[{device}] Failed to list packages.\nstderr:\n{(r.stderr or '').strip()}")
        return ""

    return r.stdout


def _package_exists(device, pkg: str) -> bool:
    """
    Check whether a given package is installed on the device.

    Implementation detail:
        adb -s <device> shell pm path <pkg>

    If 'pm path' can resolve a code path, the package exists.

    Args:
        device: ADB device id.
        pkg   : Package name (e.g. TARGET_APP_PACKAGE).

    Returns:
        True  - if the package exists.
        False - otherwise.
    """
    r = _adb(device, "shell", "pm", "path", pkg)
    return (r.returncode == 0) and ("package:" in (r.stdout or ""))


# ---------- App-specific guessers ----------
def _guess_target_package(device) -> str | None:
    """
    Try to detect the Target Application package name on a device.

    Strategy:
        1. Look for the known Target Application id:
           TARGET_APP_PACKAGE
        2. If not found, scan the package list for heuristics:
           "targetvendor", "targetapp", "targetapp", etc.

    Args:
        device: ADB device id.

    Returns:
        The detected Target Application package name (string) on success,
        or None if nothing matches.
    """
    # Common / expected Target Application package name
    known = TARGET_APP_PACKAGE
    out = _list_packages_full(device)
    if not out:
        # Could not list packages at all
        return None

    # Fast path: exact string match for the known id anywhere in the output
    if known in out:
        return known

    # Fallback: heuristic scan for "Target Application"-like packages
    hints = tuple(h.strip().lower() for h in os.getenv("TARGET_APP_PACKAGE_HINTS", TARGET_APP_PACKAGE.split(".")[-1]).split(",") if h.strip())
    for line in out.splitlines():
        if not line.startswith("package:"):
            # Ignore any unexpected lines
            continue
        try:
            # Expected format:
            #   package:/path/to/base.apk=com.pkg.name
            _, right = line.split("package:", 1)     # remove the "package:" prefix
            _apk_path, pkg = right.split("=", 1)     # split path vs. package name
            if any(h in line.lower() for h in hints):
                # If any of the hints appears in the line, we treat this as App
                return pkg.strip()
        except ValueError:
            # If the line does not split as expected, just ignore it and continue
            continue

    # Nothing matched our known id or heuristics
    return None


def _guess_proton_package(device) -> str | None:
    """
    Try to find the Proton VPN package name on the device.

    - First, check known official ids.
    - Then, look for packages whose name clearly contains 'protonvpn'.
    - Avoid generic/system VPN packages like com.android.vpndialogs.
    """
    # Known Proton VPN package IDs
    knowns = (
        "ch.protonvpn.android",
        "protonvpn.android",
    )

    out = _list_packages_full(device)
    if not out:
        return None

    # 1) Exact-known ids
    for k in knowns:
        if k in out:
            return k

    # 2) Fallback: anything whose pkg name contains 'protonvpn'
    for line in out.splitlines():
        if not line.startswith("package:"):
            continue
        try:
            _, right = line.split("package:", 1)
            _apk_path, pkg = right.split("=", 1)
            pkg = pkg.strip()
            low = pkg.lower()

            # Skip obvious system / generic VPN bits
            if pkg == "com.android.vpndialogs":
                continue

            # Only accept if it clearly looks like Proton VPN
            if "protonvpn" in low or "ch.protonvpn" in low:
                return pkg
        except ValueError:
            continue

    return None

# ---------- Uninstallers ----------
def uninstall_package(device, pkg: str) -> bool:
    """
    Uninstall a package from the given device, trying up to three methods.

    Strategy:
        1) Host-side uninstall:   adb -s <device> uninstall <pkg>
        2) In-shell uninstall:    adb -s <device> shell pm uninstall <pkg>
        3) Multi-user uninstall:  adb -s <device> shell pm uninstall --user 0 <pkg>

    Returns:
        True  - if any of the three attempts report "Success".
        False - if no attempt succeeds, or if pre-checks fail.
    """
    if not pkg:
        print(f"[{device}] No package provided to uninstall.")
        return False

    if not _adb_ping(device):               # FIX: was _adb_ok (duplicate of _adb_ping)
        print(f"[{device}] ADB communication failed. Is the device connected?")
        return False

    if not _package_exists(device, pkg):
        print(f"[{device}] Package not installed: {pkg}")
        return False

    print(f"[{device}] Uninstalling {pkg} …")

    r1 = _adb(device, "uninstall", pkg)
    out1 = (r1.stdout or "") + (r1.stderr or "")
    print(out1.strip())
    if "Success" in out1:
        return True

    r2 = _adb(device, "shell", "pm", "uninstall", pkg)
    out2 = (r2.stdout or "") + (r2.stderr or "")
    print(out2.strip())
    if "Success" in out2:
        return True

    r3 = _adb(device, "shell", "pm", "uninstall", "--user", "0", pkg)
    out3 = (r3.stdout or "") + (r3.stderr or "")
    print(out3.strip())
    return ("Success" in out3)

def uninstall_ark(device) -> bool:
    """
    Find Target Application's package on the device, then uninstall it.

    Detection:
        - First tries _guess_target_package(device) for a robust guess.
        - If that returns None, falls back to the known id:
          TARGET_APP_PACKAGE
    """
    pkg = _guess_target_package(device) or TARGET_APP_PACKAGE
    # FIX: removed dead `if not pkg:` block — the `or` fallback makes pkg always truthy.
    return uninstall_package(device, pkg)

def uninstall_proton(device) -> bool:
    """
    Find the Proton VPN package on the device, then uninstall it.

    Detection:
        - Uses _guess_proton_package(device) to identify the right package id.
    """
    pkg = _guess_proton_package(device)
    if not pkg:
        print(f"[{device}] Could not find Proton VPN package from hints.")
        return False

    # Reuse the same generic uninstall logic
    return uninstall_package(device, pkg)

def install_vpn(device: str) -> bool:
    """
    Install Proton VPN on the given device, if it isn't already installed.

    Uses:
      - _guess_proton_package(device) to see if it's present
      - _find_package_path(...) + _install_any_package(...) to install from APK_FOLDER

    Returns:
        True on successful install/already-installed, False on failure.
    """
    print(f"[{device}] install_vpn() – starting")

    # 1) Is Proton VPN already installed with a *real* proton package id?
    pkg = _guess_proton_package(device)
    if pkg:
        print(f"[{device}] Proton VPN already installed as {pkg}.")
        return True

    # 2) Find a Proton VPN APK/XAPK in your downloads folder
    vpn_apk = _find_package_path(
        APK_FOLDER,
        patterns=(
            r"proton.*vpn.*\.xapk$",
            r"proton.*vpn.*\.apk$",
            r"vpn.*proton.*\.xapk$",
            r"vpn.*proton.*\.apk$",
        ),
    )
    if not vpn_apk:
        print(f"[{device}] No Proton VPN installer found in: {APK_FOLDER}")
        return False

    print(f"[{device}] Installing Proton VPN from {os.path.basename(vpn_apk)} ...")
    ok = _install_any_package(device, vpn_apk)
    if not ok:
        print(f"[{device}] Proton VPN installation failed.")
        return False

    print(f"[{device}] Proton VPN installed successfully.")
    return True

def _target_app_version_key(path: str):
    """
    Extract a version tuple from a filename for sorting.
    e.g. "Target Application_4.34.0.apk" → (4, 34, 0)
         "Target Application_4.35.apk"   → (4, 35, 0)
         No version found        → (0, 0, 0)
    """
    base = os.path.basename(path)
    m = re.search(r"(\d+)[._](\d+)[._](\d+)", base)
    if m:
        return tuple(int(x) for x in m.groups())
    m = re.search(r"(\d+)[._](\d+)", base)
    if m:
        return (int(m.group(1)), int(m.group(2)), 0)
    return (0, 0, 0)


def install_target_app(device: str) -> bool:
    """
    Install or update Target Application on the device.

    Steps:
      1) Check if TargetApp is already installed — if so, UNINSTALL first (for update).
      2) Find the newest APK or XAPK in APK_FOLDER.
      3) Install using _install_any_package (handles both APK and XAPK).

    Returns True on success, False on failure.
    """
    dlog = _get_device_logger(device)
    print(f"[{device}] install_target_app() – starting")

    # 1) Log if already installed (install over existing = auto-update)
    pkg = _guess_target_package(device)
    if pkg:
        dlog.info(f"── install_target_app ── Already installed as {pkg!r} — installing over (auto-update)")
        print(f"[{device}] TargetApp already installed — installing new version over existing...")

    # 2) Find the newest APK or XAPK
    patterns = (
        r"target.*app.*\.xapk$",
        r"target.*app.*\.apk$",
        r"target_app.*\.xapk$",
        r"target_app.*\.apk$",
    )

    all_files = sorted(glob.glob(os.path.join(APK_FOLDER, "*.*")))
    candidates = []
    for f in all_files:
        base = os.path.basename(f)
        for pat in patterns:
            if re.search(pat, base, flags=re.I):
                candidates.append(f)
                break   # don't double-add

    if not candidates:
        msg = f"No Target Application APK/XAPK found in: {APK_FOLDER}"
        dlog.error(f"── install_target_app ── {msg}")
        print(f"[{device}] ERROR: {msg}")
        return False

    # Sort newest first by version number
    candidates.sort(key=_target_app_version_key, reverse=True)
    target_app_pkg = candidates[0]
    dlog.info(
        f"── install_target_app ── Found {len(candidates)} candidate(s). "
        f"Installing newest: {os.path.basename(target_app_pkg)}"
    )
    print(f"[{device}] Installing from {os.path.basename(target_app_pkg)} ...")

    # 3) Install
    ok = _install_any_package(device, target_app_pkg)
    if not ok:
        dlog.error("── install_target_app ── Installation failed")
        print(f"[{device}] Target Application installation failed.")
        return False

    # Write install time to sheet
    update_status(device, "LastUpdate", str(_dt.datetime.now()))
    dlog.info("── install_target_app ── Installed successfully ✓")
    print(f"[{device}] Target Application installed successfully.")
    return True

def parse_bluestacks_conf(conf_path=BLUESTACKS_CONF):
    """
    Parse the Bluestacks configuration file and extract instance info.

    The config typically contains lines like:
        bst.instance.Nougat32.display_name="TARGET_APP1"
        bst.instance.Nougat32.adb_port="5555"
        bst.instance.Nougat32.status.adb_port="5555"

    Args:
        conf_path: Path to bluestacks.conf (defaults to BLUESTACKS_CONF).

    Returns:
        A sorted list of dicts, each with:
            {
                "instance": <internal instance id>,
                "name"    : <display name from Bluestacks UI>,
                "port"    : <ADB port as string>,
            }

        Sorted by port as integer, so devices[0] is the lowest-port instance.
    """
    # Read the entire config file as text.
    # A missing conf is a normal condition (BlueStacks not installed, or
    # installed somewhere neither candidate path covers), so return an empty
    # list rather than raising FileNotFoundError up through the device scan.
    if not conf_path:
        conf_path = BLUESTACKS_CONF
    try:
        with open(conf_path, "r", encoding="utf-8", errors="ignore") as f:
            text = f.read()
    except FileNotFoundError:
        logging.warning(
            f"BlueStacks config not found at {conf_path}. Checked: "
            + ", ".join(BLUESTACKS_CONF_CANDIDATES)
        )
        return []
    except Exception as exc:
        logging.warning(f"BlueStacks config unreadable at {conf_path}: {exc!r}")
        return []

    # Regex to capture:
    #   - instance id (inst)
    #   - human-friendly display name (name)
    name_re = re.compile(
        r'bst\.instance\.(?P<inst>[^.]+)\.display_name="(?P<name>[^"]+)"'
    )
    # Regex to capture configured adb_port for an instance
    port_re = re.compile(
        r'bst\.instance\.(?P<inst>[^.]+)\.adb_port="(?P<port>\d+)"'
    )
    # Regex to capture *status* adb_port (sometimes more up-to-date than adb_port)
    port_status_re = re.compile(
        r'bst\.instance\.(?P<inst>[^.]+)\.status\.adb_port="(?P<port>\d+)"'
    )

    # by_inst maps instance-id -> {"name": ..., "port": ..., "port_status": ...}
    by_inst = {}

    # Extract display names
    for m in name_re.finditer(text):
        by_inst.setdefault(m["inst"], {})["name"] = m["name"]

    # Extract configured adb ports
    for m in port_re.finditer(text):
        by_inst.setdefault(m["inst"], {})["port"] = m["port"]

    # Extract status adb ports (often the one we actually care about)
    for m in port_status_re.finditer(text):
        by_inst.setdefault(m["inst"], {})["port_status"] = m["port"]

    devices = []
    for inst, d in by_inst.items():
        # Use the display name if present, otherwise fall back to the raw instance id
        name = d.get("name", inst)
        # Prefer status port if available; otherwise use the plain port
        port = d.get("port_status") or d.get("port")
        if port:
            devices.append({"instance": inst, "name": name, "port": port})

    # Sort instances by numeric port for deterministic ordering
    devices.sort(key=lambda x: int(x["port"]))
    return devices

def list_listening_ports(timeout: float = 10.0) -> set:
    """
    One netstat sweep -> the set of TCP ports currently in LISTENING state.

    This is what makes a fast device scan possible.  A BlueStacks instance only
    holds its ADB port open while its window is actually running, so a single
    netstat call tells us which of the configured instances are worth touching.
    Without it, a scan has to `adb connect` every configured port and wait out a
    timeout on each one — which is where the multi-minute scans came from on a
    machine with ~190 configured instances and two windows open.

    Returns a set of port strings.  Returns an empty set on any failure, and
    callers must treat "empty" as "could not determine", not "nothing running".
    """
    ports = set()
    try:
        r = subprocess.run(["netstat", "-ano", "-p", "TCP"],
                           capture_output=True, text=True, timeout=timeout)
        out = r.stdout or ""
        if not out.strip():
            # Some Windows builds reject the -p flag; retry the plain form.
            r = subprocess.run(["netstat", "-an"],
                               capture_output=True, text=True, timeout=timeout)
            out = r.stdout or ""
        for line in out.splitlines():
            if "LISTENING" not in line.upper():
                continue
            # Local address is the second column: 127.0.0.1:5555 or [::]:5555
            parts = line.split()
            if len(parts) < 2:
                continue
            local = parts[1]
            if ":" not in local:
                continue
            port = local.rsplit(":", 1)[-1].strip()
            if port.isdigit():
                ports.add(port)
    except Exception as exc:
        logging.warning(f"list_listening_ports: netstat failed: {exc!r}")
    return ports


def list_adb_listed_ids(timeout: float = 10.0) -> set:
    """
    One `adb devices` call -> the set of ids ADB already knows about.

    Union this with the netstat result: a device can be connected and usable
    while its port shows differently in netstat (or netstat is unavailable
    altogether), and a device already listed by ADB costs nothing to re-check.

    Ids are normalised to the localhost:<port> form the rest of the bot uses.
    """
    ids = set()
    try:
        r = subprocess.run(["adb", "devices"],
                           capture_output=True, text=True, timeout=timeout)
        for line in (r.stdout or "").splitlines()[1:]:
            line = line.strip()
            if not line or "\t" not in line:
                continue
            serial, state = line.split("\t", 1)
            if state.strip() not in ("device", "unauthorized"):
                continue
            serial = serial.strip()
            ids.add(serial)
            if ":" in serial:
                ids.add(f"localhost:{serial.rsplit(':', 1)[-1]}")
                ids.add(f"127.0.0.1:{serial.rsplit(':', 1)[-1]}")
    except Exception as exc:
        logging.warning(f"list_adb_listed_ids: adb devices failed: {exc!r}")
    return ids


def _instance_for_port(port):
    """
    Given an ADB port (e.g. '5555'), find which Bluestacks instance uses it.

    Args:
        port: Port number as int or string.

    Returns:
        A dict: {"instance": <instance_id>, "name": <display_name>}
        or None if no matching instance is found or parsing fails.
    """
    try:
        devices = parse_bluestacks_conf(BLUESTACKS_CONF)
        for d in devices:
            if str(d.get("port")) == str(port):
                # Return only the essential info the caller needs
                return {"instance": d.get("instance"), "name": d.get("name")}
    except Exception:
        # Any error (missing file, parse error, etc.) results in a graceful None
        pass
    return None

def _launch_instance_by_name_or_instance(display_name=None, instance=None):
    """
    Launch a Bluestacks instance either by its internal instance id or by display name.

    Preferred method:
        1) If 'instance' is provided and HD-Player.exe can be found:
               HD-Player.exe --instance <instance>
    Fallback:
        2) If 'display_name' is provided:
               Look for a .lnk on the user's Desktop whose filename contains display_name
               (case-insensitive), and open that shortcut.

    Args:
        display_name: Human-readable Bluestacks name (e.g. "TARGET_APP1").
        instance    : Internal instance id (e.g. "Nougat32").

    Returns:
        True  - if a launch attempt was made successfully (no exception).
        False - if all launch attempts fail.
    """
    hd = _find_hd_player()
    if instance and hd:
        try:
            # Launch Bluestacks directly using the instance id
            subprocess.Popen([hd, "--instance", instance], shell=False)
            return True
        except Exception as e:
            print(f"Failed to start HD-Player for instance {instance}: {e}")

    # Fallback: try to open a Desktop shortcut whose name contains display_name
    try:
        desktop = os.path.join(os.path.expanduser("~"), "Desktop")
        if display_name and os.path.isdir(desktop):
            for fname in os.listdir(desktop):
                # Only consider Windows shortcuts (.lnk files)
                if not fname.lower().endswith(".lnk"):
                    continue
                # If the display name appears anywhere in the shortcut file name, use it
                if display_name.lower() in fname.lower():
                    os.startfile(os.path.join(desktop, fname))
                    return True
    except Exception as e:
        print(f"Fallback .lnk launch failed: {e}")

    # Both direct instance launch and .lnk fallback failed
    return False

def _launch_device_for_worker(dev_id: str) -> bool:
    """
    Launch the BlueStacks instance for dev_id without reading Google Sheets.
    Used by device_worker to avoid per-subprocess sheet API calls that cause 429s.

    Reads only from bluestacks.conf (local file).
    Returns True if a launch was attempted, False if the instance could not be found.
    """
    port = _port_from_adb_id(dev_id)
    if not port:
        print(f"[{dev_id}] _launch_device_for_worker: could not parse port")
        return False
    info = _instance_for_port(port)
    if not info:
        print(f"[{dev_id}] _launch_device_for_worker: no BlueStacks instance found for port {port}")
        return False
    print(f"[{dev_id}] Launching BlueStacks instance {info['instance']} ({info['name']})")
    return _launch_instance_by_name_or_instance(
        display_name=info["name"],
        instance=info["instance"],
    )


def connect_to_devices(current):
    """
    Launch (if needed) and ADB-connect to one or more BlueStacks instances.

    Accepts:
        - A single string:
            * friendly Device name (as in sheet column A), or
            * ADB id (e.g. '127.0.0.1:5555' or 'localhost:5555'), or
            * comma-separated list of the above ('TARGET_APP1,localhost:5555').
        - OR an iterable of such entries.

    Device name <-> ADB id mapping is taken from the Control sheet rows.
    """
    # Build mappings from the Control sheet
    cfg = read_control_config()
    rows = cfg["rows"]
    id_to_name = {r["device_id"]: r["friendly"] for r in rows}
    name_to_id = {r["friendly"].lower(): r["device_id"] for r in rows if r["friendly"]}

    # Normalize 'current' to a list of non-empty, stripped strings
    selected = current.split(",") if isinstance(current, str) else list(current)
    selected = [s.strip() for s in selected if s and str(s).strip()]

    for entry in selected:
        entry_norm = entry.strip()
        adb_id = None
        friendly = None

        if ":" in entry_norm:
            # Treat as an ADB id
            adb_id = entry_norm
            friendly = id_to_name.get(adb_id)
        else:
            # Treat as a friendly name from the sheet
            adb_id = name_to_id.get(entry_norm.lower())
            friendly = entry_norm

        if not adb_id:
            print(f"No matching device found for '{entry_norm}'.")
            continue

        port = _port_from_adb_id(adb_id)

        # Quick check if the device is already online
        if _adb_wait_for_device(adb_id, timeout=5, interval=1):
            label = friendly or id_to_name.get(adb_id) or "Unknown"
            print(f"Connected to {adb_id} ({label}).")
            continue

        # ── Device not online — launch the instance ───────────────────────────
        if not port:
            print(f"Port not parsable for '{adb_id}'. Skipping.")
            continue

        info = _instance_for_port(port)
        if not info:
            print(f"No instance found in config for port {port} ({adb_id}). Skipping.")
            continue

        print(f"Launching BlueStacks instance {info['instance']} ({info['name']}) for {adb_id} ...")
        ok = _launch_instance_by_name_or_instance(
            display_name=info["name"],
            instance=info["instance"],
        )
        if not ok:
            print(f"Could not launch instance {info['instance']} for {adb_id}.")
            continue

        # ── Active retry within 45s window ───────────────────────────────────
        # BlueStacks TCP devices are not auto-discovered by ADB — `adb connect`
        # must be called explicitly after the instance is up, otherwise ADB
        # never sees the port even when BlueStacks is fully ready.
        # Poll every ~10s: call adb connect, then check if device responded.
        connected = False
        t_launch  = time.time()
        attempt   = 0
        while time.time() - t_launch < 45:
            attempt += 1
            try:
                subprocess.run(
                    ["adb", "connect", adb_id],
                    capture_output=True, timeout=5
                )
            except Exception:
                pass
            if _adb_wait_for_device(adb_id, timeout=8, interval=2):
                connected = True
                break
            print(f"  [{adb_id}] adb connect attempt {attempt} — not ready yet, retrying…")
            time.sleep(2)

        if not connected:
            print(f"Failed to connect to {adb_id} after launching instance.")
            continue

        label = friendly or id_to_name.get(adb_id) or "Unknown"
        print(f"Connected to {adb_id} ({label}).")

def get_device_status():
    """
    Run 'adb devices' and return a dict of device_id -> status.

    Example:
        {
            "127.0.0.1:5555": "device",
            "127.0.0.1:5557": "offline",
        }
    """
    result = subprocess.run(["adb", "devices"], capture_output=True, text=True)
    # Skip the first header line: "List of devices attached"
    devices_output = result.stdout.strip().split("\n")[1:]
    devices_status = {}
    for device in devices_output:
        if not device.strip():
            continue                        # FIX: skip blank trailing lines
        parts = device.split("\t", 1)       # FIX: safe split — at most 1 split
        if len(parts) < 2:
            continue                        # FIX: skip any line that isn't "id<tab>status"
        device_id = parts[0].strip()
        status    = parts[1].strip()
        if device_id:
            devices_status[device_id] = status
    return devices_status

def restart_offline_devices(devices_status):
    """
    For each device marked 'offline' in devices_status:
        1) Map its ADB port to a BlueStacks instance via _instance_for_port().
        2) Launch that instance via _launch_instance_by_name_or_instance().
        3) Wait briefly, then 'adb connect <device_id>'.

    Args:
        devices_status: dict of {device_id: status} from get_device_status().
    """
    for device_id, status in devices_status.items():
        if status != "offline":
            continue

        port = _port_from_adb_id(device_id)
        if not port:
            print(f"Device {device_id} is offline but port could not be parsed; skipping.")
            continue

        info = _instance_for_port(port)
        if not info:
            print(f"No BlueStacks instance found in config for port {port} ({device_id}). Skipping.")
            continue

        print(f"Device {device_id} is offline. Reopening instance {info['instance']} ({info['name']})...")
        ok = _launch_instance_by_name_or_instance(display_name=info["name"], instance=info["instance"])
        if not ok:
            print(f"Failed to launch instance {info['instance']} for {device_id}.")
            continue

        time.sleep(5)  # Give the emulator a moment to start

        try:
            subprocess.run(f"adb connect {device_id}", shell=True, check=True)
            print(f"Reconnected to {device_id}.")
        except subprocess.CalledProcessError as e:
            print(f"Failed to reconnect to {device_id}. Error: {e}")

def get_device_identifier(current):
    """
    Resolve a user-specified identifier to an ADB device id.

    Returns:
        device_id string on success, or None if there's no match.
    """
    result = subprocess.run(["adb", "devices"], capture_output=True, text=True)
    devices = result.stdout.strip().split("\n")[1:]

    if not devices:                        # FIX: was `not devices or len(devices) == 0`
        print("No devices connected.")
        return None

    cfg = read_control_config()
    rows = cfg["rows"]
    id_to_name = {r["device_id"]: r["friendly"] for r in rows}

    print("Connected devices:")
    for device in devices:
        parts = device.split("\t", 1)
        device_id = parts[0].strip() if parts else ""
        if not device_id:
            continue
        window_name = id_to_name.get(device_id, "Unknown")
        print(f"{device_id} - {window_name}")

    user_input = (current or "").strip()

    for device in devices:
        parts = device.split("\t", 1)
        device_id = parts[0].strip() if parts else ""
        if not device_id:
            continue
        if user_input == device_id:
            return device_id

    for dev_id, name in id_to_name.items():
        if name == user_input:
            return dev_id

    print("No matching device identifier or window name found.")
    return None

def _find_package_path(apk_folder, patterns):
    """
    Find a file in apk_folder whose name matches any of the given regex patterns.

    This searches for *.apk or *.xapk (or any extension) and returns the first
    match based on filename.

    Args:
        apk_folder: Folder to search.
        patterns  : Iterable of regex patterns (strings) to test against filenames.

    Returns:
        Full path to the first matching file, or None if nothing matches.
    """
    # Grab all files in the folder (any extension), sorted for deterministic behavior
    files = sorted(glob.glob(os.path.join(apk_folder, "*.*")))
    for f in files:
        base = os.path.basename(f)
        for pat in patterns:
            if re.search(pat, base, flags=re.I):
                return f
    return None

def _gather_xapk_contents(xapk_path, work_root=None):
    """
    Unzip a .xapk and collect its split APKs and optional OBB directories.

    Returns a dict:
        {
          "workdir": <temp dir>,
          "apks": [list of apk fullpaths (base.apk first if present)],
          "obb_dirs": [list of "<.../Android/obb/<package>>" directories]
        }

    Args:
        xapk_path: Path to the .xapk file.
        work_root: Optional working directory. If None, a temp dir is created.

    Returns:
        A dict with 'workdir', 'apks', and 'obb_dirs' as described above.
    """
    if work_root is None:
        # Create a temp directory to unpack the .xapk into
        work_root = tempfile.mkdtemp(prefix="xapk_")

    # Extract all XAPK contents into the working directory
    with zipfile.ZipFile(xapk_path, "r") as zf:
        zf.extractall(work_root)

    # Collect all .apk files (including base + split apks)
    apk_files = []
    for root, _, files in os.walk(work_root):
        for fn in files:
            if fn.lower().endswith(".apk"):
                apk_files.append(os.path.join(root, fn))

    # Sort so that base.apk (or base-*.apk) comes first, then others alphabetically
    def sort_key(p):
        n = os.path.basename(p).lower()
        return (0 if n == "base.apk" or n.startswith("base-") else 1, n)

    apk_files.sort(key=sort_key)

    # Collect OBB package directories under Android/obb
    obb_entries = []
    obb_root = os.path.join(work_root, "Android", "obb")
    if os.path.isdir(obb_root):
        for pkg in os.listdir(obb_root):
            full_pkg_dir = os.path.join(obb_root, pkg)
            if os.path.isdir(full_pkg_dir):
                obb_entries.append(full_pkg_dir)

    return {"workdir": work_root, "apks": apk_files, "obb_dirs": obb_entries}

def _push_obb_dirs(device, obb_dirs):
    """
    Push OBB files to /sdcard/Android/obb/<package>/ on the device.

    Args:
        device  : ADB device id.
        obb_dirs: List of local package directories (each containing .obb files).

    Returns:
        True  - if all applicable pushes succeed.
        False - if any adb push fails.
    """
    ok = True
    for src_pkg_dir in obb_dirs:
        pkg = os.path.basename(src_pkg_dir)
        dest_pkg_dir = f"/sdcard/Android/obb/{pkg}"

        # Ensure the destination directory exists on the device
        subprocess.run(
            ["adb", "-s", device, "shell", "mkdir", "-p", dest_pkg_dir],
            capture_output=True,
            text=True,
        )

        # Push each .obb file into the destination package directory
        for fn in os.listdir(src_pkg_dir):
            if not fn.lower().endswith(".obb"):
                continue
            src = os.path.join(src_pkg_dir, fn)
            print(f"[{device}] Pushing OBB → {pkg}/{fn}")
            res = subprocess.run(
                ["adb", "-s", device, "push", src, f"{dest_pkg_dir}/"],
                capture_output=True,
                text=True,
            )
            out = (res.stdout or "") + (res.stderr or "")
            print(out.strip())
            ok = ok and (res.returncode == 0)
    return ok

def _run_with_timeout(cmd, timeout=180):
    """
    Run a command with a timeout.

    Args:
        cmd    : List of command arguments (e.g. ["adb", "-s", device, "install", ...]).
        timeout: Max seconds to wait before killing the process.

    Returns:
        (rc, combined_output, timed_out)
        where:
            rc              : process return code (124 if killed on timeout),
            combined_output : stdout + stderr as a single string,
            timed_out       : True if a timeout occurred, False otherwise.
    """
    try:
        p = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        try:
            out, err = p.communicate(timeout=timeout)
            combo = (out or "") + (err or "")
            return p.returncode, combo, False
        except subprocess.TimeoutExpired:
            # Kill the process on timeout and capture whatever output we got
            p.kill()
            out, err = p.communicate()
            combo = (out or "") + (err or "")
            return 124, combo, True
    except Exception as e:
        # A failure to even start the process
        return 1, f"Exception: {e}", False

def _adb_install_streaming(device, apk_path, timeout=180):
    """
    First attempt: normal streaming install via 'adb install'.

    Command:
        adb -s <device> install -r -d -g <apk_path>

    Flags:
        -r : replace existing application
        -d : allow version code downgrade
        -g : grant all runtime permissions

    Returns:
        (ok, timed_out, output)
        where:
            ok       : True if install is considered successful,
            timed_out: True if a timeout occurred,
            output   : combined stdout+stderr from the install command.
    """
    print(f"[{device}] (streaming) adb install: {os.path.basename(apk_path)}")
    cmd = ["adb", "-s", device, "install", "-r", "-d", "-g", apk_path]
    rc, out, to = _run_with_timeout(cmd, timeout=timeout)
    print(out.strip())

    # FIX: INSTALL_FAILED_ALREADY_EXISTS comes with a non-zero exit code,
    # so it must be checked independently of rc == 0.
    already_exists = "INSTALL_FAILED_ALREADY_EXISTS" in out
    clean_success  = (rc == 0 and "Success" in out)
    ok = clean_success or already_exists

    return ok, to, out

def _adb_push_and_pm_install(device, apk_path, timeout=180):
    """
    Safer fallback: push the APK to the device, then run 'pm install' inside.

    Steps:
        1) adb push <apk_path> /data/local/tmp/<filename>
        2) adb shell pm install -r -d -g /data/local/tmp/<filename>
        3) adb shell rm -f /data/local/tmp/<filename>   (cleanup)

    Returns:
        True  - if install is considered successful.
        False - on any failure or timeout.
    """
    remote = f"/data/local/tmp/{os.path.basename(apk_path)}"
    print(f"[{device}] (fallback) pushing → {remote}")
    rc1, out1, to1 = _run_with_timeout(
        ["adb", "-s", device, "push", apk_path, remote],
        timeout=timeout,
    )
    print(out1.strip())
    if rc1 != 0 or to1:
        print(f"[{device}] push failed (timeout={to1})")
        return False

    print(f"[{device}] (fallback) pm install -r -d -g {remote}")
    rc2, out2, to2 = _run_with_timeout(
        ["adb", "-s", device, "shell", "pm", "install", "-r", "-d", "-g", remote],
        timeout=timeout,
    )
    print(out2.strip())

    # Best-effort cleanup of the temporary APK file
    subprocess.run(
        ["adb", "-s", device, "shell", "rm", "-f", remote],
        capture_output=True,
        text=True,
    )

    if to2:
        print(f"[{device}] pm install timed out.")
        return False

    ok_texts = ("Success", "INSTALL_FAILED_ALREADY_EXISTS")
    return (rc2 == 0 and any(t in out2 for t in ok_texts))

def _install_any_package(device, pkg_path):
    """
    Install a package (.apk or .xapk) on the device.

    Logic:
        - If extension is .apk:
            1) Try streaming install with timeout via _adb_install_streaming().
            2) If that fails or times out, fallback to _adb_push_and_pm_install().
        - If extension is .xapk:
            1) Unzip into a temporary directory via _gather_xapk_contents().
            2) Install split APKs using 'adb install-multiple'.
            3) Push any OBB dirs using _push_obb_dirs().
            4) Clean up temporary directory.
        - Otherwise:
            - Print an error and return False.

    Args:
        device  : ADB device id.
        pkg_path: Path to the .apk or .xapk file.

    Returns:
        True  - if the install (and any OBB push) is successful.
        False - otherwise.
    """
    ext = os.path.splitext(pkg_path)[1].lower()

    if ext == ".apk":
        # 1) Normal streaming install with timeout
        ok, timed_out, out = _adb_install_streaming(device, pkg_path, timeout=180)
        if ok:
            return True

        # 2) If streaming failed or timed out, use push+pm fallback
        print(f"[{device}] streaming install failed or hung — falling back to push+pm method.")
        return _adb_push_and_pm_install(device, pkg_path, timeout=240)

    if ext == ".xapk":
        print(f"[{device}] Preparing XAPK: {os.path.basename(pkg_path)}")
        bundle = _gather_xapk_contents(pkg_path)
        apks = bundle["apks"]
        if not apks:
            print(f"[{device}] No APKs found inside XAPK.")
            shutil.rmtree(bundle["workdir"], ignore_errors=True)
            return False

        print(f"[{device}] Installing split APKs via install-multiple …")
        rc, out, to = _run_with_timeout(
            ["adb", "-s", device, "install-multiple", "-r", "-d", "-g", *apks],
            timeout=240,
        )
        print(out.strip())
        ok_install = (rc == 0 and "Success" in out and not to)

        # If there are OBB dirs in the bundle, push them too
        ok_obb = True
        if bundle["obb_dirs"]:
            ok_obb = _push_obb_dirs(device, bundle["obb_dirs"])

        # Clean up temp directory
        shutil.rmtree(bundle["workdir"], ignore_errors=True)
        return ok_install and ok_obb

    print(f"[{device}] Unsupported package type: {pkg_path}")
    return False

def install_apk_folder(device, apk_folder=APK_FOLDER, reinstall_flags=("-r", "-d")):
    """
    Install all .apk files from a given folder onto the device.

    Args:
        device         : ADB device id (e.g. 'localhost:5555').
        apk_folder     : Folder to search for *.apk files (default: APK_FOLDER).
        reinstall_flags: Extra flags to pass to 'adb install', e.g.:
                         -r : replace existing app
                         -d : allow version downgrade

    Behavior:
        - Finds all *.apk files in apk_folder (sorted by filename).
        - For each APK:
            * Runs: adb -s <device> install <reinstall_flags...> <apk_path>
            * Prints stdout/stderr from adb.
        - Tracks if any install fails.

    Returns:
        True  - if all installs reported "Success".
        False - if no APKs found or any install fails/errors.
    """
    try:
        apk_paths = sorted(glob.glob(os.path.join(apk_folder, "*.apk")))
        if not apk_paths:
            print(f"[{device}] No .apk files found in: {apk_folder}")
            return False

        all_ok = True
        for apk_path in apk_paths:
            cmd = ["adb", "-s", device, "install", *reinstall_flags, apk_path]
            print(f"[{device}] Installing: {os.path.basename(apk_path)}")
            try:
                res = subprocess.run(cmd, capture_output=True, text=True, check=False)
                out = (res.stdout or "") + (res.stderr or "")
                print(out.strip())
                if "Success" not in out:
                    all_ok = False
            except Exception as e:
                print(f"[{device}] Install failed for {apk_path}: {e}")
                all_ok = False

        return all_ok

    except Exception as e:
        print(f"[{device}] install_apk_folder error: {e}")
        return False

# ------------------------------------------------------------
# 4. WINDOWS OS CONTROL
# ------------------------------------------------------------

def close_window_by_title(window_title):
    try:
        subprocess.run(
            ["taskkill", "/FI", f"WINDOWTITLE eq {window_title}", "/F"],
            check=True,
            capture_output=True,
        )
        print(f"Window with title '{window_title}' closed successfully.")
    except subprocess.CalledProcessError as e:
        print(f"Failed to close window with title '{window_title}'. Error: {e}")

def get_window_name_from_shortcut(device_id):
    """
    Legacy helper: now returns the expected window title for a device
    based on the Control sheet, not a .lnk shortcut.

    Assumption:
        - The sheet's 'Device' value (friendly name) matches the BlueStacks
          window title used in Windows.

    Args:
        device_id: ADB device id.

    Returns:
        The friendly name from the sheet, or None if not found.
    """
    try:
        cfg = read_control_config()
        for row in cfg["rows"]:
            if row["device_id"] == device_id:
                return row["friendly"]
    except Exception as e:
        print(f"Error reading Control sheet for window name: {e}")
    return None

def open_shortcut(shortcut_path):
    """
    Open a Windows shortcut (.lnk) using os.startfile.

    Args:
        shortcut_path: Full path to the .lnk file.
    """
    try:
        os.startfile(shortcut_path)
        print(f"Shortcut {shortcut_path} opened successfully.")
    except Exception as e:
        print(f"Error opening shortcut {shortcut_path}: {e}")

# ------------------------------------------------------------
# 5. IMAGING & SCREENSHOTS
# ------------------------------------------------------------


# Latest screenshot the NORMAL workflow already took, per device.
#
# Diagnostics read this instead of calling get_screenshot(). That matters
# because get_screenshot holds a per-device lock, and while recording its budget
# is 12s x 2 attempts — so a diagnostic capture could hold the lock ~25s and
# stall the actual automation behind it. Nothing here ever takes an extra
# screenshot; the cache is only ever fed frames the workflow needed anyway.
_LAST_SCREENSHOT = {}          # device -> (image, monotonic_timestamp)
UNEXPECTED_CACHE_MAX_AGE = 3.0 # a frame older than this is not worth saving


def _cache_screenshot(device, img) -> None:
    """Record a frame the workflow just obtained. Never raises."""
    try:
        if device and img is not None:
            _LAST_SCREENSHOT[device] = (img, time.monotonic())
    except Exception:
        pass


def get_cached_screenshot(device: str, max_age: float = UNEXPECTED_CACHE_MAX_AGE):
    """
    Most recent workflow screenshot for this device, or None if too old/absent.

    Deliberately does NOT capture: callers that get None must go without.
    """
    try:
        entry = _LAST_SCREENSHOT.get(device)
        if not entry:
            return None
        img, ts = entry
        if (time.monotonic() - ts) > max_age:
            return None
        return img
    except Exception:
        return None


def clear_cached_screenshot(device: str) -> None:
    """
    Drop the cached frame for a device.

    Called from the reset paths. Two reasons: a frame from before an emulator
    relaunch or a device swap shows a screen that no longer exists, and holding
    a decoded PIL image per device keeps real memory alive for the whole run
    when devices are processed one after another.
    """
    try:
        _LAST_SCREENSHOT.pop(device, None)
    except Exception:
        pass


def get_screenshot(device=None, retries=2):
    lock = _get_screenshot_lock(device) if device else _threading.Lock()

    # While screenrecord holds the capture pipeline, screencap legitimately takes
    # much longer. One patient attempt beats three short blocked ones — the short
    # ones were tripping the device-health threshold and failing healthy devices.
    _timeout = SCREENSHOT_TIMEOUT_NORMAL
    try:
        if device and recording_enabled_or_active(device):
            _timeout = SCREENSHOT_TIMEOUT_RECORDING
            if retries > SCREENSHOT_RETRIES_RECORDING:
                retries = SCREENSHOT_RETRIES_RECORDING
            _get_device_logger(device).debug(
                f"[SCREENSHOT] recording active — using long timeout "
                f"({_timeout}s, retries={retries})")
    except Exception:
        pass

    with lock:
        if not device:
            cmd = ["adb", "exec-out", "screencap", "-p"]
        else:
            cmd = ["adb", "-s", device, "exec-out", "screencap", "-p"]

        for attempt in range(retries + 1):
            try:
                result = subprocess.run(cmd, capture_output=True, check=True,
                                        timeout=_timeout)

                if not result.stdout:
                    raise OSError("Empty screenshot data")

                image_data = io.BytesIO(result.stdout)
                img = Image.open(image_data)
                img.load()
                # Passive: this frame was needed by the workflow anyway.
                _cache_screenshot(device, img)
                return img

            except subprocess.TimeoutExpired:
                if attempt < retries:
                    print(f"[{device}] Screenshot timeout (attempt {attempt + 1}/{retries + 1}), retrying...")
                    time.sleep(1)
                    continue
                else:
                    print(f"[{device}] Screenshot timed out after {retries + 1} attempts")
                    _get_device_logger(device).error(f"── get_screenshot ── timed out after {retries + 1} attempts")
                    return None

            except subprocess.CalledProcessError as e:
                if attempt < retries:
                    print(f"[{device}] Screenshot failed (attempt {attempt + 1}/{retries + 1}), retrying...")
                    time.sleep(1)
                    continue
                else:
                    exit_code_hex = hex(e.returncode & 0xFFFFFFFF) if e.returncode else "unknown"
                    print(f"[{device}] Screenshot failed after {retries + 1} attempts: "
                        f"exit code {e.returncode} ({exit_code_hex})")
                    _get_device_logger(device).error(f"── get_screenshot ── exit {e.returncode} ({exit_code_hex})")
                    return None

            except Exception as e:
                if attempt < retries:
                    print(f"[{device}] Screenshot error (attempt {attempt + 1}/{retries + 1}): {e}, retrying...")
                    time.sleep(1)
                    continue
                else:
                    print(f"[{device}] Screenshot failed after {retries + 1} attempts: {e}")
                    _get_device_logger(device).error(f"── get_screenshot ── {type(e).__name__}: {e}")
                    return None
        # Should never reach here due to the loop structure, but just in case
        return None
# -------------------------
# Per-run temp artifacts (screenshots)
# -------------------------
RUN_TMP_DIR = tempfile.mkdtemp(prefix="target_app_run_")

def _sanitize_device_id(device: str) -> str:
    # "localhost:5555" -> "localhost_5555"
    return re.sub(r"[^a-zA-Z0-9._-]+", "_", (device or "unknown"))

def _device_screenshot_path(device: str) -> str:
    return os.path.join(RUN_TMP_DIR, f"screen_{_sanitize_device_id(device)}.png")

def cleanup_device_files(device: str) -> None:
    """Delete per-device artifacts (currently only the screenshot)."""
    try:
        p = _device_screenshot_path(device)
        if os.path.exists(p):
            os.remove(p)
    except Exception as e:
        print(f"[{device}] cleanup_device_files failed: {e}")


# ------------------------------------------------------------
# 6. OCR & TEXT DETECTION (Tesseract / EasyOCR)
# ------------------------------------------------------------
# ========= Unified OCR helper (Tesseract + EasyOCR) =========
# Requires: pytesseract, cv2, numpy, PIL.Image, and optional easyocr.



# cache of EasyOCR readers so we don't re-load models every call
_EASYOCR_READERS = {}
# Serialises reader construction. The warm-up thread and a real OCR call can
# race for the same key; without this both would build a Reader and pay the
# model-load cost twice (and the second would overwrite the first).
_EASYOCR_LOCK = _threading.Lock()


def _get_easyocr_reader(langs=("en",), gpu=False):
    """
    Return a cached easyocr.Reader configured for the given languages/GPU flag.

    If easyocr is not installed, this will raise a RuntimeError the first time
    you actually ask for an EasyOCR reader (engine="easyocr").
    """
    # NOTE: this used to declare `global _easyocr_READERS` — a different name
    # from the actual cache. Harmless in practice (the function only mutates the
    # dict, never rebinds it) but a latent bug and misleading to read.
    global _EASYOCR_READERS
    try:
        import easyocr as _easyocr_mod
    except ImportError:
        raise RuntimeError(
            "easyocr is not installed. Install with 'pip install easyocr' "
            "or call text_detect(..., engine='tesseract')."
        )
    key = (tuple(sorted(langs)), bool(gpu))

    # Fast path: already built, no locking needed.
    reader = _EASYOCR_READERS.get(key)
    if reader is not None:
        return reader

    # Slow path under the lock. Re-check inside — the warm-up thread may have
    # finished building this exact reader while we were waiting, in which case
    # we reuse it instead of loading the models a second time.
    with _EASYOCR_LOCK:
        reader = _EASYOCR_READERS.get(key)
        if reader is not None:
            return reader
        reader = _easyocr_mod.Reader(list(langs), gpu=bool(gpu), verbose=False)
        _EASYOCR_READERS[key] = reader
        return reader


# Only used to flag a warm-up that is taking unusually long. Nothing waits on
# it — warm_easyocr() never blocks the caller.
EASYOCR_WARMUP_SLOW_AFTER = 60.0


def warm_easyocr(dlog=None, langs=("en",), gpu: bool = False) -> None:
    """
    Build the EasyOCR reader once, off the critical path.

    _EASYOCR_READERS already caches per process, so this does not add a second
    cache — it simply pays the model-load cost at worker startup instead of
    during VPN Connect detection or Loading. Measured ~1.5s difference between
    the first call and the steady-state median, so this is a small win, not a
    large one.

    FIRE AND FORGET — returns immediately.

    An earlier version joined the thread for up to 60s, which defeated the whole
    point: worker startup then blocked on the very model load this was meant to
    move off the critical path. The reader is built in the background; if a real
    OCR call arrives first it simply waits on _EASYOCR_LOCK and reuses whichever
    reader finishes, so the models are never loaded twice.

    If EasyOCR is missing or fails, it is logged once and the run continues on
    Tesseract/UIAutomator.

    Deliberately NOT called from the controller: multiprocessing spawn means
    every worker loads its own copy anyway.
    """
    if dlog is None:
        dlog = logging.getLogger(__name__)

    def _work():
        t0 = time.time()
        try:
            dlog.info("[EASYOCR] EasyOCR warmup start")
            _get_easyocr_reader(langs=langs, gpu=gpu)
            _el = time.time() - t0
            dlog.info(f"[EASYOCR] EasyOCR warmup done duration={_el:.1f}s")
            if _el > EASYOCR_WARMUP_SLOW_AFTER:
                dlog.warning(f"[EASYOCR] warmup was slow ({_el:.0f}s) — the first "
                             f"OCR call may have waited on it")
        except RuntimeError as exc:
            dlog.warning(f"[EASYOCR] EasyOCR unavailable ({exc}) — continuing with "
                         f"Tesseract/UIAutomator fallback")
        except Exception as exc:
            dlog.warning(f"[EASYOCR] EasyOCR warmup failed after "
                         f"{time.time() - t0:.1f}s: {exc!r} — continuing with "
                         f"Tesseract/UIAutomator fallback")

    try:
        # No join. Startup continues straight to launching/connecting the device
        # while the models load behind it.
        _threading.Thread(target=_work, daemon=True,
                          name="easyocr_warmup").start()
        dlog.debug("[EASYOCR] warmup dispatched to background — not waiting")
    except Exception as exc:
        dlog.debug(f"[EASYOCR] warmup could not start: {exc!r}")

def text_detect(
    *,
    device=None,
    image=None,
    region=None,
    engine="tesseract",

    # --- common pre-processing (applied to BOTH engines) ---
    to_gray=True,
    invert=False,
    binarize=False,
    threshold_method="otsu",   # "otsu" or "fixed"
    threshold_value=128,
    strip=True,

    # --- Tesseract options ---
    tess_lang="eng",
    tess_oem=1,
    tess_psm=6,
    tess_whitelist=None,
    tess_blacklist=None,
    tess_extra_config=None,

    # --- EasyOCR options (simple) ---
    easy_langs=("en",),
    easy_gpu=False,
    easy_allowlist=None,
    easy_blocklist=None,
    easy_paragraph=False,
    easy_detail=None,          # None → auto based on return_boxes

    # --- output ---
    return_boxes=False,
):
    """
    Unified OCR helper using Tesseract or EasyOCR with a small set of knobs.

    Typical call from this script:

        num_txt = text_detect(
            device="localhost:5565",
            region=(800, 200, 1000, 260),
            engine="tesseract",
            tess_lang="eng",
            tess_oem=1,
            tess_psm=7,
            tess_whitelist="0123456789",
            to_gray=True,
            binarize=True,
            return_boxes=False,
        )

    Returns:
      if return_boxes=False -> string (possibly multi-line)
      if return_boxes=True  -> list of {"text", "conf", "bbox"}
    """

    # ---------- 1) Get a PIL image ----------
    if image is None:
        if device is None:
            raise ValueError("text_detect: either 'image' or 'device' must be provided.")
        # Use your existing screenshot helper
        image = get_screenshot(device)
    
    if image is None:
        _get_device_logger(device).error(f"── text_detect ── screenshot returned None (device offline?)")
        return [] if return_boxes else ""

    if not isinstance(image, Image.Image):
        # Allow passing a numpy array
        image = Image.fromarray(image)

    # Optional region crop in *original* image coordinates
    if region is not None:
        x1, y1, x2, y2 = region
        image = image.crop((int(x1), int(y1), int(x2), int(y2)))

    # ---------- 2) Pre-process with OpenCV (shared) ----------
    np_img = np.array(image)

    # If already single-channel, keep as-is; else convert to BGR
    if np_img.ndim == 2:
        proc = np_img
    else:
        if np_img.shape[2] == 4:
            proc = cv2.cvtColor(np_img, cv2.COLOR_RGBA2BGR)
        else:
            proc = cv2.cvtColor(np_img, cv2.COLOR_RGB2BGR)

    if to_gray and proc.ndim == 3:
        proc = cv2.cvtColor(proc, cv2.COLOR_BGR2GRAY)

    if invert:
        proc = cv2.bitwise_not(proc)

    if binarize:
        if threshold_method == "otsu":
            _, proc = cv2.threshold(
                proc, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU
            )
        else:
            _, proc = cv2.threshold(
                proc, int(threshold_value), 255, cv2.THRESH_BINARY
            )

    # ---------- 3) Tesseract branch ----------
    eng = engine.lower()
    if eng == "tesseract":
        cfg_parts = [f"--oem {int(tess_oem)}", f"--psm {int(tess_psm)}"]

        if tess_whitelist:
            cfg_parts.append(f"-c tessedit_char_whitelist={tess_whitelist}")
        if tess_blacklist:
            cfg_parts.append(f"-c tessedit_char_blacklist={tess_blacklist}")
        if tess_extra_config:
            if isinstance(tess_extra_config, (list, tuple)):
                cfg_parts.extend(tess_extra_config)
            else:
                cfg_parts.append(str(tess_extra_config))

        cfg_str = " ".join(cfg_parts)

        if return_boxes:
            # Use image_to_data to get per-box text + confidence
            data = pytesseract.image_to_data(
                proc,
                lang=tess_lang,
                config=cfg_str,
                output_type=pytesseract.Output.DICT,
            )
            results = []
            n = len(data.get("text", []))
            for i in range(n):
                raw_text = data["text"][i]
                text = raw_text.strip() if strip and isinstance(raw_text, str) else raw_text
                if not text:
                    continue
                conf_raw = data.get("conf", ["-1"] * n)[i]
                try:
                    conf = float(conf_raw)
                except Exception:
                    conf = None
                x = int(data.get("left", [0] * n)[i])
                y = int(data.get("top", [0] * n)[i])
                w = int(data.get("width", [0] * n)[i])
                h = int(data.get("height", [0] * n)[i])
                bbox = (x, y, x + w, y + h)
                results.append({"text": text, "conf": conf, "bbox": bbox})
            return results

        # Simple text-only case
        txt = pytesseract.image_to_string(
            proc,
            lang=tess_lang,
            config=cfg_str,
        )
        return txt.strip() if strip and isinstance(txt, str) else txt

    # ---------- 4) EasyOCR branch ----------
    elif eng == "easyocr":
        # Normalize languages to a list/tuple
        if isinstance(easy_langs, str):
            langs = [s.strip() for s in easy_langs.split(",") if s.strip()]
        else:
            langs = list(easy_langs)
        if not langs:
            langs = ["en"]

        reader = _get_easyocr_reader(langs=tuple(langs), gpu=easy_gpu)

        # detail=1 exposes bbox/text/conf; detail=0 is text only
        if easy_detail is None:
            detail = 1 if return_boxes else 0
        else:
            detail = int(easy_detail)

        results = reader.readtext(
            proc,
            detail=detail,
            paragraph=easy_paragraph,
            allowlist=easy_allowlist,
            blocklist=easy_blocklist,
        )

        if not return_boxes:
            # Caller only wants text; collapse EasyOCR output
            if detail == 0:
                texts = [
                    t.strip() if strip and isinstance(t, str) else t
                    for t in results
                ]
            else:
                texts = []
                for item in results:
                    if not isinstance(item, (list, tuple)) or len(item) < 2:
                        continue
                    text = item[1]
                    text = text.strip() if strip and isinstance(text, str) else text
                    if text:
                        texts.append(text)
            joined = "\n".join(texts)
            return joined.strip() if strip else joined

        # Caller wants bounding boxes; normalize to the same dict format
        norm = []
        for item in results:
            if not isinstance(item, (list, tuple)) or len(item) < 3:
                continue
            bbox, text, conf = item
            text = text.strip() if strip and isinstance(text, str) else text
            if not text:
                continue
            xs = [int(p[0]) for p in bbox]
            ys = [int(p[1]) for p in bbox]
            x1b, x2b = min(xs), max(xs)
            y1b, y2b = min(ys), max(ys)
            norm.append({
                "text": text,
                "conf": float(conf) if conf is not None else None,
                "bbox": (x1b, y1b, x2b, y2b),
            })
        return norm

    else:
        raise ValueError(f"text_detect: unknown engine '{engine}'.")

# Updated Wrappers to accept an optional 'image'
def check_text(device: str, x1, y1, x2, y2, image=None) -> str:
    return (text_detect(
        device=device,
        image=image,  # Pass the image through
        region=(int(x1), int(y1), int(x2), int(y2)),
        engine="tesseract",
        tess_oem=1,
        tess_psm=6,
        to_gray=True,
        binarize=True,
        strip=True,
        return_boxes=False,
    ) or "").strip()

def check_text1(device: str, x1, y1, x2, y2, image=None) -> str:
    return (text_detect(
        device=device,
        image=image,  # Pass the image through
        region=(int(x1), int(y1), int(x2), int(y2)),
        engine="easyocr",
        to_gray=True,
        binarize=True,
        strip=True,
        return_boxes=False,
    ) or "").strip()

def check_text2(device: str, x1, y1, x2, y2, image=None) -> str:
    allow = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ "
    return (text_detect(
        device=device,
        image=image,  # Pass the image through
        region=(int(x1), int(y1), int(x2), int(y2)),
        engine="easyocr",
        easy_allowlist=allow,
        to_gray=True,
        binarize=True,
        strip=True,
        return_boxes=False,
    ) or "").strip()

def find_text(device: str, target_text: str, engine: str = "easyocr"):
    """
    Scans the screen for specific text and returns the first match details.
    
    Args:
        device (str): ADB device ID.
        target_text (str): The text to search for (case-insensitive).
        engine (str): 'tesseract' (faster) or 'easyocr' (smarter). Default is EasyOCR.

    Returns:
        dict: {'text': 'Found Text', 'bbox': (x1, y1, x2, y2), 'conf': 0.9} 
        OR 
        None: if the text was not found.
    """
    # 1. Get all text on screen with bounding boxes
    results = text_detect(
        device=device,
        engine=engine,
        return_boxes=True,  # Crucial: gets us coordinates + text
        to_gray=True
    )

    if not isinstance(results, list):
        return None

    # 2. Search for the target
    target_lower = target_text.lower()
    
    for item in results:
        # Check if target is inside the found text (e.g. "Proton" in "Proton VPN")
        if target_lower in item.get('text', '').lower():
            return item  # Returns the whole dict: {'text':..., 'bbox':..., 'conf':...}

    return None

def _build_ocr_kwargs_from_cfg(cfg: dict | None, engine: str) -> dict:
    """
    Convert a JSON 'cfg' dict into kwargs for text_detect().

    If cfg is None/empty and engine is tesseract → we use default:
        to_gray=True, tess_lang="eng", tess_oem=1, tess_psm=6
    """
    cfg = cfg or {}
    engine = (engine or "tesseract").lower()
    kwargs = {}

    # --- DEFAULT for "simple" rules (no cfg, no ocr block) ---
    # This is exactly for cases like:
    #   { "text": "...", "rect": [x1,y1,x2,y2] }
    # with no 'ocr' entry.
    if not cfg and engine == "tesseract":
        kwargs["to_gray"] = True
        kwargs["tess_lang"] = "eng"
        kwargs["tess_oem"] = 1
        kwargs["tess_psm"] = 6
        return kwargs

    # --- pre-processing (shared) ---
    if "grayscale" in cfg:
        kwargs["to_gray"] = bool(cfg.get("grayscale"))
    if "invert" in cfg:
        kwargs["invert"] = bool(cfg.get("invert"))
    if "binarize_otsu" in cfg:
        kwargs["binarize"] = bool(cfg.get("binarize_otsu"))

    # --- Tesseract-specific ---
    if engine == "tesseract":
        kwargs["tess_lang"] = cfg.get("lang", "eng")
        kwargs["tess_oem"] = int(cfg.get("oem", 1))
        kwargs["tess_psm"] = int(cfg.get("psm", 6))

        wl = (cfg.get("whitelist") or "").strip()
        bl = (cfg.get("blacklist") or "").strip()
        if wl:
            kwargs["tess_whitelist"] = wl
        if bl:
            kwargs["tess_blacklist"] = bl

        extra = (cfg.get("extra") or "").strip()
        if extra:
            kwargs["tess_extra_config"] = extra

    # --- EasyOCR-specific ---
    elif engine == "easyocr":
        langs_raw = cfg.get("easy_langs", "en")
        if isinstance(langs_raw, str):
            langs = [s.strip() for s in langs_raw.split(",") if s.strip()]
        else:
            langs = list(langs_raw) if langs_raw else ["en"]
        if not langs:
            langs = ["en"]
        kwargs["easy_langs"] = tuple(langs)

        kwargs["easy_gpu"] = bool(cfg.get("gpu", False))

        allow = (cfg.get("allowlist") or "").strip()
        block = (cfg.get("blocklist") or "").strip()
        if allow:
            kwargs["easy_allowlist"] = allow
        if block:
            kwargs["easy_blocklist"] = block

        kwargs["easy_paragraph"] = bool(cfg.get("paragraph", False))
        if "detail" in cfg:
            kwargs["easy_detail"] = 1 if cfg.get("detail") else 0

        # If you later extend text_detect() to support text_threshold/low_text,
        # you can pass them here.

    return kwargs

def _any_word_matches(expected: str, found: str) -> bool:
    """
    True if *any* word from `expected` appears as a whole word in `found`.
    """
    if not expected or not found:
        return False

    # Split into words, ignore punctuation, drop very short words
    exp_words   = [w for w in re.findall(r"\w+", expected.lower()) if len(w) >= 3]
    found_words = set(re.findall(r"\w+", found.lower()))

    if not exp_words or not found_words:
        return False

    return any(w in found_words for w in exp_words)


# ------------------------------------------------------------
# 7. INTERACTION PRIMITIVES (Taps, Swipes, Delays)
# ------------------------------------------------------------


def random_delay(min_delay=1.0, max_delay=3.0):
    """
    Sleep for a random duration between min_delay and max_delay.

    Args:
        min_delay: Minimum sleep time in seconds.
        max_delay: Maximum sleep time in seconds.

    Returns:
        The actual delay time used.
    """
    delay_time = random.uniform(min_delay, max_delay)
    time.sleep(delay_time)
    return delay_time


# clicking helpers
# ==============================================================================
# LOW-LEVEL RAW INPUT HELPERS  (no guard — call only after guard already ran)
# ==============================================================================

def _raw_tap(device: str, x: int, y: int) -> None:
    """Send a tap via ADB WITHOUT any guard check. Only call after guard ran."""
    command = f"adb -s {device} shell input tap {x} {y}"
    try:
        subprocess.run(command, shell=True, check=True)
        print(f"[_raw_tap] ({x},{y}) on {device}")
        # Every tap in the bot funnels through here, which makes it the one place
        # worth instrumenting to get a complete click timeline.  No-op when
        # recording is off.
        record_event(device, "click", coord=f"({x},{y})", x=x, y=y,
                     page=_last_seen_page.get(device))
    except subprocess.CalledProcessError as e:
        print(f"[_raw_tap] error: {e}")
        record_event(device, "click", coord=f"({x},{y})", x=x, y=y,
                     result="adb_error", error=str(e))


def _raw_swipe(device: str, x1: int, y1: int, x2: int, y2: int,
               duration_ms: int = 800) -> None:
    """Send a swipe via ADB WITHOUT any guard check. Only call after guard ran."""
    cmd = f"adb -s {device} shell input swipe {x1} {y1} {x2} {y2} {duration_ms}"
    try:
        subprocess.run(cmd, shell=True, check=True)
        print(f"[_raw_swipe] ({x1},{y1})→({x2},{y2}) on {device}")
        record_event(device, "swipe", coord=f"({x1},{y1})->({x2},{y2})",
                     duration_ms=duration_ms, page=_last_seen_page.get(device))
    except subprocess.CalledProcessError as e:
        print(f"[_raw_swipe] error: {e}")


def _raw_keyevent(device: str, keycode: str) -> None:
    """Send a keyevent via ADB WITHOUT any guard check. Only call after guard ran."""
    cmd = f"adb -s {device} shell input keyevent {keycode}"
    try:
        subprocess.run(cmd, shell=True, check=True)
        print(f"[_raw_keyevent] {keycode} on {device}")
        record_event(device, "keyevent", keycode=str(keycode),
                     page=_last_seen_page.get(device))
    except subprocess.CalledProcessError as e:
        print(f"[_raw_keyevent] error: {e}")


# ==============================================================================
# PUBLIC INPUT HELPERS  (all guard by default)
# ==============================================================================

def tap_on_device(x, y, device, guard=None, dlog=None):
    """
    Tap a specific coordinate on the device.
    Uses guard_fix_if_signalled() — fast no-op when no guard signal is pending.
    Pass guard=_NOGUARD sentinel to skip guard (for internal use after guard ran).
    """
    if guard is _NOGUARD:
        _raw_tap(device, x, y)
        return
    if dlog is None:
        dlog = _get_device_logger(device)
    if guard is None:
        guard = _target_app_guards.get(device)
    ok = guard_fix_if_signalled(device, dlog, guard, context=f"tap({x},{y})")
    if not ok:
        raise GuardRecoveryFailed(f"[{device}] Guard failed before tap({x},{y})")
    _raw_tap(device, x, y)


# Sentinel object — passed as guard= to skip the guard check inside tap_on_device
# when click_in_bounding_box has already run guard_check_and_recover().
_NOGUARD = object()


def guard_fix_if_signalled(device: str, dlog=None, guard=None, context: str = "") -> bool:
    """
    Lightweight guard fast-path for click/sleep/wait helpers.

    Normal path (no signal): returns True immediately with zero ADB/screenshot/OCR work.
    Signal path: logs once, then calls full guard_check_and_recover() to fix the problem.

    Use instead of guard_check_and_recover() in tap_on_device, click_in_bounding_box,
    guarded_swipe, zoom_out, guarded_sleep, and when_on_page section-A polling.
    """
    if dlog is None:
        dlog = _get_device_logger(device)

    # ── Controller pause gate ────────────────────────────────────────────────
    # This runs before every tap, swipe and guarded sleep in task code, which
    # makes it the natural choke point for "stop clicking right now".  Checked
    # before the guard so no recovery is attempted against a dead network.
    if _pause_requested():
        gate = wait_while_paused(device, dlog, phase="runtime",
                                 fn="guard_fix_if_signalled", context="runtime")
        if gate == SIG_MANUAL_STOP:
            return False
        # Resumed.  Returning False aborts the current step; device_worker sees
        # the "host_pause_resumed" marker and restarts the current task from the
        # beginning instead of running a full prepare_target_app.
        dlog.info(
            f"[GUARD-FAST] [{device}] [{context}] resumed from controller pause "
            f"— aborting current step so the task restarts from the beginning"
        )
        return False

    live_guard = guard if guard is not None else _target_app_guards.get(device)

    # Fast path — no guard registered at all
    if live_guard is None:
        return True

    # Fast path — interrupt not set AND guard reports ok (both in-memory reads, no I/O)
    if not _guard_interrupt_event(device).is_set() and live_guard.check()[0] == "ok":
        return True

    # Signal exists — log once and delegate to full recovery
    dlog.info(
        f"[GUARD-FAST] [{device}] [{context}] "
        f"TargetAppGuard signalled — running full recovery"
    )
    return guard_check_and_recover(device, dlog, live_guard, context=context)


def guarded_swipe(device: str, x1: int, y1: int, x2: int, y2: int,
                  duration_ms: int = 800, guard=None, dlog=None) -> None:
    """
    Swipe with guard fast-check before the gesture.  Auto-resolves guard/dlog.
    go_up / go_down / go_up_in_box / go_down_in_box / go_left_in_box all
    route through here — so every scroll/swipe gesture is automatically guarded.
    """
    if dlog is None:
        dlog = _get_device_logger(device)
    if guard is None:
        guard = _target_app_guards.get(device)
    ok = guard_fix_if_signalled(
        device, dlog, guard,
        context=f"swipe({x1},{y1},{x2},{y2})",
    )
    if not ok:
        raise GuardRecoveryFailed(
            f"[{device}] Guard failed before swipe({x1},{y1},{x2},{y2})"
        )
    _raw_swipe(device, x1, y1, x2, y2, duration_ms)


def click_in_bounding_box(device, x1, y1, x4, y4, guard=None, dlog=None):
    """
    Tap a random point inside a given rectangle.

    Uses guard_fix_if_signalled() — fast no-op when no guard signal is pending;
    falls through to full guard_check_and_recover() only when TargetAppGuard has fired.

    Raises GuardRecoveryFailed if recovery fails.  The controller's exception
    handler treats this the same as any ADB-level exception and calls prepare_target_app.

    Args:
        device:      ADB device id.
        x1,y1,x4,y4: Rectangle bounds.
        guard:       TargetAppGuard instance (optional — auto-resolved).
        dlog:        Device logger  (optional — auto-resolved).
    """
    # ── Auto-resolve ──────────────────────────────────────────────────────────
    if dlog is None:
        dlog = _get_device_logger(device)
    if guard is None:
        guard = _target_app_guards.get(device)

    # ── Fast guard check before tap ───────────────────────────────────────────
    ok = guard_fix_if_signalled(
        device, dlog, guard,
        context=f"click({x1},{y1},{x4},{y4})",
    )
    if not ok:
        dlog.error(
            f"── click_in_bounding_box ── guard recovery FAILED before tap "
            f"({x1},{y1})→({x4},{y4}) — raising GuardRecoveryFailed"
        )
        raise GuardRecoveryFailed(
            f"[{device}] Guard recovery failed before tap ({x1},{y1}→{x4},{y4})"
        )

    random_x = random.randint(x1, x4)
    random_y = random.randint(y1, y4)
    _raw_tap(device, random_x, random_y)
    print(f"Clicked at ({random_x}, {random_y}) on device {device}.")
    return None


def go_up(device, guard=None, dlog=None):
    """
    Perform an upward gesture on the device (guarded by default).
    """
    guarded_swipe(device, 1252, 227, 1252, 727, 2000, guard=guard, dlog=dlog)
    print(f"[{device}] go_up: (1252,227) → (1252,727).")


def go_down(device, guard=None, dlog=None):
    """
    Perform a downward gesture on the device (guarded by default).
    """
    guarded_swipe(device, 1252, 727, 1252, 227, 2000, guard=guard, dlog=dlog)
    print(f"[{device}] go_down: (1252,727) → (1252,227).")

def go_up_in_box(device, x1, y1, x2, y2, duration_ms=800, guard=None, dlog=None):
    """
    Scroll up inside a bounded region (guarded).
    Finger moves top→bottom, revealing items above the current view.
    """
    rx      = random.randint(x1 + 10, x2 - 10)
    start_y = y1 + 10
    end_y   = y2 - 10
    guarded_swipe(device, rx, start_y, rx, end_y, duration_ms,
                  guard=guard, dlog=dlog)
    print(f"[{device}] go_up_in_box: ({rx},{start_y}) → ({rx},{end_y}).")


def go_down_in_box(device, x1, y1, x2, y2, duration_ms=800, guard=None, dlog=None):
    """
    Scroll down inside a bounded region (guarded).
    Finger moves bottom→top, revealing items below the current view.
    """
    rx      = random.randint(x1 + 10, x2 - 10)
    start_y = y2 - 10
    end_y   = y1 + 10
    guarded_swipe(device, rx, start_y, rx, end_y, duration_ms,
                  guard=guard, dlog=dlog)
    print(f"[{device}] go_down_in_box: ({rx},{start_y}) → ({rx},{end_y}).")

def go_left_in_box(device, x1, y1, x2, y2, duration_ms=800, guard=None, dlog=None):
    """
    Swipe left-to-right inside a bounded region (guarded).
    """
    ry      = random.randint(y1 + 10, y2 - 10)
    start_x = x1 + 10
    end_x   = x2 - 10
    guarded_swipe(device, start_x, ry, end_x, ry, duration_ms,
                  guard=guard, dlog=dlog)
    print(f"[{device}] go_left_in_box: ({start_x},{ry}) → ({end_x},{ry}).")


# Per-device cache so we only scan once per session
_input_device_cache: dict[str, str] = {}

def _find_touch_device(device: str) -> str:
    """
    Find the input event path for 'BlueStacks Virtual Touch' on this device.
    Scans /dev/input/event0–event9, caches result.
    Returns path like '/dev/input/event4', or empty string if not found.
    """
    if device in _input_device_cache:
        return _input_device_cache[device]

    out = _adb_shell(device, "getevent", "-p") or ""
    current_path = ""
    for line in out.splitlines():
        line = line.strip()
        if line.startswith("add device"):
            # e.g. "add device 4: /dev/input/event4"
            parts = line.split(":")
            if len(parts) >= 2:
                current_path = parts[-1].strip()
        elif "BlueStacks Virtual Touch" in line:
            _input_device_cache[device] = current_path
            return current_path

    return ""


def _verify_touch_device(device: str, dlog) -> bool:
    """
    Call at startup. Confirms event4 is still BlueStacks Virtual Touch.
    If not, scans and updates cache. Returns False if not found at all.
    """
    # Quick check — is event4 still correct?
    out = _adb_shell(device, "getevent", "-p") or ""
    event4_name = ""
    in_event4 = False
    for line in out.splitlines():
        line = line.strip()
        if "/dev/input/event4" in line:
            in_event4 = True
        elif in_event4 and line.startswith("name:"):
            event4_name = line.split(":", 1)[-1].strip().strip('"')
            break

    if event4_name == "BlueStacks Virtual Touch":
        _input_device_cache[device] = "/dev/input/event4"
        dlog.info(f"── touch device ── event4 confirmed as BlueStacks Virtual Touch ✓")
        return True

    # event4 shifted — scan for the right one
    dlog.warning(f"── touch device ── event4 is '{event4_name}' — scanning for BlueStacks Virtual Touch")
    path = _find_touch_device(device)
    if path:
        dlog.info(f"── touch device ── found BlueStacks Virtual Touch at {path} ✓")
        return True

    dlog.error(f"── touch device ── BlueStacks Virtual Touch not found on any event device")
    return False


def zoom_out(device, guard=None, dlog=None):
    """
    Perform a pinch-in (zoom out) gesture using sendevent (guarded).
    Guard runs before the gesture. Uses cached input device path.
    """
    if dlog is None:
        dlog = _get_device_logger(device)
    if guard is None:
        guard = _target_app_guards.get(device)
    ok = guard_fix_if_signalled(device, dlog, guard, context="zoom_out")
    if not ok:
        raise GuardRecoveryFailed(f"[{device}] Guard failed before zoom_out")

    path = _input_device_cache.get(device, "/dev/input/event4")

    cmd = (
        f"sendevent {path} 3 53 16383 && sendevent {path} 3 54 10315 && sendevent {path} 0 2 0 && "
        f"sendevent {path} 3 53 16383 && sendevent {path} 3 54 22451 && sendevent {path} 0 2 0 && "
        f"sendevent {path} 0 0 0 && "
        f"sendevent {path} 3 53 16383 && sendevent {path} 3 54 11074 && sendevent {path} 0 2 0 && "
        f"sendevent {path} 3 53 16383 && sendevent {path} 3 54 21692 && sendevent {path} 0 2 0 && "
        f"sendevent {path} 0 0 0 && "
        f"sendevent {path} 3 53 16383 && sendevent {path} 3 54 11832 && sendevent {path} 0 2 0 && "
        f"sendevent {path} 3 53 16383 && sendevent {path} 3 54 20934 && sendevent {path} 0 2 0 && "
        f"sendevent {path} 0 0 0 && "
        f"sendevent {path} 3 53 16383 && sendevent {path} 3 54 12591 && sendevent {path} 0 2 0 && "
        f"sendevent {path} 3 53 16383 && sendevent {path} 3 54 20175 && sendevent {path} 0 2 0 && "
        f"sendevent {path} 0 0 0 && "
        f"sendevent {path} 3 53 16383 && sendevent {path} 3 54 13349 && sendevent {path} 0 2 0 && "
        f"sendevent {path} 3 53 16383 && sendevent {path} 3 54 19417 && sendevent {path} 0 2 0 && "
        f"sendevent {path} 0 0 0 && "
        f"sendevent {path} 3 53 16383 && sendevent {path} 3 54 14108 && sendevent {path} 0 2 0 && "
        f"sendevent {path} 3 53 16383 && sendevent {path} 3 54 18658 && sendevent {path} 0 2 0 && "
        f"sendevent {path} 0 0 0 && "
        f"sendevent {path} 3 53 16383 && sendevent {path} 3 54 14866 && sendevent {path} 0 2 0 && "
        f"sendevent {path} 3 53 16383 && sendevent {path} 3 54 17900 && sendevent {path} 0 2 0 && "
        f"sendevent {path} 0 0 0 && "
        f"sendevent {path} 3 53 16383 && sendevent {path} 3 54 15625 && sendevent {path} 0 2 0 && "
        f"sendevent {path} 3 53 16383 && sendevent {path} 3 54 17141 && sendevent {path} 0 2 0 && "
        f"sendevent {path} 0 0 0 && "
        f"sendevent {path} 3 53 16383 && sendevent {path} 3 54 16383 && sendevent {path} 0 2 0 && "
        f"sendevent {path} 3 53 16383 && sendevent {path} 3 54 16383 && sendevent {path} 0 2 0 && "
        f"sendevent {path} 0 0 0 && "
        f"sendevent {path} 0 2 0 && sendevent {path} 0 2 0 && sendevent {path} 0 0 0"
    )
    try:
        subprocess.run(f"adb -s {device} shell \"{cmd}\"", shell=True, check=True)
        print(f"[{device}] zoom_out: pinch gesture sent")
    except subprocess.CalledProcessError as e:
        print(f"[{device}] zoom_out: failed — {e}")

# ------------------------------------------------------------
# 8. GOOGLE SHEETS & TIMING UTILS
# ------------------------------------------------------------

# ============= Sheets helpers (control + status) =============
# === Sheet layout constants ===

HEADER_ROW       = 6   # Row with headers (device name, adb port, flags, status headers, etc.)
DATA_START_ROW   = 7   # First device row (each device configuration starts here)
CONTROL_LAST_COL = 26  # Z (1-based column index) → control columns are C..Z
STATUS_FIRST_COL = CONTROL_LAST_COL + 1  # 27 → AA (first status column)
# Daily reset will clear only these columns
DAILY_RESET_CLEAR_COLS = [
    "AB", "AC", "AD", "AF", "AI", "AJ", "AK", "AL", "AM", "AN", "AO",
    "AP", "AQ", "AR", "AS", "AT", "AU", "AV", "AW", "AX", "AY", "AZ",
    "BA", "BB", "BC", "BD", "BE", "BF", "BG", "BH", "BI", "BJ", "BK", "BL",
    "BM", "BN", "BP", "BQ", "BR", "BS", "BT", "BU", "BY", "BZ",
    "CA", "CB", "CC", "CD", "CE", "CF", "CG", "CH",
]


# --- Google Sheets client / worksheet cache ---
# Cached Control sheet + its values for this run only
_CONTROL_WS = None
_CONTROL_VALUES = None
_GS_CLIENT = None


def _gs_client():
    """Return a cached gspread client so we don't re-auth on every call."""
    global _GS_CLIENT
    if _GS_CLIENT is None:
        socket.setdefaulttimeout(30)   # prevent infinite hang on stale TCP connection
        scope = [
            "https://spreadsheets.google.com/feeds",
            "https://www.googleapis.com/auth/drive",
        ]
        creds = ServiceAccountCredentials.from_json_keyfile_name(CREDS_JSON, scope)
        _GS_CLIENT = gspread.authorize(creds)
    return _GS_CLIENT

def _reset_gs_client():
    """Force gspread to re-auth on next call — call after VPN drop/reconnect."""
    global _GS_CLIENT, _CONTROL_WS, _NAMELIST_WS
    _GS_CLIENT   = None
    _CONTROL_WS  = None
    _NAMELIST_WS = None

def _get_control_ws():
    """Return a cached handle to the Control sheet (single open per run)."""
    global _CONTROL_WS
    if _CONTROL_WS is None:
        gc = _gs_client()
        _CONTROL_WS = gc.open(DOC_NAME).worksheet(CONTROL_SHEET)
    return _CONTROL_WS

_NAMELIST_WS = None

def _get_namelist_ws():
    """Return a cached handle to the namelist tab."""
    global _NAMELIST_WS
    if _NAMELIST_WS is None:
        _NAMELIST_WS = _gs_client().open(DOC_NAME).worksheet("namelist")
    return _NAMELIST_WS


def _to_bool(v):
    """
    Convert a value into a boolean, interpreting common truthy strings.

    Examples of True:
        True, "true", "1", "yes", "y", "on"  (case-insensitive)

    Args:
        v: Any value (from a sheet cell, config, etc.).

    Returns:
        True or False.
    """
    if isinstance(v, bool):
        return v
    s = str(v or "").strip().lower()
    return s in ("true", "1", "yes", "y", "on")

def _load_control_sheet(refresh_values=True):
    """
    Load the Control worksheet and (optionally) its values.

    Args:
        refresh_values: if True, re-fetch all values from the sheet.
                        if False, reuse the last cached values (if any).

    Returns:
        (ws, all_vals)
        ws       : gspread Worksheet object for CONTROL_SHEET.
        all_vals : list-of-lists with the full grid values
                   (may be None if refresh_values=False and nothing cached yet).
    """
    global _CONTROL_WS, _CONTROL_VALUES

    # 1) Ensure we have the worksheet object cached
    if _CONTROL_WS is None:
        gc = _gs_client()
        _CONTROL_WS = gc.open(DOC_NAME).worksheet(CONTROL_SHEET)

    # 2) Optionally refresh values
    if refresh_values or _CONTROL_VALUES is None:
        try:
            _CONTROL_VALUES = _CONTROL_WS.get_all_values()
        except Exception:
            # stale connection — reset client and retry once
            _reset_gs_client()
            gc = _gs_client()
            _CONTROL_WS = gc.open(DOC_NAME).worksheet(CONTROL_SHEET)
            _CONTROL_VALUES = _CONTROL_WS.get_all_values()

    return _CONTROL_WS, _CONTROL_VALUES

def _col_index_to_a1(col_idx):
    """
    Convert a 1-based column index to an A1-style column label.

    Examples:
        1  -> "A"
        26 -> "Z"
        27 -> "AA"
        28 -> "AB"

    Args:
        col_idx: 1-based column index (int).

    Returns:
        Column label as a string.
    """
    s = ""
    while col_idx:
        col_idx, rem = divmod(col_idx - 1, 26)
        s = chr(65 + rem) + s
    return s

def apply_checkbox_validation(ws, start_row, end_row):
    """
    Apply Google Sheets 'Boolean' (checkbox) data validation to C..Z
    for the given row range.

    Args:
        ws        : gspread Worksheet object (the 'Control' sheet).
        start_row : First row (1-based) to validate, inclusive.
        end_row   : Last row (1-based) to validate, inclusive.

    Effect:
        - Adds a BOOLEAN data validation rule over:
            rows:    start_row .. end_row
            columns: C..Z (i.e., index 2..25, end index 26 is exclusive)
        - This makes those cells act as checkboxes in the UI.
    """
    sheet_id = ws._properties["sheetId"]

    req = {
        "setDataValidation": {
            "range": {
                "sheetId": sheet_id,
                # Row indices in API are 0-based and end-exclusive
                "startRowIndex": start_row - 1,  # inclusive
                "endRowIndex": end_row,          # exclusive
                # Column indices are 0-based and end-exclusive
                "startColumnIndex": 2,           # C = 2 (0-based)
                "endColumnIndex": CONTROL_LAST_COL,  # 26 → covers C..Z (exclusive)
            },
            "rule": {
                "condition": {"type": "BOOLEAN"},
                "strict": True,
                "showCustomUi": True,
            },
        }
    }

    # Apply the validation rule using the Sheets batchUpdate API through gspread
    ws.spreadsheet.batch_update({"requests": [req]})

# --- OCR/status helpers ---


# Cache: maps header_name → column index, per worksheet id
_STATUS_COL_CACHE = {}   # { (sheet_id, header_name): col_idx }
_DEVICE_ROW_CACHE: dict = {}  # { device_id.lower(): row_index } — populated by read_control_config

def _find_or_create_status_col(ws, header_name, start_col_idx=None):
    if start_col_idx is None:
        start_col_idx = STATUS_FIRST_COL

    # NEW: check cache first — avoids a row_values API call per update_status() call
    sheet_id = ws._properties.get("sheetId", id(ws))
    cache_key = (sheet_id, header_name.strip().lower())
    if cache_key in _STATUS_COL_CACHE:
        return _STATUS_COL_CACHE[cache_key]

    row = _sheets_call(ws.row_values, HEADER_ROW)
    while len(row) < start_col_idx - 1:
        row.append("")

    for j, val in enumerate(row, start=1):
        if j >= start_col_idx and str(val).strip().lower() == header_name.strip().lower():
            _STATUS_COL_CACHE[cache_key] = j   # cache it
            return j

    j = max(start_col_idx, len(row) + 1)
    _sheets_call(ws.update_acell, f"{_col_index_to_a1(j)}{HEADER_ROW}", header_name)
    _STATUS_COL_CACHE[cache_key] = j   # cache it
    return j

def maybe_refresh_devices_from_conf(ws, all_vals, uncheck_trigger=True):
    """
    Smart-sync bluestacks.conf → control sheet.

    Behaviour:
      • Devices already present (matched by adb_id in col B) are left untouched.
      • If only the friendly name in col A differs, that single cell is updated.
      • Devices not yet in the sheet are appended AFTER the last existing row.
      • No rows are ever cleared or reset.
      • Display names are read from bluestacks_config.conf (same directory as
        bluestacks.conf). Falls back to bluestacks.conf names if unavailable.

    Args:
        ws             : Control worksheet.
        all_vals       : Full sheet snapshot (list of lists).
        uncheck_trigger: If True, check B3 first and reset it to FALSE after sync.
                         Pass False to call directly from the controller UI.

    Returns:
        dict with keys:
            triggered    (bool)   – False when B3 was unchecked and we did nothing
            added        (list)   – [{"adb_id": ..., "name": ...}, ...]
            name_updated (list)   – [{"adb_id": ..., "old_name": ..., "new_name": ...}, ...]
            unchanged    (int)    – devices that needed no change
            total        (int)    – total device rows in sheet after sync
    """
    _EMPTY = {"triggered": False, "added": [], "name_updated": [], "unchanged": 0, "total": 0}

    # ── B3 trigger check (only in trigger mode) ───────────────────────────────
    if uncheck_trigger:
        b3_raw = ""
        if len(all_vals) >= 3:
            row3 = all_vals[2]          # 0-based index for row 3
            if len(row3) >= 2:
                b3_raw = row3[1]
        if not _to_bool(b3_raw):
            return _EMPTY

    # ── Parse ports + fallback names from bluestacks.conf ────────────────────
    conf_devices = parse_bluestacks_conf(BLUESTACKS_CONF)
    if not conf_devices:
        print("[maybe_refresh_devices_from_conf] No BlueStacks instances found in conf.")
        if uncheck_trigger:
            _sheets_call(ws.update_acell, "B3", False)
        return {"triggered": True, "added": [], "name_updated": [], "unchanged": 0, "total": 0}

    # ── Override display names from bluestacks_config.conf ───────────────────
    try:
        _config_path = os.path.join(os.path.dirname(BLUESTACKS_CONF), "bluestacks_config.conf")
        with open(_config_path, "r", encoding="utf-8", errors="ignore") as _f:
            _cfg_text = _f.read()
        _name_re = re.compile(
            r'bst\.instance\.(?P<inst>[^.]+)\.display_name="(?P<n>[^"]+)"'
        )
        _config_names = {m["inst"]: m["n"] for m in _name_re.finditer(_cfg_text)}
        for d in conf_devices:
            if d["instance"] in _config_names:
                d["name"] = _config_names[d["instance"]]
        print(f"[maybe_refresh_devices_from_conf] loaded {len(_config_names)} name(s) "
              f"from bluestacks_config.conf")
    except Exception as _e:
        print(f"[maybe_refresh_devices_from_conf] bluestacks_config.conf read failed "
              f"(falling back to bluestacks.conf names): {_e}")

    # ── Read existing sheet rows ───────────────────────────────────────────────
    # Build:  existing_map[adb_id] = {"row_num": <1-based int>, "name": <str>}
    data_start_idx = DATA_START_ROW - 1   # 0-based into all_vals
    existing_map: dict[str, dict] = {}
    last_data_row = DATA_START_ROW - 1    # 1-based, tracks the last populated row

    for offset, r in enumerate(all_vals[data_start_idx:]):
        row_num   = DATA_START_ROW + offset          # 1-based sheet row
        name_cell = r[0].strip() if len(r) > 0 else ""
        adb_cell  = r[1].strip() if len(r) > 1 else ""

        if not name_cell and not adb_cell:
            continue                                 # blank row — skip

        last_data_row = row_num

        # Derive the canonical adb_id for this row
        if adb_cell:
            adb_id = adb_cell
        elif ":" in name_cell:
            adb_id = name_cell
        else:
            continue                                 # can't identify device — skip

        existing_map[adb_id] = {"row_num": row_num, "name": name_cell}

    # ── Compare conf devices against existing sheet rows ──────────────────────
    added:        list[dict] = []
    name_updated: list[dict] = []
    unchanged                = 0
    new_rows:     list[list] = []   # rows to batch-append

    for d in conf_devices:
        adb_id   = f"localhost:{d['port']}"
        if adb_id == "localhost:5555":
            continue                                 # always skip reserved port

        friendly = (d.get("name") or "").strip() or adb_id

        if adb_id in existing_map:
            existing_name = existing_map[adb_id]["name"]
            if existing_name != friendly:
                # Update only the name cell (col A) for this row
                row_num = existing_map[adb_id]["row_num"]
                _sheets_call(ws.update_acell, f"A{row_num}", friendly)
                name_updated.append({
                    "adb_id":   adb_id,
                    "old_name": existing_name,
                    "new_name": friendly,
                })
                print(f"[maybe_refresh_devices_from_conf] name updated row {row_num}: "
                      f"{existing_name!r} → {friendly!r}")
            else:
                unchanged += 1
        else:
            # New device — collect for a single batch write
            defaults = [False] * (CONTROL_LAST_COL - 2)   # C..Z
            new_rows.append([friendly, adb_id] + defaults)
            added.append({"adb_id": adb_id, "name": friendly})

    # ── Batch-append new rows after the last existing row ─────────────────────
    if new_rows:
        start_row        = last_data_row + 1
        end_row          = start_row + len(new_rows) - 1
        last_ctrl_letter = _col_index_to_a1(CONTROL_LAST_COL)
        _sheets_call(ws.update,
                     values=new_rows,
                     range_name=f"A{start_row}:{last_ctrl_letter}{end_row}",
                     value_input_option="USER_ENTERED")
        apply_checkbox_validation(ws, start_row, end_row)
        print(f"[maybe_refresh_devices_from_conf] appended {len(new_rows)} new row(s) "
              f"starting at row {start_row}.")

    total = len(existing_map) + len(added)

    # ── Reset trigger checkbox ────────────────────────────────────────────────
    if uncheck_trigger:
        _sheets_call(ws.update_acell, "B3", False)

    print(f"[maybe_refresh_devices_from_conf] done — "
          f"{len(added)} added, {len(name_updated)} names updated, "
          f"{unchanged} unchanged. Total: {total}")

    return {
        "triggered":    True,
        "added":        added,
        "name_updated": name_updated,
        "unchanged":    unchanged,
        "total":        total,
    }

def read_control_config(ws=None, all_vals=None):
    if ws is None or all_vals is None:
        ws, all_vals = _load_control_sheet(refresh_values=False)

    run_all = False
    start_from_raw = ""

    if len(all_vals) >= 1:
        row1 = all_vals[0]
        if len(row1) >= 2:
            run_all = _to_bool(row1[1])

    if len(all_vals) >= 2:
        row2 = all_vals[1]
        if len(row2) >= 2:
            start_from_raw = (row2[1] or "").strip()

    # TekkmanMissions, redeem codes and the namelist tab were read here purely to
    # feed tekkman / redeem / change_name. Those tasks are gone and nothing else
    # consumed them, so the three sheet reads go too — that is three fewer API
    # round-trips on every startup.

    header_row = all_vals[HEADER_ROW - 1] if len(all_vals) >= HEADER_ROW else []

    def _find_col(label, default=None):
        for idx, val in enumerate(header_row, start=1):
            if str(val).strip() == label:
                return idx
        return default

    col_device        = _find_col("Device",       1)
    col_adb           = _find_col("Adb port",     2)
    col_run_d         = _find_col("RunDailies",   None)
    col_dev_type      = _find_col("DeviceType",   None)
    col_vip_collect   = _find_col("VipCollect",   None)

    rows = []
    data_start_idx = DATA_START_ROW - 1

    for offset, r in enumerate(all_vals[data_start_idx:], start=0):
        row_index = DATA_START_ROW + offset

        name = (r[col_device - 1] if len(r) >= col_device else "").strip()
        adb  = (r[col_adb - 1]    if len(r) >= col_adb    else "").strip()

        if not name and not adb:
            continue

        if adb:
            dev_id = adb
        elif ":" in name:
            dev_id = name
        else:
            dev_id = None

        if not dev_id:
            continue

        run_dailies = False
        if col_run_d is not None and len(r) >= col_run_d:
            run_dailies = _to_bool(r[col_run_d - 1])

        device_type = ""
        if col_dev_type is not None and len(r) >= col_dev_type:
            device_type = str(r[col_dev_type - 1]).strip()

        vip_collect_status = ""
        if col_vip_collect is not None and len(r) >= col_vip_collect:
            vip_collect_status = str(r[col_vip_collect - 1]).strip().lower()

        rows.append({
            "device_id":            dev_id,
            "friendly":             name if name else dev_id,
            "run_dailies":          run_dailies,
            "device_type":          device_type,
            "row_index":            row_index,
            # Only live task statuses are parsed. Columns for deleted tasks may
            # still exist in the spreadsheet; they are simply never read.
            "vip_collect_status":   vip_collect_status,
        })

    start_from = None
    if start_from_raw:
        if ":" in start_from_raw:
            start_from = start_from_raw
        else:
            for row in rows:
                if row["friendly"] == start_from_raw:
                    start_from = row["device_id"]
                    break

    # Populate device-row cache so flush_status needs no read calls
    global _DEVICE_ROW_CACHE
    for _r in rows:
        _did = (_r.get("device_id") or "").strip().lower()
        _ri  = _r.get("row_index")
        if _did and _ri:
            _DEVICE_ROW_CACHE[_did] = _ri
            # also index by friendly name
            _fn = (_r.get("friendly") or "").strip().lower()
            if _fn:
                _DEVICE_ROW_CACHE[_fn] = _ri

    return {
            "run_all":          run_all,
            "start_from":       start_from,
            "rows":             rows,
            "run_d_col":        col_run_d,
            "available_version": _read_available_version_f2(),
            "device_row_cache": dict(_DEVICE_ROW_CACHE),
        }

def _read_available_version_f2() -> str:
    """
    Read cell F2 (available TargetApp version) from the Control sheet.
    Called exactly once during read_control_config at startup.
    Updates the module-level _available_version global.
    Returns the version string, or "" on failure.
    """
    global _available_version
    try:
        ws  = _get_control_ws()
        val = _sheets_call(ws.acell, "F2").value
        ver = str(val).strip() if val else ""
        logging.info(f"_read_available_version_f2 ── F2={ver!r}")
        _available_version = ver
        return ver
    except Exception as exc:
        logging.warning(f"_read_available_version_f2 ── failed to read F2: {exc}")
        return ""

def _sheets_call(func, *args, max_retries=6, base_wait=2, **kwargs):
    """
    Call a gspread API function with exponential backoff on rate-limit/timeout.

    Handles:
        - 429 RESOURCE_EXHAUSTED  (quota hit)
        - 503 Service Unavailable (transient Google outage)
        - HTTPSConnectionPool / ReadTimeout (network timeout under load)

    Args:
        func       : gspread method to call (e.g. ws.update_acell)
        *args      : positional args for func
        max_retries: total retries before giving up (default 6 → max wait ~2min)
        base_wait  : starting wait seconds, doubles each attempt (default 2)
        **kwargs   : keyword args for func

    Returns:
        Whatever func returns, or raises the last exception after all retries.
    """
    import time as _time
    last_exc = None
    for attempt in range(max_retries + 1):
        try:
            return func(*args, **kwargs)
        except Exception as e:
            last_exc = e
            # Decide whether this is retryable
            err_str = str(e).lower()
            status  = getattr(getattr(e, "response", None), "status_code", None)
            retryable = (
                status in (429, 500, 503)
                or "rate" in err_str
                or "quota" in err_str
                or "connectionpool" in err_str
                or "timeout" in err_str
                or "connection aborted" in err_str
                or "connection reset" in err_str
                or "unavailable" in err_str
            )
            if not retryable or attempt == max_retries:
                raise
            wait = base_wait * (2 ** attempt)
            print(f"[Sheets] Retryable error on attempt {attempt + 1}/{max_retries}: "
                  f"{type(e).__name__} — waiting {wait}s")
            _time.sleep(wait)
    raise last_exc

# Buffer: { device_id_or_name: { header_name: value } }
_PENDING_STATUS = {}   # type: dict[str, dict[str, str]]

def update_status(device_name_or_id, header_name, status_value):
    """
    Buffer a status update for this device. No Sheets API call happens here.
    The actual write is done in flush_status() at the end of the device's run.
    Logging still fires immediately so the log tells you what happened.
    """
    key = (device_name_or_id or "").strip()
    if not key:
        logging.warning("update_status called with empty device id — ignored")
        return
    if key not in _PENDING_STATUS:
        _PENDING_STATUS[key] = {}
    _PENDING_STATUS[key][header_name] = str(status_value)
    # Log immediately so the per-device log is complete even before the flush
    _get_device_logger(key).debug(f"── update_status ── queued {header_name}: {status_value}")
    print(f"[{key}] Status queued → {header_name}: {status_value}")


def flush_status(device_name_or_id):
    """
    Write all buffered status updates for a device to Google Sheets in one batch.
    Call this once at the end of perform_actions_for_device() (in the finally block).

    API calls made (normal path):
        - ws.batch_update × 1   (device row found in _DEVICE_ROW_CACHE)

    Fallback if row not cached:
        - ws.col_values  × 2   (A and B, to find the device row)
        - ws.batch_update × 1
    """
    key = (device_name_or_id or "").strip()
    updates = _PENDING_STATUS.pop(key, {})
    if not updates:
        _get_device_logger(key).debug("── flush_status ── nothing to write")
        return

    dlog = _get_device_logger(key)
    dlog.info(f"── flush_status ── Writing {len(updates)} status field(s) to Sheets")
    with _sheets_lock:
        try:
            ws = _get_control_ws()
            status_start_col = STATUS_FIRST_COL

            # ── Find device row — prefer cache (no API read needed) ────────────
            device_row = _DEVICE_ROW_CACHE.get(key.lower())
            if device_row is None:
                dlog.debug("── flush_status ── row not in cache — falling back to col_values")
                colA = _sheets_call(ws.col_values, 1)
                colB = _sheets_call(ws.col_values, 2)
                last_row = max(len(colA), len(colB))
                target   = key.lower()
                for row in range(DATA_START_ROW, last_row + 1):
                    a = (colA[row - 1] if row - 1 < len(colA) else "").strip().lower()
                    b = (colB[row - 1] if row - 1 < len(colB) else "").strip().lower()
                    if target == a or target == b:
                        device_row = row
                        _DEVICE_ROW_CACHE[target] = row   # cache for future calls
                        break

            if device_row is None:
                dlog.warning(f"── flush_status ── No sheet row found for '{key}' — updates lost")
                print(f"[flush_status] No sheet row found for '{key}'")
                return

            # Build batch payload — _find_or_create_status_col is cached so cheap
            batch_data = []
            for header_name, status_value in updates.items():
                col_idx = _find_or_create_status_col(ws, header_name, start_col_idx=status_start_col)
                a1 = f"{_col_index_to_a1(col_idx)}{device_row}"
                batch_data.append({"range": a1, "values": [[status_value]]})
                dlog.info(f"── flush_status ── {header_name} = {status_value!r} → {a1}")

            # Single API call to write everything
            _sheets_call(ws.batch_update, batch_data, value_input_option="USER_ENTERED")
            dlog.info(f"── flush_status ── Done ({len(batch_data)} cell(s) written)")
            print(f"[{key}] flush_status: wrote {len(batch_data)} cell(s)")

        except Exception as e:
            dlog.error(f"── flush_status ── Failed: {type(e).__name__}: {e}")
            print(f"[flush_status] Error writing for '{key}': {e}")

# --- DROP-IN REPLACEMENTS (put with your other sheet helpers) ---

_CLOCKS = {}  # { (device, label): t0 }

def start_clock(device: str, label: str = "default") -> None:
    _CLOCKS[(device, label)] = time.perf_counter()

def stop_clock(device: str, label: str = "default", clear: bool = True) -> float:
    t0 = _CLOCKS.get((device, label))
    if t0 is None:
        return 0.0
    elapsed = time.perf_counter() - t0
    if clear:
        _CLOCKS.pop((device, label), None)
    return elapsed


def _parse_ts(s: str):
    """
    Parse a timestamp string into a datetime (or return None).

    Supports:
        - ISO format:       'YYYY-MM-DDTHH:MM:SS' (and variants accepted by fromisoformat)
        - Legacy formats:   'YYYY-MM-DD HH:MM:SS'
                            'YYYY/MM/DD HH:MM:SS'

    Args:
        s: Raw timestamp string (e.g. what you read from F1).

    Returns:
        datetime instance if parsing succeeds, or None if s is empty or unparseable.
    """
    if not s:
        return None
    s = s.strip()

    # 1st try: Python's fromisoformat (handles a bunch of variants)
    try:
        return _dt.datetime.fromisoformat(s)
    except Exception:
        # 2nd try: a couple of explicit formats used in this script
        for fmt in ("%Y-%m-%d %H:%M:%S", "%Y/%m/%d %H:%M:%S"):
            try:
                return _dt.datetime.strptime(s, fmt)
            except Exception:
                pass
    # Give up → treat as no timestamp
    return None


def _latest_cutoff_leq(now: _dt.datetime):
    """
    Compute the most recent daily cutoff time (13:30) that is <= 'now'.

    Rules:
        - If current time-of-day is >= 13:30:
            → return today @ 13:30
        - Else:
            → return yesterday @ 13:30
    """
    cutoff_time = _dt.time(13, 30)

    if now.time() >= cutoff_time:
        # Same-day cutoff at 13:30
        return now.replace(hour=13, minute=30, second=0, microsecond=0)

    # Otherwise we haven't reached today's cutoff yet → use yesterday's cutoff
    yest = (now - _dt.timedelta(days=1)).date()
    return _dt.datetime.combine(yest, cutoff_time)


def should_refresh_daily(last_refresh: _dt.datetime | None, now: _dt.datetime) -> bool:
    """
    Decide whether we should do a 'daily refresh' based on last_refresh and now.

    Logic:
        - If we never refreshed before (last_refresh is None) → True.
        - Else:
            * Compute latest_cutoff = _latest_cutoff_leq(now).
            * Refresh if last_refresh < latest_cutoff.

    In other words:
        "Has there been a refresh since the most recent 13:30
         that is not in the future?"
    """
    if last_refresh is None:
        return True

    latest_cutoff = _latest_cutoff_leq(now)
    return last_refresh < latest_cutoff


def _clear_status_values(ws):
    """
    Clear only the columns listed in DAILY_RESET_CLEAR_COLS
    for all device rows.
    """
    ranges = []
    for col in DAILY_RESET_CLEAR_COLS:
        col = str(col).strip().upper()
        if not col:
            continue
        ranges.append(f"{col}{DATA_START_ROW}:{col}{ws.row_count}")

    if ranges:
        ws.batch_clear(ranges)

def maybe_refresh_daily_statuses(ws, all_vals):
    """
    If needed, clear status columns and stamp F1 with the refresh time.

    Uses:
        - ws       : Control worksheet.
        - all_vals : full sheet values (from _load_control_sheet).

    Behavior:
        - Ensures E1 = "Last Refresh" (label).
        - Reads F1 from the in-memory all_vals snapshot.
        - Uses should_refresh_daily() to decide if a refresh is needed.
        - If refresh is needed:
            * Clears all status columns via _clear_status_values(ws).
            * Writes new timestamp to F1.
    """
    now = _dt.datetime.now()

    last_refresh_raw = ""
    if len(all_vals) >= 1:
        row0 = all_vals[0]
        if len(row0) >= 6:
            last_refresh_raw = (row0[5] or "").strip()

    last_refresh = _parse_ts(last_refresh_raw)

    if should_refresh_daily(last_refresh, now):
        _clear_status_values(ws)          # FIX: removed misleading "if you want" comment
        stamp = now.strftime("%Y-%m-%d %H:%M:%S")
        _sheets_call(ws.update_acell, "F1", stamp)
        print("[Sheet] Daily status refresh: done.")
        return True
    else:
        print("[Sheet] Daily status refresh: not needed right now.")
        return False


# ------------------------------------------------------------
# 9. PAGE DETECTION, NAVIGATION & STATE
# ------------------------------------------------------------


_PAGES_CACHE = None

def load_pages_config(path: str = PAGES_JSON, force_reload: bool = False) -> dict:
    """
    Load pages.json (new array format) and return a dict keyed by page name.
    """
    global _PAGES_CACHE
    if _PAGES_CACHE is not None and not force_reload:
        return _PAGES_CACHE

    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
    except Exception as e:
        logging.error(f"Failed to load pages config from {path}: {e}")
        _PAGES_CACHE = {}
        return {}

    result = {}
    if isinstance(data, list):
        for entry in data:
            if isinstance(entry, dict):
                name = entry.get("page", "").strip()
                if name:
                    result[name] = entry
    elif isinstance(data, dict):
        result = data  # legacy fallback

    _PAGES_CACHE = result
    return result


#start workflow functions

def press_back(device: str, times: int = 1, *page_names: str, delay: float = 1.0):
    """
    Unified Back function.

    Usage:
      1. Simple: press_back(device)
         -> Presses back once. (Acts like the old back() function).
      
      2. Multi-tap: press_back(device, 3)
         -> Presses back 3 times.
      
      3. Smart Navigation: press_back(device, 5, "home", "main_menu")
         -> Presses back up to 5 times, stopping early if "home" or "main_menu" is detected.

    Returns:
        The name of the matched page (str) if found, otherwise None.
    """
    for i in range(times):
        # --- 1. The Physical Action (The "Muscle") ---
        try:
            subprocess.run(
                ["adb", "-s", device, "shell", "input", "keyevent", "4"],
                check=True,
                capture_output=True,
                text=True,
            )
            print(f"[{device}] BACK keyevent sent ({i+1}/{times}).")
        except subprocess.CalledProcessError as e:
            print(f"[{device}] Failed to send BACK keyevent: {e}")

        # --- 2. The Logic (The "Brain") ---
        # If we have targets or are pressing multiple times, we need a delay.
        # If it's a simple single press, we still sleep by default for safety, 
        # but you can set delay=0 to skip it.
        time.sleep(delay)

        # Check if we landed on a desired page
        for name in page_names:
            # We use a try-except here just in case is_on_page isn't defined yet
            try:
                if is_on_page(device, name):
                    print(f"[{device}] Landed on '{name}' after back press.")
                    return name
            except NameError:
                pass # is_on_page might not be imported/defined, ignore

    return None

# ---- SIMPLE PER-DEVICE CHECKPOINTS ----
CHECKPOINTS: dict[str, dict[str, object]] = {}

def set_checkpoint(device: str, key: str, value: object) -> None:
    """
    Store a per-device checkpoint, e.g.:

        set_checkpoint(device, "vpn_stage", VPN_STAGE_INTRO_DONE)
    """
    dev_cp = CHECKPOINTS.setdefault(device, {})
    old = dev_cp.get(key)
    dev_cp[key] = value
    _get_device_logger(device).info(f"── set_checkpoint ── [{key}] {old!r} -> {value!r}")


def get_checkpoint(device: str, key: str, default: object = None) -> object:
    """
    Read a per-device checkpoint, returning default if not set.
    """
    return CHECKPOINTS.get(device, {}).get(key, default)



# ── module-level store: device → active PageMonitor ──────────────────────────

def _fuzzy_text_match(expected: str, found: str, threshold: float = 0.80) -> bool:
    expected = expected.lower().strip()
    found    = found.lower().strip()
    if not expected:
        return True
    ratio = SequenceMatcher(None, expected, found).ratio()
    return ratio >= threshold


def _score_regions_pixels(img_array, regions, tolerance=10):
    """
    Check pixel_grid of each region against img_array (RGB numpy H×W×3).
    Returns (score 0.0-1.0, matched_pixels, total_pixels).
    """
    ih, iw = img_array.shape[:2]
    total = 0
    matched = 0
    for region in regions:
        grid = region.get("pixel_grid")
        if not grid:
            continue
        x   = region.get("x", 0)
        y   = region.get("y", 0)
        w   = region.get("w", region.get("width", 1))
        h   = region.get("h", region.get("height", 1))
        step_x = max(1, math.ceil(w / 40))
        step_y = max(1, math.ceil(h / 40))
        for row_idx, row in enumerate(grid):
            py = y + row_idx * step_y
            if py >= ih:
                continue
            for col_idx, ref in enumerate(row):
                px = x + col_idx * step_x
                if px >= iw:
                    continue
                if not (isinstance(ref, (list, tuple)) and len(ref) == 3):
                    continue
                total += 1
                live = img_array[py, px]
                if (abs(int(live[0]) - ref[0]) <= tolerance and
                        abs(int(live[1]) - ref[1]) <= tolerance and
                        abs(int(live[2]) - ref[2]) <= tolerance):
                    matched += 1
    score = (matched / total) if total > 0 else 0.0
    return score, matched, total


def is_on_page(
    device: str,
    page_name: str,
    require_all_texts: bool = False,
    image: Image.Image | None = None,
    threshold: float = 0.60,              # ← NEW
) -> bool:
    """
    Return True if the device screen matches `page_name` from pages.json.

    Uses pixel_grid regions and OCR text checks with fuzzy matching.
    Combined score >= threshold means a match (default 0.60).
    """
    dlog = _get_device_logger(device)
    pages = load_pages_config()
    page_spec = pages.get(page_name)
    if not page_spec:
        dlog.debug(f"── is_on_page ── [{page_name}] no spec found")
        return False

    screenshot = image if image is not None else get_screenshot(device)
    if screenshot is None:
        dlog.warning(f"── is_on_page ── [{page_name}] screenshot failed")
        return False

    img_array = np.array(screenshot.convert("RGB"))

    regions = page_spec.get("regions", [])
    texts   = page_spec.get("texts", [])

    has_pixels = bool(regions)
    has_texts  = bool(texts)

    pixel_score = 0.0
    if has_pixels:
        pixel_score, px_matched, px_total = _score_regions_pixels(img_array, regions)
        dlog.debug(
            f"── is_on_page ── [{page_name}] pixel: {px_matched}/{px_total} = {pixel_score:.3f}"
        )

    text_score = 0.0
    if has_texts:
        text_matched = 0
        text_total   = 0
        for t_spec in texts:
            expected = (t_spec.get("text") or "").strip()
            rect     = t_spec.get("rect")
            required = bool(t_spec.get("required"))

            if not expected:
                continue
            if not rect or len(rect) != 4:
                tx = t_spec.get("x")
                ty = t_spec.get("y")
                tw = t_spec.get("w")
                th = t_spec.get("h")
                if tx is not None and ty is not None and tw is not None and th is not None:
                    rect = [tx, ty, tx + tw, ty + th]
                else:
                    continue

            x1, y1, x2, y2 = rect
            text_total += 1

            try:
                crop = screenshot.crop((x1, y1, x2, y2)).convert("L")
                crop_np = np.array(crop)
                _, binarized = cv2.threshold(crop_np, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
                binarized_img = Image.fromarray(binarized)
                ocr_text = pytesseract.image_to_string(
                    binarized_img, config="--oem 1 --psm 6"
                ).strip()
            except Exception as e:
                dlog.debug(f"── is_on_page ── [{page_name}] OCR error for rect {rect}: {e}")
                ocr_text = ""

            matched = _fuzzy_text_match(expected, ocr_text, threshold=0.80)

            dlog.debug(
                f"── is_on_page ── [{page_name}] text rect={rect} required={required} "
                f"expected='{expected}' found='{ocr_text}' match={matched}"
            )

            if matched:
                text_matched += 1
            elif required:
                dlog.debug(f"── is_on_page ── [{page_name}] required text FAILED → score=0")
                return False

        text_score = (text_matched / text_total) if text_total > 0 else 0.0
        has_texts = text_total > 0

    if has_pixels and has_texts:
        if pixel_score < 0.10:
            final = pixel_score * 0.30 + text_score * 0.70 * (pixel_score / 0.10)
        else:
            final = pixel_score * 0.30 + text_score * 0.70
    elif has_texts:
        final = text_score
    elif has_pixels:
        final = pixel_score
    else:
        final = 0.0

    ok = final >= threshold                # ← CHANGED (was hardcoded 0.60)
    dlog.info(
        f"── is_on_page ── [{page_name}]: pixel={pixel_score:.3f} text={text_score:.3f} "
        f"final={final:.3f} threshold={threshold:.2f} → {'MATCH' if ok else 'no match'}"
    )
    # Only POSITIVE detections are recorded.  Logging every negative check would
    # bury the timeline: a single dispatch loop tests a dozen pages per frame.
    if ok:
        record_event(device, "page_seen", page=page_name, source="is_on_page",
                     score=round(final, 3), threshold=round(threshold, 2))
    return ok

def when_on_page(device: str,
                 target_pages,
                 timeout: float = 30.0,
                 check_interval: float = 0.5,
                 safety_interval: float = 10.0,
                 retry_callback=None,
                 save_on_timeout: bool = True,
                 guard=None,
                 dlog=None):
    """
    Waits for ANY of the given pages to appear using PARALLEL processing.

    Guard runs at the top of every poll iteration (≤ 1s cadence) and
    immediately on any screenshot failure.  Guard is auto-resolved from
    _target_app_guards[device] when not provided, so all callers get protection
    even without an explicit guard= argument.

    Returns the matched page name, or None on timeout / guard failure / error.
    If timeout occurs and save_on_timeout is True, saves a screenshot.
    """
    if isinstance(target_pages, str):
        target_pages = [target_pages]

    if not target_pages:
        _get_device_logger(device).warning("── when_on_page ── called with empty target_pages")
        return None

    _dlog          = dlog if dlog is not None else _get_device_logger(device)
    _guard         = guard if guard is not None else _target_app_guards.get(device)
    expecting_home = "device main page" in target_pages

    os.makedirs(UNEXPECTED_PAGES_DIR, exist_ok=True)

    t0                = time.time()
    last_safety_check = t0
    last_guard_check  = t0   # guard runs every ≤ 1.0s

    _dlog.info(f"Waiting up to {timeout}s for: {target_pages}")
    print(f"[{device}] Waiting up to {timeout}s for: {target_pages} (Parallel Check)")

    max_workers = max(1, min(20, len(target_pages)))

    with ThreadPoolExecutor(max_workers=max_workers) as pool:

        while time.time() - t0 < timeout:
            now = time.time()

            # ── A. GUARD FAST-CHECK (every ≤ 1.0s — in-memory only on normal path) ──
            if now - last_guard_check >= 1.0 or _guard_interrupt_event(device).is_set():
                last_guard_check = now
                ok = guard_fix_if_signalled(
                    device, _dlog, _guard,
                    context=f"when_on_page({target_pages[0]!r})",
                )
                if not ok:
                    _dlog.warning(
                        f"── when_on_page ── [{', '.join(target_pages)}] "
                        f"guard recovery failed — exiting"
                    )
                    return None
                # Re-resolve live guard in case prepare_target_app created a new one
                _guard = _target_app_guards.get(device) or guard

            # ── B. SAFETY CHECK (every safety_interval seconds) ──────────────
            if now - last_safety_check >= safety_interval:
                last_safety_check = now

                if not _adb_ping(device):
                    # Section A no longer runs ADB recovery, so do it explicitly here.
                    _dlog.critical(
                        f"[{device}] CRITICAL: Device offline during safety check "
                        f"— running full guard recovery."
                    )
                    print(f"[{device}] CRITICAL: Device offline — running full guard recovery.")
                    ok = guard_check_and_recover(
                        device, _dlog, _guard,
                        context="when_on_page/safety_adb_ping_failed",
                    )
                    if not ok:
                        return None
                    _guard = _target_app_guards.get(device) or guard
                    continue

                safety_img = get_screenshot(device)
                if safety_img is not None:
                    if not expecting_home and is_on_page(device, "device main page", image=safety_img):
                        msg = "Crashed to Home screen — triggering callback."
                        print(f"[{device}] CRITICAL: {msg}")
                        _dlog.critical(msg)
                        if retry_callback:
                            return retry_callback(device)
                        return None

            # ── C. PARALLEL PAGE CHECK ────────────────────────────────────────
            try:
                img = get_screenshot(device)
                if img is None:
                    _dlog.warning(
                        "── when_on_page ── screenshot returned None — "
                        "calling guard_check_and_recover immediately"
                    )
                    ok = guard_check_and_recover(
                        device, _dlog, _guard,
                        context="when_on_page/screenshot_none",
                    )
                    if not ok:
                        return None
                    last_guard_check = time.time()
                    _guard = _target_app_guards.get(device) or guard
                    time.sleep(0.3)
                    continue

                future_to_page = {
                    pool.submit(is_on_page, device, page, False, img): page
                    for page in target_pages
                }

                try:
                    for future in as_completed(future_to_page, timeout=5.0):
                        page_name = future_to_page[future]
                        if future.result():
                            _dlog.info(f"Found target page: '{page_name}'")
                            print(f"[{device}] Found target page: '{page_name}'")
                            _mark_page_seen(device, page_name)
                            record_event(device, "page_seen", page=page_name,
                                         source="when_on_page")
                            for f in future_to_page:
                                f.cancel()
                            return page_name
                except FutureTimeoutError:
                    _dlog.warning("── when_on_page ── OCR batch timed out (>5s) — retrying")
                    for f in future_to_page:
                        f.cancel()

            except Exception as e:
                _dlog.error(f"Error in check loop: {e}", exc_info=True)
                print(f"[{device}] Error in check loop: {e}")

            time.sleep(check_interval)

    # ── TIMEOUT ───────────────────────────────────────────────────────────────
    msg = f"Timed out after {timeout}s waiting for {target_pages}"
    _dlog.warning(msg)
    print(f"[{device}] {msg}")

    if save_on_timeout:
        timeout_img = get_screenshot(device)
        if timeout_img is not None:
            count = _UNEXPECTED_PAGE_COUNTERS.get(device, 0) + 1
            _UNEXPECTED_PAGE_COUNTERS[device] = count

            safe_name  = _sanitize_device_id(device)
            img_name   = f"{safe_name}_{count}.png"
            img_path   = os.path.join(UNEXPECTED_PAGES_DIR, img_name)
            timeout_img.save(img_path)

            msg_with_img = f"{msg} — screenshot saved → {img_path}"
            _dlog.warning(msg_with_img)
            print(f"[{device}] Screenshot saved: {img_path}")

    return None

_REOPEN_GUARD = {}   # device -> attempt count

def reopen_device(device: str, max_retries: int = 2, timeout: float = 60.0) -> bool:
    """
    Emergency recovery — close the emulator window, relaunch it, wait for the
    home screen.

    Returns True if the device is back at the home screen and ready.
    Returns False if the window could not be relaunched or home was not reached.

    Does NOT reset per-device state. Callers (_reopen_device_capped) are
    responsible for calling reset_transient_recovery_state() before this, and
    reset_device_finished_state() when the device is truly done or failed.
    Full counter reset must NEVER happen inside reopen_device because it is
    called during active recovery where scenario counters (emulator close count,
    VPN drop count, etc.) must survive to enforce caps.

    Does NOT call prepare_target_app(). The caller (device_worker) is responsible for
    restarting prepare_target_app after this returns True. Calling prepare_target_app from here
    would create nested prepare_target_app calls (since reopen_device is called from
    within prepare_target_app's own call stack), leaking TargetAppGuard threads.

    Anti-loop guard: if called more than max_retries times for the same device
    without a successful run in between, it gives up and returns False.
    """
    dlog = _get_device_logger(device)

    # Anti-loop guard
    tries = _REOPEN_GUARD.get(device, 0) + 1
    _REOPEN_GUARD[device] = tries

    if tries > max_retries:
        dlog.error(
            f"── reopen_device ── Exceeded max_retries ({max_retries}). Giving up."
        )
        print(f"[{device}] CRITICAL: reopen_device exceeded max_retries ({max_retries}).")
        # append, never overwrite: an earlier issue in this run must survive
        append_issue(device, "fatal_crash_loop",
                     f"reopen_device exceeded max_retries ({max_retries})",
                     fn="reopen_device", phase="reopen")
        return False

    print(f"[{device}] REOPENING DEVICE (Attempt {tries}/{max_retries})...")
    dlog.info(f"── reopen_device ── Attempt {tries}/{max_retries}")

    # Close existing emulator window
    wn = get_window_name_from_shortcut(device)
    if wn:
        close_window_by_title(wn)

    cleanup_device_files(device)

    # Brief pause before relaunch
    time.sleep(5)
    connect_to_devices(device)

    # Wait for home screen — poll on_home_screen(), no screenshot or OCR
    dlog.info(f"── reopen_device ── Waiting up to {timeout}s for home screen")
    t0 = time.time()
    home_reached = False
    while time.time() - t0 < timeout:
        if on_home_screen(device):
            home_reached = True
            break
        time.sleep(2)

    if not home_reached:
        dlog.error("── reopen_device ── Home screen not reached after relaunch")
        print(f"[{device}] reopen_device: home screen not reached.")
        return False

    dlog.info("── reopen_device ── Home confirmed ✓")
    print(f"[{device}] Device recovered — home screen confirmed")

    # Do NOT call _reset_device_state() here. Scenario counters (emulator close
    # count, VPN drop count, reinstall count) must survive recovery so caps are
    # enforced correctly. reset_transient_recovery_state() was already called by
    # _reopen_device_capped() before this function was invoked.
    # Full reset happens only through reset_device_finished_state() when the
    # device is done, failed, or manually stopped.

    # Guard counter resets on a successful recovery
    _REOPEN_GUARD[device] = 0

    # Return True = device is physically recovered and ready.
    # The CALLER (device_worker) is responsible for restarting prepare_target_app.
    # prepare_target_app must NEVER be called from inside reopen_device because
    # reopen_device is itself called from within prepare_target_app's call stack
    # (_setup_vpn_inner → _reopen_device_capped → reopen_device), and
    # calling prepare_target_app here creates nested prepare_target_app calls on the same
    # device, leaking TargetAppGuard threads and running setup stages multiple times.
    dlog.info("── reopen_device ── returning True (device_worker will restart prepare_target_app)")
    return True

# ==============================================================================
# VPN GUARD SYSTEM
# ==============================================================================
#
# _reset_device_state(device)
#   Wipes all per-device state dicts so the next call to prepare_target_app/setup_vpn
#   starts completely fresh — as if the device was never touched this run.
#
# vpn_guard(device, dlog, context="")
#   Call this at any point inside setup_vpn where something unexpected could
#   have happened. It checks for known error conditions and returns one of:
#
#     ("ok",)           — no problem detected, caller continues normally
#     ("restart", bool) — full reset + prepare_target_app restarted, caller does:
#                             status, result = vpn_guard(...)

# Per-device registry of the currently active VpnGuard instance.
# start() registers; stop() deregisters.  Prevents two VpnGuard threads
# from running simultaneously for the same device.
_active_vpn_guards: dict = {}   # device → VpnGuard
#                             if status == "restart": return result
#     ("stage4",)       — unexpected screen fixed: VPN reopened, vpn_stage set
#                         to 3. Caller does nothing special — setup_vpn's
#                         if-chain will naturally fall into stage 4 next.
#     ("failed",)       — unrecoverable, caller returns False
#
# Errors handled (expandable):
#   1. Device offline          → full reset → prepare_target_app
#   2. No internet             → full reset → prepare_target_app
#   3. Unexpectedly on home    → open_vpn → vpn_stage = 3 (stage 4 next)
#   4. Unexpected/unknown page → go_home → open_vpn → vpn_stage = 3
# ==============================================================================


def _reset_device_state(device: str) -> None:
    """
    Wipe ALL per-device state so the next run starts completely fresh.
    Must be called before any full prepare_target_app restart (emulator reopen,
    internet-restored restart, normal retry cycle, guard recovery relaunch).

    Counters reset:
      VPN: stage, tries, kill/reopen count, reinstall count, down log
      TargetApp: stage, install attempts, kill/reopen count, reinstall count, not-fg log
      Connection issue: log, rolling counter
      Home/bounce: count, timestamps
      Emulator: reopen count, REOPEN_GUARD flag
      Guard: interrupt event, GUARD_RECOVERY_LOCKS entry, TargetAppGuard thread
      Controller retry: recovery_counters entry, guard counters
    """
    dlog = _get_device_logger(device)
    dlog.info(f"[RESET] _reset_device_state({device}) — clearing all per-device counters")

    # VPN counters
    vpn_stage.pop(device, None)
    stage_tries.pop(device, None)
    install_attempts.pop(device, None)
    _vpn_kill_reopen_count.pop(device, None)
    # _vpn_install_count is deliberately NOT cleared here.  It is the shared
    # install/reinstall budget and must survive mid-run recovery, otherwise a
    # device could reinstall ProtonVPN indefinitely by looping through resets.
    # Cleared only in reset_device_finished_state() via _ctr_reset_run().
    _vpn_down_timestamps.pop(device, None)

    # TargetApp counters
    target_app_stage.pop(device, None)
    target_app_install_attempts.pop(device, None)
    _target_app_kill_reopen_count.pop(device, None)
    _target_app_reinstall_count.pop(device, None)
    _target_app_not_fg_timestamps.pop(device, None)

    # Connection issue
    _connection_issue_log.pop(device, None)
    _connection_issue_timestamps.pop(device, None)
    _loading_connection_issue_count.pop(device, None)

    # Home/bounce
    _home_bounce_count.pop(device, None)
    _home_bounce_timestamps.pop(device, None)

    # Emulator (do NOT clear _device_reopen_count here —
    # it is preserved across Scenario D recoveries to enforce the 5-close cap.
    # It is cleared only by reset_device_finished_state() when device is done/failed.)
    _REOPEN_GUARD.pop(device, None)
    _device_reopen_offline_count.pop(device, None)
    _loading_phase_active.pop(device, None)
    _last_seen_page.pop(device, None)
    _target_app_open_in_progress_until.pop(device, None)   # clear open_target_app debounce
    _target_app_post_loading_minutemaid_until.pop(device, None)  # clear MinuteMaid window
    _last_vpn_change_failure_reason.pop(device, None)
    _last_guard_recovery_reason.pop(device, None)
    _vpn_app_unstable_timestamps.pop(device, None)
    _vpn_reinstall_for_instability.pop(device, None)

    # New per-session attempt budgets (Connect, Change Server, open_target_app, Switch,
    # Sign up, connection-issue OK).  Safe to clear here: these are per-app-
    # session, not per-run.  The per-RUN caps (self-closed, program reopen,
    # shared VPN install) are deliberately NOT touched — they only reset in
    # reset_device_finished_state().
    _ctr_reset_session(device)
    _target_app_page_checks_paused_until.pop(device, None)
    _target_app_page_checks_pause_reason.pop(device, None)
    _screenshot_failure_start_time.pop(device, None)
    _loading_attempt_state.pop(device, None)

    # Passive diagnostic frame — a screenshot taken before a reset shows a
    # screen that no longer exists, and the decoded image would otherwise stay
    # in memory for the rest of the run.
    clear_cached_screenshot(device)

    # Guard interrupt
    _guard_interrupt_clear(device)

    # Per-device recovery lock — remove so it gets recreated fresh
    with _GRL_MUTEX:
        _GUARD_RECOVERY_LOCKS.pop(device, None)

    # Stop and remove TargetApp guard if running
    g = _target_app_guards.pop(device, None)
    if g:
        try:
            g.stop()
        except Exception:
            pass

    # Stop and remove VpnGuard if running — a leaked VpnGuard thread would keep
    # reporting on a device that a new setup_vpn is already monitoring.
    vg = _active_vpn_guards.pop(device, None)
    if vg:
        try:
            vg.stop()
        except Exception:
            pass

    dlog.info(
        f"[RESET] _reset_device_state({device}) — done "
        f"| surviving run caps: {_counters_snapshot(device)}"
    )


def reset_transient_recovery_state(device: str) -> None:
    """
    Clear only guard/interrupt/lock/thread state during mid-run recovery
    (e.g. Scenario D emulator relaunch).

    Does NOT clear scenario counters (_device_reopen_count, _target_app_reinstall_count,
    _vpn_down_timestamps, etc.) — those must persist across recoveries so caps
    and frequency checks work correctly.

    Full counter reset only happens through reset_device_finished_state() when
    the device is truly done, failed, or manually stopped.
    """
    dlog = _get_device_logger(device)
    dlog.info(f"[RESET] reset_transient_recovery_state({device}) — guard/lock/thread only")
    # Guard interrupt + recovery lock
    _guard_interrupt_clear(device)
    with _GRL_MUTEX:
        _GUARD_RECOVERY_LOCKS.pop(device, None)
    # Reopen guard flag
    _REOPEN_GUARD.pop(device, None)
    # Page-check lockout must not survive a recovery — a stale window would
    # blind TargetAppGuard to real unexpected pages after the device comes back.
    _target_app_page_checks_paused_until.pop(device, None)
    _target_app_page_checks_pause_reason.pop(device, None)
    # Same reasoning for the cached diagnostic frame: it predates the relaunch.
    clear_cached_screenshot(device)
    # Stop and remove TargetAppGuard thread (will be restarted by prepare_target_app)
    g = _target_app_guards.pop(device, None)
    if g:
        try: g.stop()
        except Exception: pass
    # Same for VpnGuard — setup_vpn always creates a fresh one.
    vg = _active_vpn_guards.pop(device, None)
    if vg:
        try: vg.stop()
        except Exception: pass
    dlog.info(
        f"[RESET] reset_transient_recovery_state({device}) — done "
        f"| run caps preserved: {_counters_snapshot(device)}"
    )


def reset_device_finished_state(device: str) -> None:
    """
    Full reset when the device has completed all tasks, been marked failed, or
    manual stop was called.

    This is the ONLY place per-run caps are cleared.  Mid-run recovery must
    never reach here, otherwise a device could loop forever by resetting the
    very counters that are supposed to stop it.
    """
    dlog = _get_device_logger(device)
    dlog.info(
        f"[RESET] reset_device_finished_state({device}) — "
        f"final counters before wipe: {_counters_snapshot(device)}"
    )

    _reset_device_state(device)

    # Legacy counters
    _device_reopen_count.pop(device, None)
    _loading_full_restart_count.pop(device, None)
    _vpn_recovery_full_restart_count.pop(device, None)
    _vpn_kill_reopen_count.pop(device, None)
    _device_reopen_offline_count.pop(device, None)

    # All new per-run caps: self-closed, program reopen, shared VPN install,
    # unexpected-home history, intentional-close window, host-pause state.
    _ctr_reset_run(device)

    # A finished device starts its next run with a clean Issues cell.  Within a
    # run, append_issue() only ever appends, so nothing is lost mid-flight.
    clear_issues_for_fresh_start(device)

    # Belt and braces: _reset_device_state() above already dropped it, but the
    # final path must not depend on that. Nothing should hold a decoded frame
    # for a device that is done.
    clear_cached_screenshot(device)

    dlog.info(f"[RESET] reset_device_finished_state({device}) — all per-run state cleared")


# Per-device rolling timestamp logs for frequency detection
_vpn_down_timestamps:              dict = {}   # device → [float, ...]
_target_app_not_fg_timestamps:            dict = {}   # device → [float, ...]
_connection_issue_timestamps:      dict = {}   # device → [float, ...]
_loading_connection_issue_count:   dict = {}   # device → int
_target_app_reinstall_count:              dict = {}   # device → int  (0 or 1)
# NOTE: the old _vpn_reinstall_count (cap 1) is gone.  ProtonVPN installs and
# reinstalls now share one budget, _vpn_install_count (CAP_VPN_INSTALL), gated
# by vpn_install_allowed() in the SETUP CORE block.  Keeping the old counter
# alive would let setup_device's install and a recovery reinstall draw from two
# separate budgets and quietly exceed the cap.
_device_reopen_count:              dict = {}   # device → int
_loading_phase_active:             dict = {}   # device → bool  (True while TargetApp loading)
_last_seen_page:                   dict = {}   # device → str   (last page detected)
# Debounce: set to time.time() + _TARGET_APP_OPEN_DEBOUNCE_SECS when open_target_app fires.
# Any guard/recovery path that tries to call open_target_app within the window is
# skipped — TargetApp is still in its launch/transition period.
_target_app_open_in_progress_until:       dict = {}   # device → float (expiry timestamp)
_TARGET_APP_OPEN_DEBOUNCE_SECS                 = 18   # seconds after open_target_app before guard may reopen


def _mark_page_seen(device: str, page_name: str) -> None:
    """
    Update last-seen page and manage loading-phase state.
    Called by when_on_page() result, setup_target_app, and key detection points.
    """
    _last_seen_page[device] = page_name
    if page_name == "loading":
        _loading_phase_active[device] = True
    elif page_name in ("target app main", "game main map", "game main"):
        _loading_phase_active[device] = False


def _set_loading_phase(device: str, active: bool) -> None:
    """Explicitly set loading phase state."""
    _loading_phase_active[device] = active


# Known VPN foreground activities — anything outside this set is "unexpected"
_VPN_KNOWN_ACTIVITIES = {
    "RoutingActivity",
    "AddAccountActivity",
    "UpgradeOnboardingDialogActivity",
    "NoVpnPermissionActivity",
    "vpndialogs",
}
# Per-device counter: how many times home screen appeared unexpectedly during setup_vpn
_home_bounce_count: dict = {}       # device → int
_home_bounce_timestamps: dict = {}  # device → list of timestamps (for 5-in-60s detection)
_HOME_BOUNCE_MAX = 4                # reopen device after this many bounces
_HOME_BOUNCE_REINSTALL_COUNT = 5    # reinstall ProtonVPN if 5 bounces within 60s



# =============================================================================
# SETUP CORE  —  signals, counters, Issues appending, host-internet pause,
#                shared device-health checks, capped device reopen helpers
# -----------------------------------------------------------------------------
# This block is the shared foundation for the rewritten setup flow:
#
#     prepare_target_app -> setup_device -> setup_vpn -> (2s) -> setup_target_app -> Loading
#
# Design rules enforced here:
#   * Guards DETECT only.  Every recovery action lives on the main thread and
#     goes through the helpers below, so caps can never be bypassed.
#   * Host-internet-down is a CONTROLLER-LEVEL PAUSE, not a guard issue.  While
#     paused we do not click, reinstall, reopen, or increment any counter.
#   * Self-closed emulator and program-initiated reopen are separate counters
#     with separate caps, separated by an "intentional close" window.
# =============================================================================

# ── Internal return signals ──────────────────────────────────────────────────
# Every setup-phase function returns one of these strings.  Only prepare_target_app()
# converts them into the True/False the controller expects.
SIG_SUCCESS            = "success"
SIG_RESTART_SETUP_VPN  = "restart_setup_vpn"
SIG_RESTART_SETUP_TARGET_APP  = "restart_setup_target_app"
SIG_RESTART_BEFORE_TARGET_APP = "restart_prepare_target_app"
SIG_PAUSE_CONTROLLER   = "pause_controller"
SIG_FAIL_DEVICE        = "fail_device"
SIG_MANUAL_STOP        = "manual_stop"

_ALL_SIGNALS = {
    SIG_SUCCESS, SIG_RESTART_SETUP_VPN, SIG_RESTART_SETUP_TARGET_APP,
    SIG_RESTART_BEFORE_TARGET_APP, SIG_PAUSE_CONTROLLER, SIG_FAIL_DEVICE,
    SIG_MANUAL_STOP,
}

# Signals that must abort the current phase immediately and bubble all the way
# out to prepare_target_app() without any further recovery attempts.
_TERMINAL_SIGNALS = {SIG_FAIL_DEVICE, SIG_MANUAL_STOP}


# ── Caps (all "per device per run" unless stated) ────────────────────────────
# Every number here is referenced by name, never inlined, so the cap and the
# log line can never drift apart.
CAP_DEVICE_SELF_CLOSED      = 5     # emulator closed itself; we just reopen it
CAP_PROGRAM_DEVICE_REOPEN   = 2     # we deliberately closed/reopened it
CAP_VPN_INSTALL             = 2     # SHARED: setup_device install + recovery reinstall
CAP_CONNECT_ATTEMPTS        = 4     # per ProtonVPN session
CAP_CHANGE_SERVER_ATTEMPTS  = 3     # per VPN session
CAP_OPEN_TARGET_APP_ATTEMPTS       = 3
CAP_SWITCH_ATTEMPTS         = 3     # loading_warning / loading_warning1
CAP_SIGNUP_ATTEMPTS         = 3     # google_signin
CAP_CONNECTION_ISSUE_OK     = 3     # OK clicks on the connection-issue popup
CAP_UNEXPECTED_HOME_EVENTS  = 5     # within UNEXPECTED_HOME_WINDOW seconds

# Display calibration — every tap coordinate in this bot assumes these exactly.
EXPECTED_WIDTH              = 1920
EXPECTED_HEIGHT             = 1080
EXPECTED_DENSITY            = 240
DISPLAY_CHECK_ATTEMPTS      = 3     # retries when wm output is unreadable

# Timing constants
SCREENSHOT_FAIL_THRESHOLD   = 10.0  # continuous seconds of None screenshots
NOT_RESPONDING_THRESHOLD    = 10.0  # continuous seconds of failed ADB pings
LOADING_GONE_CONFIRM        = 5.0   # loading must stay gone this long
LOADING_INITIAL_WINDOW      = 30.0  # wait for any valid page after open_target_app
LOADING_STUCK_THRESHOLD     = 60.0  # no percent increase for this long
SIGNUP_PAGE_GUARD_LOCKOUT   = 15.0  # pause page checks after Sign up click
INTENTIONAL_CLOSE_WINDOW    = 30.0  # self-closed detection suppressed this long
UNEXPECTED_HOME_WINDOW      = 60.0  # rolling window for CAP_UNEXPECTED_HOME_EVENTS
VPN_HOME_TOLERANCE          = 5.0   # Home > this after open_vpn = unexpected_home
TARGET_APP_HOME_TOLERANCE          = 3.0   # Home > this after open_target_app = unexpected_home
TARGET_APP_PAGE_TOLERANCE          = 3.0   # TargetApp not foreground > this = unexpected_page
HOST_INTERNET_POLL_INTERVAL = 5.0   # worker-side poll while paused


# ── Per-device counters and state ────────────────────────────────────────────
# All of these survive mid-run recovery.  They are cleared ONLY by
# reset_device_finished_state() (device done / failed / manually stopped).
_device_self_closed_count:        dict = {}   # device -> int
_program_device_reopen_count:     dict = {}   # device -> int
_vpn_install_count:               dict = {}   # device -> int  (SHARED install+reinstall)
_connect_attempts:                dict = {}   # device -> int  (per ProtonVPN session)
_change_server_attempts:          dict = {}   # device -> int  (per VPN session)
_open_target_app_attempts:               dict = {}   # device -> int
_loading_warning_switch_attempts: dict = {}   # device -> int
_google_signin_signup_attempts:   dict = {}   # device -> int
_connection_issue_ok_attempts:    dict = {}   # device -> int
_loading_attempt_state:           dict = {}   # device -> int  (0=normal,1=forcestop,2=reinstall)
_unexpected_home_timestamps:      dict = {}   # device -> [float, ...]
_intentional_device_close_until:  dict = {}   # device -> float (epoch)
_screenshot_failure_start_time:   dict = {}   # device -> float | None
_host_internet_pause_state:       dict = {}   # device -> bool

# Counters that are per-session rather than per-run.  Reset by their owning
# phase, not by the finished-state reset.
_SESSION_COUNTERS = (
    _connect_attempts,
    _change_server_attempts,
    _open_target_app_attempts,
    _loading_warning_switch_attempts,
    _google_signin_signup_attempts,
    _connection_issue_ok_attempts,
)

# Every counter dict that a full per-run reset must clear.
_RUN_COUNTERS = (
    _device_self_closed_count,
    _program_device_reopen_count,
    _vpn_install_count,
    _connect_attempts,
    _change_server_attempts,
    _open_target_app_attempts,
    _loading_warning_switch_attempts,
    _google_signin_signup_attempts,
    _connection_issue_ok_attempts,
    _loading_attempt_state,
    _unexpected_home_timestamps,
    _intentional_device_close_until,
    _screenshot_failure_start_time,
    _host_internet_pause_state,
)


# ── Structured logging ───────────────────────────────────────────────────────

def _slog(dlog, device: str, fn: str, phase: str, msg: str, **kv) -> str:
    """
    Single structured log line for every important setup action.

    Always emits device / function / phase.  Extra context is passed as kwargs
    and rendered as key=value so the logs stay greppable:

        [SETUP] 127.0.0.1:5555 | Loading | loading_warning | clicked Switch
                page=loading_warning button=switch coord=(753,671)
                attempt=1/3 elapsed=7.4s

    Returns the formatted string so callers can reuse it for print()/Issues.
    """
    parts = []
    for key, val in kv.items():
        if val is None:
            continue
        if isinstance(val, float):
            parts.append(f"{key}={val:.1f}")
        else:
            parts.append(f"{key}={val}")
    tail = ("  " + " ".join(parts)) if parts else ""
    line = f"[SETUP] {device} | {fn} | {phase} | {msg}{tail}"
    try:
        dlog.info(line)
    except Exception:
        pass
    # _slog is the single structured-logging call across the whole setup flow,
    # so bridging it here captures phase transitions, guard handling and recovery
    # decisions without touching any individual call site.
    try:
        _record_event_from_slog(device, fn, phase, msg, kv)
    except Exception:
        pass
    return line


def _counters_snapshot(device: str) -> str:
    """Compact counter dump for Issues entries and escalation logs."""
    return (
        f"self_closed={_device_self_closed_count.get(device, 0)}/{CAP_DEVICE_SELF_CLOSED} "
        f"prog_reopen={_program_device_reopen_count.get(device, 0)}/{CAP_PROGRAM_DEVICE_REOPEN} "
        f"vpn_install={_vpn_install_count.get(device, 0)}/{CAP_VPN_INSTALL} "
        f"connect={_connect_attempts.get(device, 0)}/{CAP_CONNECT_ATTEMPTS} "
        f"chg_srv={_change_server_attempts.get(device, 0)}/{CAP_CHANGE_SERVER_ATTEMPTS} "
        f"open_target_app={_open_target_app_attempts.get(device, 0)}/{CAP_OPEN_TARGET_APP_ATTEMPTS}"
    )


# ── Counter helpers ──────────────────────────────────────────────────────────

def _ctr_get(store: dict, device: str, default: int = 0) -> int:
    """Read a per-device counter."""
    return store.get(device, default)


def _ctr_inc(store: dict, device: str, dlog=None, name: str = "") -> int:
    """Increment a per-device counter and return the NEW value."""
    new = store.get(device, 0) + 1
    store[device] = new
    if dlog is not None and name:
        dlog.debug(f"[COUNTER] {device} | {name} -> {new}")
    return new


def _ctr_reset_session(device: str) -> None:
    """
    Clear per-session attempt counters only.

    Called when a fresh ProtonVPN session or a fresh TargetApp launch starts.  Run
    caps (self-closed, program reopen, VPN install) are deliberately NOT
    touched here — those must survive every mid-run recovery.
    """
    for store in _SESSION_COUNTERS:
        store.pop(device, None)


def _ctr_reset_run(device: str) -> None:
    """
    Clear ALL per-run counters.  Only legitimate when the device is truly
    finished, failed, or manually stopped — never during mid-run recovery.
    """
    for store in _RUN_COUNTERS:
        store.pop(device, None)
    # The V2 unknown-UI capture is "once per device per RUN", so its latch is
    # released here with the rest of the per-run state — not during mid-run
    # recovery, which would let one device write the same artifact repeatedly.
    _vpn_unknown_captured.pop(device, None)


# ── Intentional-close window ─────────────────────────────────────────────────
# The emulator disappearing from netstat means one of two very different things:
#   * we closed it on purpose  -> program-initiated reopen, cap 2
#   * it vanished on its own   -> self-closed, cap 5, just reopen it
# The only way to tell them apart is to record our own intent first.

def mark_intentional_close(device: str, dlog=None,
                           window: float = INTENTIONAL_CLOSE_WINDOW) -> None:
    """Call immediately BEFORE the program closes a device on purpose."""
    until = time.time() + window
    _intentional_device_close_until[device] = until
    if dlog is not None:
        dlog.info(
            f"[CLOSE-FLAG] {device} | intentional close window opened for "
            f"{window:.0f}s (until={until:.1f}) — self-closed detection suppressed"
        )


def clear_intentional_close(device: str, dlog=None) -> None:
    """Call only AFTER the device has reopened and ADB is ready again."""
    if _intentional_device_close_until.pop(device, None) is not None and dlog is not None:
        dlog.info(f"[CLOSE-FLAG] {device} | intentional close window cleared")


def is_intentional_close_active(device: str) -> bool:
    """True while the program's own close/reopen window is still open."""
    return time.time() < _intentional_device_close_until.get(device, 0.0)


# ── Issues tab — append, never overwrite ─────────────────────────────────────
# update_status() writes into _PENDING_STATUS[device][header], so writing
# "Issues" twice in one run silently discarded the first entry.  append_issue()
# concatenates instead, keeping the full recovery history for the run.

_ISSUES_HEADER   = "Issues"
_ISSUES_MAX_CHARS = 45000          # Google Sheets hard limit is 50,000 per cell
_ISSUES_SEP       = " || "


def append_issue(device: str, issue_code: str, detail: str = "",
                 fn: str = "", phase: str = "") -> None:
    """
    Append one issue entry to the buffered Issues cell for this device.

    Never removes or overwrites an entry written earlier in the same run.
    Each entry carries timestamp, function, phase, issue code, detail and a
    snapshot of the recovery counters at the moment it fired.
    """
    key = (device or "").strip()
    if not key:
        return

    stamp = _dt.datetime.now().strftime("%H:%M:%S")
    bits  = [stamp]
    if fn:
        bits.append(fn)
    if phase:
        bits.append(f"({phase})")
    bits.append(issue_code)
    if detail:
        bits.append(f"- {detail}")
    bits.append(f"[{_counters_snapshot(key)}]")
    entry = " ".join(bits)

    existing = ""
    try:
        existing = _PENDING_STATUS.get(key, {}).get(_ISSUES_HEADER, "") or ""
    except Exception:
        existing = ""

    combined = (existing + _ISSUES_SEP + entry) if existing else entry
    if len(combined) > _ISSUES_MAX_CHARS:
        # Keep the newest entries; the oldest are the least useful for triage.
        combined = "...(truncated)... " + combined[-_ISSUES_MAX_CHARS:]

    try:
        _PENDING_STATUS.setdefault(key, {})[_ISSUES_HEADER] = combined
    except Exception:
        pass

    dlog = _get_device_logger(key)
    dlog.error(f"[ISSUE] {key} | {issue_code} | {detail} | {fn}/{phase}")
    print(f"[{key}] ISSUE: {issue_code} {detail}")
    try:
        record_event(key, "issue", issue_code=issue_code, detail=detail,
                     fn=fn, phase=phase, counters=_counters_snapshot(key))
    except Exception:
        pass


def clear_issues_for_fresh_start(device: str) -> None:
    """
    Drop buffered Issues text for a device.

    Only valid on a genuinely fresh device start (reset_device_finished_state).
    Never call this mid-run — that is exactly the overwrite bug this replaces.
    """
    key = (device or "").strip()
    if not key:
        return
    try:
        if key in _PENDING_STATUS:
            _PENDING_STATUS[key].pop(_ISSUES_HEADER, None)
    except Exception:
        pass


# ── Manual stop / controller pause signalling ────────────────────────────────

_WORKER_PAUSE_EVENT = None   # set by device_worker from the controller


def _set_worker_pause_event(ev) -> None:
    """Called once by device_worker so the bot can see controller pause state."""
    global _WORKER_PAUSE_EVENT
    _WORKER_PAUSE_EVENT = ev


def _pause_requested() -> bool:
    """True while the controller has paused this worker (host internet down)."""
    try:
        ev = _WORKER_PAUSE_EVENT
        return bool(ev is not None and ev.is_set())
    except Exception:
        return False


def wait_while_paused(device: str, dlog=None, phase: str = "", fn: str = "",
                      context: str = "setup") -> str:
    """
    The pause gate.  Every action and checkpoint path funnels through here.

    When the controller sets this worker's pause_event (host internet down) we
    stop dead and wait.  While waiting we perform NO device actions at all:

        no taps, no Back presses, no app launches
        no reinstalls, no device close/reopen
        no recovery-counter increments
        no screenshots or OCR

    Manual Stop stays responsive throughout.  pause_event is deliberately a
    different Event from stop_event — pausing is not stopping.

    `context` decides what "resumed" means to the caller:
        "setup"   -> caller returns SIG_RESTART_BEFORE_TARGET_APP
        "loading" -> caller continues Loading (and clicks OK if the popup is up)
        "runtime" -> caller aborts the current step so the task restarts

    Returns "ok" (never paused), "resumed", or SIG_MANUAL_STOP.
    """
    if not _pause_requested():
        return "ok"

    if dlog is None:
        dlog = _get_device_logger(device)

    t0 = time.time()
    _slog(dlog, device, fn or "wait_while_paused", phase or context,
          "CONTROLLER PAUSE — holding still "
          "(no clicks / no recovery / no reinstall / no reopen / no counters)",
          context=context)
    print(f"[{device}] PAUSED by controller — waiting (host internet down)")

    while _pause_requested():
        if _stop_requested():
            _slog(dlog, device, fn or "wait_while_paused", phase or context,
                  "manual stop while paused", elapsed=time.time() - t0)
            return SIG_MANUAL_STOP
        time.sleep(0.5)

    waited = time.time() - t0
    _slog(dlog, device, fn or "wait_while_paused", phase or context,
          "controller released the pause — resuming from safe checkpoint",
          elapsed=waited, context=context)
    print(f"[{device}] Resumed after {waited:.0f}s pause")

    if context == "runtime":
        # Marker read by device_worker's GuardRecoveryFailed handler so the
        # current task restarts from the beginning rather than triggering a
        # full prepare_target_app — nothing about the device changed while we waited.
        _last_guard_recovery_reason[device] = "host_pause_resumed"

    return "resumed"


def stop_aware_sleep(device: str, seconds: float, dlog=None,
                     chunk: float = 0.5, honor_pause: bool = True) -> str:
    """
    Sleep in small chunks, aborting early on manual stop or controller pause.

    Returns:
        SIG_SUCCESS            — the full duration elapsed
        SIG_MANUAL_STOP        — the controller asked this worker to stop
        SIG_RESTART_BEFORE_TARGET_APP — we were paused mid-wait and have resumed

    `honor_pause=False` is used by pause_controller_until_host_internet_back()
    itself, which is already inside a pause and must not re-enter the gate.
    """
    t_end = time.time() + max(0.0, seconds)
    while time.time() < t_end:
        if _stop_requested():
            if dlog is not None:
                dlog.warning(f"[STOP] {device} | manual stop during {seconds:.1f}s wait")
            return SIG_MANUAL_STOP
        if honor_pause and _pause_requested():
            gate = wait_while_paused(device, dlog, phase="sleep",
                                     fn="stop_aware_sleep", context="setup")
            if gate == SIG_MANUAL_STOP:
                return SIG_MANUAL_STOP
            return SIG_RESTART_BEFORE_TARGET_APP
        time.sleep(min(chunk, max(0.05, t_end - time.time())))
    return SIG_SUCCESS


# ── Host internet — controller-level pause ───────────────────────────────────

def host_internet_ok() -> bool:
    """
    Single entry point for "is the PC's internet up?".

    Delegates to the existing _host_internet_ok_bot() implementation (ping
    8.8.8.8, ping 1.1.1.1, then an HTTPS generate_204 fallback) so there is
    exactly one definition of host reachability in the bot.
    """
    try:
        return bool(_host_internet_ok_bot())
    except Exception:
        # Fail OPEN: never declare a global outage because our own check blew up.
        return True


def _notify_host_internet_pause(device: str, reason: str) -> None:
    """
    Tell the controller to enter pause (not the old kill/close emergency).

    The controller sets a global pause flag, stops launching new devices, holds
    the queue, and signals running workers to pause in place.  It must NOT
    terminate subprocesses or close emulators for this condition.
    """
    if _WORKER_STATUS_Q is not None:
        try:
            _WORKER_STATUS_Q.put_nowait({
                "type":   "host_internet_pause",
                "dev_id": device,
                "reason": reason,
            })
        except Exception:
            pass


def _notify_host_internet_back(device: str) -> None:
    """Tell the controller this worker has seen host internet return."""
    if _WORKER_STATUS_Q is not None:
        try:
            _WORKER_STATUS_Q.put_nowait({
                "type":   "host_internet_back",
                "dev_id": device,
            })
        except Exception:
            pass


def pause_controller_until_host_internet_back(device: str, dlog, phase: str = "",
                                              fn: str = "") -> str:
    """
    Hold this device in place until host internet returns.

    While paused we deliberately do NOTHING that could make things worse:
      * no clicking, no Back presses
      * no app reinstall
      * no device close/reopen
      * no counter increments
      * no new device actions

    Manual Stop stays responsive throughout.

    Returns:
        SIG_RESTART_BEFORE_TARGET_APP — host internet came back; caller restarts clean
        SIG_MANUAL_STOP        — controller asked us to stop while paused
    """
    if _host_internet_pause_state.get(device):
        # Already inside a pause loop for this device — don't stack two.
        dlog.debug(f"[HOST-NET] {device} | pause already active — not re-entering")
    _host_internet_pause_state[device] = True

    t0 = time.time()
    _slog(dlog, device, fn or "pause_controller", phase or "host_internet",
          "HOST INTERNET DOWN — pausing device in place "
          "(no clicks / no reopen / no reinstall / no counter changes)")
    print(f"[{device}] HOST INTERNET DOWN — paused, waiting for it to return")

    append_issue(device, "host_internet_down_pause",
                 "paused in place, awaiting host internet", fn=fn, phase=phase)
    _notify_host_internet_pause(device, "host_internet_down")

    try:
        while True:
            if _stop_requested():
                _slog(dlog, device, fn or "pause_controller", phase or "host_internet",
                      "manual stop while paused", elapsed=time.time() - t0)
                return SIG_MANUAL_STOP

            # Resume needs BOTH conditions: our own host check must pass, and
            # the controller must not be holding this worker.  The event is the
            # controller -> worker channel; when it is not wired (the normal
            # case today) _pause_requested() is False and the host check alone
            # decides.
            if host_internet_ok() and not _pause_requested():
                elapsed = time.time() - t0
                _slog(dlog, device, fn or "pause_controller", phase or "host_internet",
                      "host internet RESTORED — resuming from safe checkpoint",
                      elapsed=elapsed, signal=SIG_RESTART_BEFORE_TARGET_APP)
                print(f"[{device}] Host internet restored after {elapsed:.0f}s — resuming")
                _notify_host_internet_back(device)
                return SIG_RESTART_BEFORE_TARGET_APP

            if _pause_requested():
                dlog.info(
                    f"[HOST-NET] {device} | host internet is back but the controller "
                    f"is still holding this worker — staying paused"
                )

            waited = time.time() - t0
            dlog.info(
                f"[HOST-NET] {device} | still down after {waited:.0f}s — "
                f"re-checking in {HOST_INTERNET_POLL_INTERVAL:.0f}s"
            )
            # Chunked so manual Stop is honoured within ~0.5s.  honor_pause is
            # False here: we are already the pause, re-entering the gate from
            # inside it would recurse.
            if stop_aware_sleep(device, HOST_INTERNET_POLL_INTERVAL, dlog,
                                honor_pause=False) == SIG_MANUAL_STOP:
                return SIG_MANUAL_STOP
    finally:
        _host_internet_pause_state.pop(device, None)


def check_network_and_maybe_pause(device: str, dlog, phase: str = "",
                                  fn: str = "") -> str:
    """
    The single decision point for every suspected network failure.

    Call this whenever: the device internet check fails, the VPN will not
    connect, tun0 is down, an TargetApp connection-issue page appears, or runtime
    network recovery starts.

    Returns:
        "ok"                   — device internet is actually fine, carry on
        "device_only"          — host internet is up, so this is a device/VPN
                                 problem; caller owns the normal recovery path
        SIG_RESTART_BEFORE_TARGET_APP — host was down, we paused, it is back now
        SIG_MANUAL_STOP        — stop requested while paused
    """
    if _stop_requested():
        return SIG_MANUAL_STOP

    dev_ok = False
    try:
        dev_ok = bool(internet(device))
    except Exception as exc:
        dlog.warning(f"[HOST-NET] {device} | internet(device) raised: {exc!r}")

    if dev_ok:
        _slog(dlog, device, fn or "check_network", phase,
              "device internet OK — no network recovery needed")
        return "ok"

    host_ok = host_internet_ok()
    _slog(dlog, device, fn or "check_network", phase,
          "device internet FAILED — classified by host check",
          host_internet="up" if host_ok else "DOWN")

    if host_ok:
        # Host is fine, so this is emulator/VPN-local.  Caller decides what to
        # do (VPN reconnect, change server, program reopen, ...).
        return "device_only"

    return pause_controller_until_host_internet_back(device, dlog, phase=phase, fn=fn)


# ── Shared device-health checks ──────────────────────────────────────────────
# Used by BOTH VpnGuard and TargetAppGuard.  There is deliberately no third "common
# guard" thread: only one phase guard runs at a time and it calls these.

class HealthState:
    """
    Mutable per-guard scratch space for the continuous-failure windows.

    A single failed ADB ping or a single None screenshot means nothing; what
    matters is the same failure persisting for N continuous seconds.  This
    holder tracks when each streak started so the guard loop stays stateless.
    """

    __slots__ = ("not_responding_since", "screenshot_failed_since", "last_issue")

    def __init__(self):
        self.not_responding_since    = None
        self.screenshot_failed_since = None
        self.last_issue              = None

    def reset(self):
        self.not_responding_since    = None
        self.screenshot_failed_since = None


def check_device_closed(device: str, dlog=None) -> "str | None":
    """
    Detect an emulator that closed WITHOUT us asking it to.

    netstat (is_emulator_process_alive) is authoritative here because it
    bypasses ADB entirely — ADB can drop simply because the VPN shifted the
    routing table, which is not a closed emulator.

    Returns "device_closed_by_itself" or None.
    """
    try:
        alive = is_emulator_process_alive(device)
    except Exception:
        return None          # fail-open: never invent a crash
    if alive:
        return None
    if is_intentional_close_active(device):
        if dlog is not None:
            dlog.debug(
                f"[HEALTH] {device} | port not LISTENING but intentional-close "
                f"window is active — NOT counted as self-closed"
            )
        return None
    if dlog is not None:
        dlog.warning(f"[HEALTH] {device} | emulator port not LISTENING — self-closed")
    return "device_closed_by_itself"


def check_device_not_responding(device: str, state: HealthState,
                                dlog=None) -> "str | None":
    """
    Detect a live-but-frozen emulator: port still LISTENING, ADB dead.

    Only fires after NOT_RESPONDING_THRESHOLD continuous seconds so a single
    slow ping never triggers a device reopen.
    """
    try:
        if _adb_ping(device):
            if state.not_responding_since is not None and dlog is not None:
                dlog.info(f"[HEALTH] {device} | ADB responsive again — streak reset")
            state.not_responding_since = None
            return None
    except Exception:
        pass

    now = time.time()
    if state.not_responding_since is None:
        state.not_responding_since = now
        if dlog is not None:
            dlog.warning(
                f"[HEALTH] {device} | ADB ping failed — "
                f"{NOT_RESPONDING_THRESHOLD:.0f}s tolerance started"
            )
        return None

    held = now - state.not_responding_since
    if held >= NOT_RESPONDING_THRESHOLD:
        if dlog is not None:
            dlog.error(
                f"[HEALTH] {device} | ADB unresponsive for {held:.1f}s "
                f"(>{NOT_RESPONDING_THRESHOLD:.0f}s) — device_not_responding"
            )
        return "device_not_responding"
    return None


def check_screenshot_failed_repeatedly(device: str, state: HealthState,
                                       img_was_none: bool,
                                       dlog=None) -> "str | None":
    """
    Detect screenshots failing continuously for SCREENSHOT_FAIL_THRESHOLD
    seconds while screenshots are actually needed.

    The caller passes the result of its own get_screenshot() attempt so we
    never take an extra screenshot just to check on screenshots.
    """
    now = time.time()
    if not img_was_none:
        if state.screenshot_failed_since is not None and dlog is not None:
            dlog.info(f"[HEALTH] {device} | screenshots recovered — streak reset")
        state.screenshot_failed_since = None
        _screenshot_failure_start_time.pop(device, None)
        return None

    # While recording is active, screencap contends with screenrecord for the
    # device capture pipeline. A blocked screencap then says nothing about device
    # health — so the threshold is widened rather than failing a healthy device
    # for a diagnostic feature. THIS APPLIES TO THE SCREENSHOT CLASS ONLY:
    # check_device_closed() (netstat) and check_device_not_responding() (ADB ping)
    # are deliberately untouched and still fire at their normal thresholds.
    recording = False
    try:
        recording = recording_enabled_or_active(device)
    except Exception:
        pass
    threshold = (SCREENSHOT_FAIL_THRESHOLD_RECORDING if recording
                 else SCREENSHOT_FAIL_THRESHOLD)

    if state.screenshot_failed_since is None:
        state.screenshot_failed_since = now
        _screenshot_failure_start_time[device] = now
        if dlog is not None:
            dlog.warning(
                f"[HEALTH] {device} | screenshot returned None — "
                f"{threshold:.0f}s tolerance started"
                + ("  (recording active — widened; screenrecord contends with "
                   "screencap)" if recording else "")
            )
        return None

    held = now - state.screenshot_failed_since
    if held >= threshold:
        if recording:
            # Even past the widened threshold, prefer a positive liveness signal
            # over failing the device. If netstat says the emulator is up and ADB
            # answers, this is contention, not a dead device.
            alive = False
            try:
                alive = bool(is_emulator_process_alive(device)) and bool(_adb_ping(device))
            except Exception:
                alive = False
            if alive:
                if dlog is not None:
                    dlog.warning(
                        f"[HEALTH] {device} | screenshots failing for {held:.1f}s "
                        f"while recording, but the emulator is LISTENING and ADB "
                        f"answers — treating as screenrecord contention, NOT a "
                        f"device failure (recording is diagnostic and must never "
                        f"fail a device)"
                    )
                # Restart the window so we keep watching without escalating.
                state.screenshot_failed_since = now
                _screenshot_failure_start_time[device] = now
                return None
        if dlog is not None:
            dlog.error(
                f"[HEALTH] {device} | screenshots failing for {held:.1f}s "
                f"(>{threshold:.0f}s) — screenshot_failed_repeatedly"
                + ("  (recording active AND device not answering)" if recording else "")
            )
        return "screenshot_failed_repeatedly"
    return None


def shared_device_health(device: str, state: HealthState, dlog=None,
                         img_was_none: "bool | None" = None) -> "str | None":
    """
    Run the shared checks in priority order and return the first issue found.

    Order matters: a closed emulator explains every other symptom, and a frozen
    emulator explains screenshot failures, so checking cheapest-and-most-
    fundamental first avoids misclassifying the recovery.
    """
    issue = check_device_closed(device, dlog)
    if issue:
        state.last_issue = issue
        return issue

    issue = check_device_not_responding(device, state, dlog)
    if issue:
        state.last_issue = issue
        return issue

    if img_was_none is not None:
        issue = check_screenshot_failed_repeatedly(device, state, img_was_none, dlog)
        if issue:
            state.last_issue = issue
            return issue

    return None


# ── Capped device recovery (main thread only) ────────────────────────────────

def recover_self_closed_device(device: str, dlog, phase: str = "",
                               fn: str = "") -> str:
    """
    The emulator closed on its own.  Just open it again — do not close anything.

    Capped at CAP_DEVICE_SELF_CLOSED per device per run.  This counter is
    completely separate from the program-initiated reopen counter so a flaky
    emulator can never eat our deliberate-recovery budget.
    """
    count = _ctr_inc(_device_self_closed_count, device, dlog, "device_self_closed")
    if count > CAP_DEVICE_SELF_CLOSED:
        _slog(dlog, device, fn or "recover_self_closed_device", phase,
              "self-closed cap exhausted — failing device",
              attempt=f"{count}/{CAP_DEVICE_SELF_CLOSED}", signal=SIG_FAIL_DEVICE)
        append_issue(device, "device_self_closed",
                     f"emulator self-closed {count} times "
                     f"(cap {CAP_DEVICE_SELF_CLOSED}) — giving up",
                     fn=fn, phase=phase)
        return SIG_FAIL_DEVICE

    _slog(dlog, device, fn or "recover_self_closed_device", phase,
          "emulator self-closed — relaunching directly (no close first)",
          attempt=f"{count}/{CAP_DEVICE_SELF_CLOSED}")
    append_issue(device, "device_self_closed",
                 f"emulator closed by itself, relaunch {count}/{CAP_DEVICE_SELF_CLOSED}",
                 fn=fn, phase=phase)

    # Guard/lock/thread state only — recovery counters must survive.
    reset_transient_recovery_state(device)

    try:
        _launch_device_for_worker(device)
    except Exception as exc:
        dlog.error(f"[RECOVER] {device} | _launch_device_for_worker raised: {exc!r}")

    # Wait for ADB to come back so the caller restarts against a live device.
    t0 = time.time()
    back = False
    while time.time() - t0 < 60.0:
        if _stop_requested():
            return SIG_MANUAL_STOP
        if _device_exists_in_adb(device):
            back = True
            break
        try:
            _adb_connect_quiet(device)
        except Exception:
            pass
        time.sleep(2.0)

    _slog(dlog, device, fn or "recover_self_closed_device", phase,
          "relaunch finished", elapsed=time.time() - t0,
          adb_back=back, signal=SIG_RESTART_BEFORE_TARGET_APP)
    return SIG_RESTART_BEFORE_TARGET_APP


def program_reopen_device(device: str, dlog, reason: str = "",
                          phase: str = "", fn: str = "") -> str:
    """
    Deliberately close and reopen the emulator as a recovery step.

    Capped at CAP_PROGRAM_DEVICE_REOPEN per device per run.  Sets the
    intentional-close window first so neither guard mistakes our own close for
    a self-closed emulator and burns the wrong counter.
    """
    count = _ctr_inc(_program_device_reopen_count, device, dlog, "program_device_reopen")
    if count > CAP_PROGRAM_DEVICE_REOPEN:
        _slog(dlog, device, fn or "program_reopen_device", phase,
              "program reopen cap exhausted — failing device",
              reason=reason, attempt=f"{count}/{CAP_PROGRAM_DEVICE_REOPEN}",
              signal=SIG_FAIL_DEVICE)
        append_issue(device, "program_device_reopen_cap_exhausted",
                     f"reason={reason} cap={CAP_PROGRAM_DEVICE_REOPEN}",
                     fn=fn, phase=phase)
        return SIG_FAIL_DEVICE

    _slog(dlog, device, fn or "program_reopen_device", phase,
          "program-initiated device close/reopen",
          reason=reason, attempt=f"{count}/{CAP_PROGRAM_DEVICE_REOPEN}")

    mark_intentional_close(device, dlog)
    reset_transient_recovery_state(device)

    ok = False
    t0 = time.time()
    try:
        ok = bool(reopen_device(device))
    except Exception as exc:
        dlog.error(f"[RECOVER] {device} | reopen_device raised: {exc!r}")

    if ok:
        clear_intentional_close(device, dlog)
        _slog(dlog, device, fn or "program_reopen_device", phase,
              "device reopened and ADB ready", elapsed=time.time() - t0,
              signal=SIG_RESTART_BEFORE_TARGET_APP)
        return SIG_RESTART_BEFORE_TARGET_APP

    # Reopen failed.  Leave the intentional-close window to expire on its own so
    # a still-transitioning emulator is not immediately counted as self-closed.
    _slog(dlog, device, fn or "program_reopen_device", phase,
          "reopen_device FAILED", elapsed=time.time() - t0,
          reason=reason, signal=SIG_RESTART_BEFORE_TARGET_APP)
    append_issue(device, "program_device_reopen_failed", f"reason={reason}",
                 fn=fn, phase=phase)
    return SIG_RESTART_BEFORE_TARGET_APP


def handle_screenshot_failure(device: str, dlog, phase: str = "",
                              fn: str = "") -> str:
    """
    Recovery for screenshots failing continuously for >10s.

    Deliberately never calls vpn_change_server — a black screencap says nothing
    about the VPN tunnel, and changing servers here only wasted time.
    """
    _slog(dlog, device, fn or "handle_screenshot_failure", phase,
          "screenshots failed repeatedly — classifying device health")
    append_issue(device, "screenshot_failed_repeatedly",
                 f">{SCREENSHOT_FAIL_THRESHOLD:.0f}s of failed screenshots",
                 fn=fn, phase=phase)

    if check_device_closed(device, dlog):
        return recover_self_closed_device(device, dlog, phase=phase, fn=fn)

    tmp = HealthState()
    tmp.not_responding_since = time.time() - NOT_RESPONDING_THRESHOLD
    if check_device_not_responding(device, tmp, dlog):
        return program_reopen_device(device, dlog, reason="device_not_responding",
                                     phase=phase, fn=fn)

    # Device is alive and ADB answers, but we still cannot capture the screen.
    return program_reopen_device(device, dlog, reason="screenshot_failed_repeatedly",
                                 phase=phase, fn=fn)


# ── Shared ProtonVPN install/reinstall cap ───────────────────────────────────

def vpn_install_allowed(device: str, dlog, reason: str,
                        phase: str = "", fn: str = "") -> bool:
    """
    Single gate for EVERY ProtonVPN install or reinstall.

    setup_device's first-time install and every later recovery reinstall share
    one counter (CAP_VPN_INSTALL per device per run), so the two paths cannot
    combine to exceed the cap.  Checking and incrementing happen together here
    precisely so no caller can do one without the other.

    Returns True if the install may proceed (counter already incremented).
    """
    used = _ctr_get(_vpn_install_count, device)
    if used >= CAP_VPN_INSTALL:
        _slog(dlog, device, fn or "vpn_install_allowed", phase,
              "ProtonVPN install/reinstall DENIED — shared cap exhausted",
              reason=reason, attempt=f"{used}/{CAP_VPN_INSTALL}")
        append_issue(device, "vpn_install_cap_exhausted",
                     f"reason={reason} cap={CAP_VPN_INSTALL}", fn=fn, phase=phase)
        return False

    new = _ctr_inc(_vpn_install_count, device, dlog, "vpn_install")
    _slog(dlog, device, fn or "vpn_install_allowed", phase,
          "ProtonVPN install/reinstall ALLOWED (shared cap)",
          reason=reason, attempt=f"{new}/{CAP_VPN_INSTALL}")
    return True


# ── Strict VPN gate ──────────────────────────────────────────────────────────

def require_vpn_up_or_fail(device: str, dlog, fn: str = "", phase: str = "",
                           issue_code: str = "vpn_down",
                           detail: str = "") -> str:
    """
    Hard gate: tun0 must be UP, or the device fails.

    The rule this enforces: if the VPN cannot be restored, the bot must NOT
    touch Target Application at all. Playing unprotected is worse than not playing —
    it exposes the real IP, which is the entire reason the VPN is here.

    Deliberately distinguishes three situations:

      host internet down  -> NOT a VPN failure. Pause and let the existing
                             controller pause handle it; on resume the caller
                             restarts from a clean checkpoint.
      device gone/frozen  -> NOT a VPN failure. Left to the existing device
                             recovery paths.
      device alive, host  -> a real, unrecoverable VPN failure: fail_device.
      up, tun0 still down

    Returns SIG_SUCCESS, SIG_FAIL_DEVICE, SIG_RESTART_BEFORE_TARGET_APP or
    SIG_MANUAL_STOP.
    """
    if _stop_requested():
        return SIG_MANUAL_STOP

    try:
        tun_up = bool(vpn_activity(device))
    except Exception as exc:
        dlog.warning(f"[VPN-GATE] {device} | vpn_activity raised: {exc!r}")
        tun_up = False

    if tun_up:
        _slog(dlog, device, fn or "require_vpn_up_or_fail", phase,
              "tun0 verified UP", tun0="up")
        return SIG_SUCCESS

    host_ok = host_internet_ok()
    _slog(dlog, device, fn or "require_vpn_up_or_fail", phase,
          "tun0 is DOWN — classifying before refusing",
          tun0="down", host_internet="up" if host_ok else "DOWN")

    if not host_ok:
        # Host outage, not a VPN failure. Pause in place; on resume the caller
        # restarts cleanly and this gate runs again.
        sig = pause_controller_until_host_internet_back(
            device, dlog, phase=phase, fn=fn or "require_vpn_up_or_fail")
        _slog(dlog, device, fn or "require_vpn_up_or_fail", phase,
              "host internet pause resolved — caller restarts", signal=sig)
        return sig

    # Emulator health is someone else's problem; only judge VPN here.
    if check_device_closed(device, dlog):
        _slog(dlog, device, fn or "require_vpn_up_or_fail", phase,
              "device closed — device recovery owns this, not the VPN gate")
        return SIG_RESTART_BEFORE_TARGET_APP

    _slog(dlog, device, fn or "require_vpn_up_or_fail", phase,
          "REFUSING to continue without VPN — device alive, host internet up, "
          "tun0 still down", tun0="down", host_internet="up",
          issue=issue_code, signal=SIG_FAIL_DEVICE)
    append_issue(device, issue_code,
                 detail or "tun0 not active and could not be restored; "
                           "refusing to continue without VPN",
                 fn=fn or "require_vpn_up_or_fail", phase=phase)
    return SIG_FAIL_DEVICE


# ── Signal helpers ───────────────────────────────────────────────────────────

def _is_terminal(sig: str) -> bool:
    """True for signals that must abort everything with no further recovery."""
    return sig in _TERMINAL_SIGNALS


def _sig_or_stop(sig: str) -> str:
    """Normalise an unknown/None signal into a safe terminal value."""
    if sig in _ALL_SIGNALS:
        return sig
    return SIG_FAIL_DEVICE


# =============================================================================
# END SETUP CORE
# =============================================================================
# =============================================================================
# OPTIONAL RUN RECORDING  —  segmented screen video + structured event timeline
# -----------------------------------------------------------------------------
# Enabled per run by the controller's "Record video" checkbox, delivered to the
# worker as cfg_data["record_video"].  Off by default and near-zero cost when
# off: every hook starts with a dict lookup and returns immediately.
#
# Two independent products, deliberately decoupled:
#
#   1. VIDEO      adb screenrecord, in segments, pulled to the host
#   2. EVENTS     events.jsonl — what page was seen, what button was clicked,
#                 at which coordinate, on which attempt, and whether the click
#                 registered
#
# Decoupled because they fail differently.  screenrecord is unavailable or
# flaky on some emulator builds, and when it dies the event timeline is still
# the thing that actually explains a failed run.  So a video failure never
# stops event capture, and neither ever fails the automation.
#
# Android's screenrecord has a hard per-invocation time limit (3 minutes on most
# builds), which is why this records in ~170s segments back-to-back rather than
# one long file.
# =============================================================================

RECORDINGS_ROOT        = "recordings"
RECORD_SEGMENT_SECONDS = 170      # under Android's 180s screenrecord ceiling
RECORD_BIT_RATE        = "4000000"
RECORD_SIZE            = "1280x720"   # downscaled: smaller files, same detail for review
_RECORD_PULL_TIMEOUT   = 120

_RECORD_ENABLED: dict = {}   # device -> bool
_RECORD_STATE:   dict = {}   # device -> dict
_EVENT_PATH:     dict = {}   # device -> path to events.jsonl
_EVENT_LOCK           = _threading.Lock()
_RECORD_RUN_ID        = None  # one timestamp per worker process


def _recording_run_id() -> str:
    """One timestamped run id per worker process; every run gets its own folder."""
    global _RECORD_RUN_ID
    if _RECORD_RUN_ID is None:
        _RECORD_RUN_ID = _dt.datetime.now().strftime("%Y%m%d-%H%M%S")
    return _RECORD_RUN_ID


def recording_enabled(device: str) -> bool:
    return bool(_RECORD_ENABLED.get(device))


def recording_enabled_or_active(device: str) -> bool:
    """
    True while screenrecord is (or may be) holding the device capture pipeline.

    `adb shell screenrecord` and `adb exec-out screencap` contend for the same
    capture path on BlueStacks. While a recording is running, screencap can block
    past its timeout through no fault of the device — 3,426 such timeouts in the
    31/07 run, every sampled one inside a recording window and none outside.

    Callers use this to keep a *diagnostic* feature from being able to fail a
    device: screenshot timeouts get a longer budget and a longer health
    threshold while this is true. Device-liveness checks are NOT affected.
    """
    if _RECORD_ENABLED.get(device):
        return True
    st = _RECORD_STATE.get(device)
    if not st:
        return False
    try:
        th = st.get("thread")
        if th is not None and th.is_alive():
            return True
        if st.get("proc") is not None:
            return True
    except Exception:
        pass
    return False


# Screenshot budgets. While recording is active one long wait beats three short
# blocked attempts: 3 x 5s failures used to trip the 10s health threshold and
# fail the device outright.
SCREENSHOT_TIMEOUT_NORMAL     = 5
SCREENSHOT_TIMEOUT_RECORDING  = 12
SCREENSHOT_RETRIES_RECORDING  = 1
# Continuous-failure threshold for the screenshot class only, while recording.
SCREENSHOT_FAIL_THRESHOLD_RECORDING = 30.0


# ── Event timeline ───────────────────────────────────────────────────────────

def record_event(device: str, event_type: str, **fields) -> None:
    """
    Append one line to events.jsonl.

    Cheap no-op when recording is off — that matters because this is called from
    _raw_tap and is_on_page, which run thousands of times per device.

    Recognised event types:
        page_seen · click · swipe · keyevent · guard_issue · issue · recovery
        task_start · task_done · task_failed · prepare_target_app_start · prepare_target_app_done
        recording_segment · recording_error · phase

    Never raises: instrumentation must not be able to break a run.
    """
    if not _RECORD_ENABLED.get(device):
        return
    path = _EVENT_PATH.get(device)
    if not path:
        return

    try:
        state = _RECORD_STATE.get(device) or {}
        t0    = state.get("t0") or time.time()
        now   = time.time()
        entry = {
            "ts":        _dt.datetime.now().isoformat(timespec="milliseconds"),
            "elapsed_s": round(now - t0, 3),
            "device":    device,
            "type":      event_type,
        }
        for k, v in fields.items():
            if v is None:
                continue
            entry[k] = v if isinstance(v, (str, int, float, bool, list, dict)) else str(v)

        line = json.dumps(entry, ensure_ascii=False)
        with _EVENT_LOCK:
            with open(path, "a", encoding="utf-8") as f:
                f.write(line + "\n")
            state["event_count"] = state.get("event_count", 0) + 1
            counts = state.setdefault("type_counts", {})
            counts[event_type] = counts.get(event_type, 0) + 1
    except Exception:
        # Silent by design. A failure to log an event must never surface as a
        # bot error, and logging the logging failure risks an infinite loop.
        pass


def _record_event_from_slog(device: str, fn: str, phase: str, msg: str,
                            fields: dict) -> None:
    """
    Bridge from _slog() into the event timeline.

    _slog is the single structured-logging call used across the whole setup
    flow, so hooking it here captures phase transitions, guard handling and
    recovery decisions without touching any individual call site.
    """
    if not _RECORD_ENABLED.get(device):
        return
    low = (msg or "").lower()
    if "guard issue" in low or "detected" in low:
        etype = "guard_issue"
    elif any(w in low for w in ("recover", "escalat", "reopen", "reinstall",
                                "restart", "pause")):
        etype = "recovery"
    else:
        etype = "phase"
    record_event(device, etype, fn=fn, phase=phase, message=msg,
                 **{k: v for k, v in (fields or {}).items() if k != "counters"})


# ── Video capture ────────────────────────────────────────────────────────────

KEEP_SEGMENTS_AFTER_MERGE = True   # keep raw segments alongside full_recording.mp4


def _record_remote_path(device: str, seg: int) -> str:
    return f"/sdcard/target_app_rec_{_sanitize_device_id(device)}_{seg:04d}.mp4"


def _which(tool: str) -> "str | None":
    """Locate an external tool without requiring it to be installed."""
    try:
        import shutil
        return shutil.which(tool)
    except Exception:
        return None


def _mp4_is_valid(path: str, dlog=None) -> tuple:
    """
    Decide whether a pulled MP4 is actually playable.

    "File exists and is non-zero" is NOT enough: a screenrecord that was killed
    rather than interrupted writes frame data with no `moov` atom, producing a
    multi-megabyte file that no player can open. That is exactly how an invalid
    segment_0004.mp4 ended up counted as saved.

    Two checks, cheapest last:
      1. ffprobe, when available — authoritative, reports a real duration
      2. moov-atom scan — works everywhere, no dependencies

    Returns (ok: bool, reason: str, duration: float|None).
    """
    if not path or not os.path.exists(path):
        return (False, "file missing", None)
    try:
        size = os.path.getsize(path)
    except Exception as exc:
        return (False, f"stat failed: {exc}", None)
    if size <= 0:
        return (False, "zero-byte file", None)
    if size < 8192:
        return (False, f"file too small ({size} bytes)", None)

    ffprobe = _which("ffprobe")
    if ffprobe:
        try:
            r = subprocess.run(
                [ffprobe, "-v", "error", "-show_entries", "format=duration",
                 "-of", "default=noprint_wrappers=1:nokey=1", path],
                capture_output=True, text=True, timeout=30)
            out = (r.stdout or "").strip()
            if r.returncode == 0 and out:
                try:
                    dur = float(out)
                except ValueError:
                    dur = 0.0
                if dur > 0.05:
                    return (True, f"ffprobe ok ({dur:.1f}s)", dur)
                return (False, f"ffprobe duration {dur}", dur)
            return (False, f"ffprobe rc={r.returncode} "
                           f"{(r.stderr or '').strip()[:100]}", None)
        except Exception as exc:
            if dlog:
                dlog.debug(f"[RECORD] ffprobe failed on {path}: {exc!r}")

    # No ffprobe: look for the moov atom directly. screenrecord writes it last,
    # so its absence means the file was never finalised.
    try:
        with open(path, "rb") as f:
            head = f.read(4 * 1024 * 1024)
            f.seek(max(0, size - 4 * 1024 * 1024))
            tail = f.read(4 * 1024 * 1024)
        if b"moov" in head or b"moov" in tail:
            return (True, "moov atom present", None)
        return (False, "moov atom missing — file not finalised", None)
    except Exception as exc:
        return (False, f"read failed: {exc}", None)


def _record_wait_adb_back(device: str, dlog, timeout: float = 90.0) -> bool:
    """
    Wait for ADB to come back before giving up on a segment.

    ADB drops routinely while the VPN tunnel is being established or changed,
    and a pull attempted in that window fails through no fault of the recording.
    """
    t0 = time.time()
    while time.time() - t0 < timeout:
        if _stop_requested():
            return False
        try:
            if _device_exists_in_adb(device) and _adb_ping(device):
                if time.time() - t0 > 1.0:
                    dlog.info(f"[RECORD] {device} | ADB back after "
                              f"{time.time() - t0:.0f}s")
                return True
        except Exception:
            pass
        try:
            _adb_connect_quiet(device)
        except Exception:
            pass
        time.sleep(2.0)
    dlog.warning(f"[RECORD] {device} | ADB did not return within {timeout:.0f}s")
    return False


def _record_remote_size(device: str, remote: str) -> int:
    """Size of the device-side file, or -1 when it cannot be read."""
    try:
        out = _adb_shell(device, "stat", "-c", "%s", remote, timeout=10) or ""
        out = out.strip().splitlines()[-1].strip() if out.strip() else ""
        return int(out) if out.isdigit() else -1
    except Exception:
        return -1


# How long the recorder waits for Android to report a foreground activity before
# starting the FIRST segment. Generous, because it only costs a slow-booting
# device a few seconds and the alternative is a lost recording.
RECORD_ACTIVITY_READY_TIMEOUT = 120.0
RECORD_MISSING_PROBES         = 3      # existence probes before declaring "missing"
RECORD_STDERR_LOG_LIMIT       = 32768  # last 32 KB of screenrecord stderr


def _record_activity_ready(activity: str) -> bool:
    """
    True when a foreground activity string means the UI is genuinely up.

    Rejects three things:
      * empty            — dumpsys had no mCurrentFocus at all
      * "null"           — mCurrentFocus=null, nothing focused yet
      * "FallbackHome"   — com.android.settings/.FallbackHome, which is Android's
                           BOOT-TIME placeholder home. It is a real, non-null
                           activity, which is why the first version of this gate
                           accepted it after 0.1s on localhost:9035 — and then
                           screenrecord failed because the device was still
                           booting. A device showing FallbackHome has not
                           finished starting.
    """
    act = (activity or "").strip()
    if not act:
        return False
    low = act.lower()
    return "null" not in low and "fallbackhome" not in low


def _record_storage_ready(device: str, dlog=None) -> bool:
    """
    True only when /sdcard is a mounted directory that can actually be WRITTEN.

    This is the condition that really failed. The live log said so directly:

        screenrecord: Unable to open '/sdcard/target_app_rec_localhost_9035_0001.mp4':
                      No such file or directory

    Existence is not enough and neither is the activity state — the check has to
    create a file and delete it again, because that is exactly what screenrecord
    is about to do.

    Deliberately NOT using _adb_shell(): it returns stdout only and swallows the
    exit status, so a failed `touch` would look identical to a successful one.
    subprocess.run is used directly so the return code decides.

    Never creates /sdcard. If the real mount is missing, `mkdir` would produce a
    writable directory on the read-only rootfs or on tmpfs, screenrecord would
    happily fill it, and the pull would then read from a path the system later
    shadows with the real mount. Absent means not ready, full stop.
    """
    probe = (f"/sdcard/.target_app_recprobe_{_sanitize_device_id(device)}_"
             f"{os.getpid()}_{_threading.get_ident()}")
    # One shell round-trip. `&&` means the exit status is non-zero if the
    # directory is missing OR the file cannot be created.
    cmd = f"test -d /sdcard && touch {probe} && rm -f {probe}"
    try:
        r = subprocess.run(["adb", "-s", device, "shell", cmd],
                           capture_output=True, text=True, timeout=10)
        ok = (r.returncode == 0)
    except Exception as exc:
        if dlog is not None:
            try:
                dlog.debug(f"[RECORD] {device} | storage probe raised: {exc!r}")
            except Exception:
                pass
        return False
    if not ok:
        # Best-effort cleanup: `touch` may have succeeded and `rm` failed.
        try:
            subprocess.run(["adb", "-s", device, "shell", f"rm -f {probe}"],
                           capture_output=True, text=True, timeout=5)
        except Exception:
            pass
    return ok


def _record_wait_foreground_activity(device: str, dlog, stop_ev,
                                     timeout: float = RECORD_ACTIVITY_READY_TIMEOUT
                                     ) -> str:
    """
    Block the RECORDER THREAD until the device can actually be recorded.

    ADB accepting a connection is not the same as the device being ready, and a
    foreground activity on its own is not either. Both conditions must hold:

      1. a real foreground activity — not empty, not null, not FallbackHome
      2. /sdcard mounted and writable, proven by creating and deleting a file

    Returns "ready" / "stopped" / "timeout". A timeout still starts the segment,
    since best-effort recording beats none — it just logs which condition was
    still unmet.

    This runs on the recorder daemon thread ONLY. device_worker and prepare_target_app
    never wait for it: start_device_recording() stays exactly where it is, so
    setup_device, setup_vpn and setup_target_app are still recorded.
    """
    t0 = time.time()
    last_state = None
    while True:
        if stop_ev.is_set() or _stop_requested():
            return "stopped"

        try:
            act = (_get_current_activity(device) or "").strip()
        except Exception:
            act = ""
        act_ok = _record_activity_ready(act)
        # Only probe storage once the UI is up: it costs an adb round-trip, and
        # a device still on FallbackHome is not going to be recorded regardless.
        sd_ok = _record_storage_ready(device, dlog) if act_ok else False

        if act_ok and sd_ok:
            dlog.info(f"[RECORD] {device} | recording readiness complete "
                      f"activity={act!r} sdcard_ready=True "
                      f"waited={time.time() - t0:.1f}s")
            return "ready"

        # Log each DISTINCT state once instead of the same line every second.
        fallback = "fallbackhome" in (act or "").lower()
        state = (act, fallback, sd_ok)
        if state != last_state:
            dlog.info(f"[RECORD] {device} | recording waiting for readiness "
                      f"activity={act!r} fallback_home={str(fallback).lower()} "
                      f"sdcard_ready={str(bool(sd_ok)).lower()}")
            last_state = state

        if time.time() - t0 >= timeout:
            missing = []
            if not act_ok:
                missing.append("fallback_home" if fallback else f"activity={act!r}")
            if not sd_ok:
                missing.append("sdcard_not_writable")
            dlog.warning(f"[RECORD] {device} | readiness not reached after "
                         f"{timeout:.0f}s (still missing: {', '.join(missing)}) "
                         f"— starting screenrecord anyway")
            return "timeout"
        # stop_ev.wait doubles as the poll interval, so a stop is noticed at once.
        if stop_ev.wait(timeout=1.0):
            return "stopped"


def _record_drain_stderr(err_file, limit: int = RECORD_STDERR_LOG_LIMIT) -> str:
    """
    Read and CLOSE a screenrecord stderr temp file.

    screenrecord's stderr used to go to an undrained subprocess.PIPE, which threw
    the only explanation of a failure away — and left proc.wait() exposed to the
    documented full-pipe deadlock. A temp file has neither problem: the kernel
    never blocks the writer, and the text is still here after the process exits.

    Only the LAST `limit` bytes are returned; a spinning encoder can produce a
    lot of repeated output and none of it is worth more than the tail.
    """
    if err_file is None:
        return ""
    try:
        try:
            size = err_file.seek(0, os.SEEK_END)
            err_file.seek(max(0, size - limit), os.SEEK_SET)
            raw = err_file.read() or b""
        except Exception:
            return ""
        return raw.decode("utf-8", errors="replace").strip()
    finally:
        try:
            err_file.close()
        except Exception:
            pass


def _record_wait_remote_stable(device: str, dlog, remote: str,
                               timeout: float = 30.0,
                               probes: int = RECORD_MISSING_PROBES) -> tuple:
    """
    Decide what the device-side MP4 is doing.  Returns (status, last_size):

        "stable"   two identical positive size readings — safe to pull
        "missing"  the path is absent; screenrecord never created it
        "unstable" it exists but never settled inside `timeout`

    The "missing" case has to be separated out. This function is only called
    once screenrecord has exited AND _record_wait_adb_back has confirmed ADB, so
    a path that is still absent is not coming back — yet the old code treated
    size=-1 exactly like "not flushed yet", burned the full 30s, and then let
    _record_pull_segment repeat the whole thing twice more. That cost 96s of a
    110s device run on localhost:8955.

    Pulling while screenrecord is still flushing produces a truncated file, so
    the existing two-identical-readings rule is kept for files that do exist.
    """
    # Quick existence probes first: ~1s to tell "absent" from "still writing".
    last = -1
    for i in range(max(1, probes)):
        last = _record_remote_size(device, remote)
        if last >= 0:
            break
        if i < probes - 1:
            time.sleep(0.5)
    else:
        dlog.warning(f"[RECORD] {device} | remote file absent after "
                     f"{probes} probes — screenrecord created nothing")
        return ("missing", -1)

    t0 = time.time()
    stable = 0
    while time.time() - t0 < timeout:
        size = _record_remote_size(device, remote)
        if size < 0:
            time.sleep(1.0)
            continue
        if size == last and size > 0:
            stable += 1
            if stable >= 2:
                dlog.info(f"[RECORD] {device} | remote file stable at {size} bytes")
                return ("stable", size)
        else:
            stable = 0
        last = size
        time.sleep(1.0)
    dlog.warning(f"[RECORD] {device} | remote size never stabilised "
                 f"(last={last}) after {timeout:.0f}s")
    return ("unstable", last)


def _record_kill_device_side(device: str, dlog) -> None:
    """
    Stop the device-side screenrecord cleanly.

    screenrecord finalises its MP4 on SIGINT.  Killing the local adb client
    instead would leave the device still recording and the file unplayable, so
    always signal the process on the device.
    """
    for cmd in (("pkill", "-2", "screenrecord"),
                ("killall", "-2", "screenrecord"),
                ("pkill", "screenrecord")):
        try:
            _adb_shell(device, *cmd, timeout=5)
        except Exception:
            continue
        break
    time.sleep(1.5)   # let it flush the MP4 trailer


def _record_pull_segment(device: str, dlog, remote: str, local: str) -> tuple:
    """
    Pull one finished segment, validate it, and only then delete the remote copy.

    Order matters. The previous version deleted the device-side file
    unconditionally and treated "exists and non-zero" as success, so a transient
    ADB drop during a VPN transition destroyed the only good copy AND counted the
    result as saved.

    Now: wait for ADB -> wait for the remote file to stop growing -> pull (with
    retries) -> validate -> delete only on a confirmed-valid local file.

    Returns (ok, reason, duration).
    """
    attempts = 3
    last_reason = "not attempted"

    for attempt in range(1, attempts + 1):
        if _stop_requested():
            return (False, "manual stop", None)

        if not _record_wait_adb_back(device, dlog, timeout=90.0):
            last_reason = "ADB offline"
            dlog.warning(f"[RECORD] {device} | pull attempt {attempt}/{attempts}: "
                         f"ADB offline — keeping remote file for a later retry")
            continue

        status, _last_size = _record_wait_remote_stable(device, dlog, remote,
                                                        timeout=30.0)
        if status == "missing":
            # screenrecord exited without producing a file and ADB is up, so the
            # path is not going to appear. Do NOT pull and do NOT spend two more
            # attempts re-confirming it: return now, and let _record_worker roll
            # to a fresh segment. Deliberately worded WITHOUT "unrecoverable" so
            # it counts toward the consecutive-failure limit — repeated missing
            # files mean screenrecord itself is unavailable, which is not the
            # same as the moov-atom casualty of a VPN tunnel transition.
            reason = ("remote file missing after screenrecord exited — "
                      "nothing was created, so a pull retry cannot help")
            dlog.error(f"[RECORD] {device} | {reason}")
            return (False, reason, None)

        try:
            r = subprocess.run(["adb", "-s", device, "pull", remote, local],
                               capture_output=True, text=True,
                               timeout=_RECORD_PULL_TIMEOUT)
            if r.returncode != 0:
                last_reason = (f"pull rc={r.returncode} "
                               f"{(r.stderr or '').strip()[:120]}")
                dlog.warning(f"[RECORD] {device} | pull attempt {attempt}/{attempts} "
                             f"failed: {last_reason}")
                time.sleep(2.0)
                continue
        except Exception as exc:
            last_reason = f"pull raised: {exc}"
            dlog.warning(f"[RECORD] {device} | pull attempt {attempt}/{attempts} "
                         f"raised: {exc!r}")
            time.sleep(2.0)
            continue

        ok, reason, dur = _mp4_is_valid(local, dlog)
        if ok:
            dlog.info(f"[RECORD] {device} | segment validated: {reason}")
            try:
                _adb_shell(device, "rm", "-f", remote, timeout=10)
            except Exception:
                pass
            return (True, reason, dur)

        last_reason = reason
        try:
            os.remove(local)
        except Exception:
            pass

        # D5(a): the pull SUCCEEDED but the file has no moov atom.
        #
        # That means screenrecord died without finalising — which is exactly what
        # happens when ADB drops during the tun0 transition. The bytes on the
        # device are already final and broken, so pulling the same file again can
        # only produce the same broken file. Retrying twice more wasted ~11s and
        # still lost the segment.
        #
        # Give up on THIS segment immediately, delete the dead remote file so
        # /sdcard does not fill, and let the caller roll straight to a new one.
        if "moov atom missing" in reason or "moov atom not found" in reason:
            dlog.warning(
                f"[RECORD] {device} | segment is unrecoverable ({reason}) — "
                f"screenrecord died without finalising, most likely the ADB drop "
                f"during the VPN tunnel transition. Not retrying; rolling to a "
                f"new segment."
            )
            try:
                _adb_shell(device, "rm", "-f", remote, timeout=10)
            except Exception:
                pass
            return (False, f"{reason} (unrecoverable — rolled to a new segment)", None)

        # Anything else (partial transfer, truncated read) may genuinely differ
        # on a retry, so those still get the full attempt budget.
        dlog.warning(f"[RECORD] {device} | pulled file INVALID "
                     f"(attempt {attempt}/{attempts}): {reason} — remote kept")
        time.sleep(2.0)

    dlog.error(f"[RECORD] {device} | segment could not be retrieved as a valid "
               f"MP4: {last_reason} (remote file left in place)")
    return (False, last_reason, None)


def _record_worker(device: str, dlog, state: dict) -> None:
    """
    Background segment loop.

    Runs entirely on its own adb invocations so it never blocks a tap, and
    tolerates every failure: one bad segment is logged and the loop continues,
    because a partial recording is still useful and the run must not care.
    """
    stop_ev = state["stop_event"]
    folder  = state["folder"]
    seg     = 0
    fails   = 0

    dlog.info(f"[RECORD] {device} | segment loop started -> {folder}")

    # ── Segment 1 only: wait for the display subsystem ────────────────────────
    # Purely a recorder-thread wait. The automation is already running; nothing
    # in device_worker or prepare_target_app blocks on this, and no failure counter is
    # touched while waiting — an emulator that is slow to draw is not a recorder
    # fault.
    if _record_wait_foreground_activity(device, dlog, stop_ev) == "stopped":
        dlog.info(f"[RECORD] {device} | stop requested while waiting for the "
                  f"display — recorder exiting without starting a segment")
        return

    while not stop_ev.is_set():
        seg += 1
        remote = _record_remote_path(device, seg)
        local  = os.path.join(folder, f"segment_{seg:04d}.mp4")
        t_seg  = time.time()
        err_file = None

        try:
            # stderr goes to a temp FILE, never an undrained PIPE: the kernel
            # cannot block the writer, so proc.wait() below is safe, and the
            # text survives the process for logging. stdout is discarded —
            # screenrecord only prints progress there.
            err_file = tempfile.TemporaryFile(mode="w+b")
            proc = subprocess.Popen(
                ["adb", "-s", device, "shell", "screenrecord",
                 "--time-limit", str(RECORD_SEGMENT_SECONDS),
                 "--bit-rate", RECORD_BIT_RATE,
                 "--size", RECORD_SIZE,
                 remote],
                stdout=subprocess.DEVNULL, stderr=err_file,
            )
        except Exception as exc:
            _record_drain_stderr(err_file)      # closes the handle
            fails += 1
            dlog.warning(f"[RECORD] {device} | segment {seg} could not start: {exc!r}")
            record_event(device, "recording_error", segment=seg, error=str(exc))
            if fails >= 3:
                dlog.error(f"[RECORD] {device} | 3 consecutive start failures — giving up")
                state["failed"] = True
                state["error"]  = f"screenrecord would not start: {exc}"
                return
            if stop_ev.wait(timeout=5.0):
                return
            continue

        state["proc"] = proc

        # ── This thread OWNS stopping the active screenrecord ─────────────────
        # stop_device_recording() only sets the stop event and joins; if it also
        # killed screenrecord we would race this loop, and a kill landing between
        # the poll and the pull is what truncates the final MP4.
        while proc.poll() is None:
            if stop_ev.wait(timeout=1.0):
                dlog.info(f"[RECORD] {device} | stop requested during segment {seg} "
                          f"— sending device-side SIGINT")
                _record_kill_device_side(device, dlog)
                break
        try:
            # screenrecord needs a moment after SIGINT to write the moov atom.
            proc.wait(timeout=30)
        except Exception:
            dlog.warning(f"[RECORD] {device} | screenrecord did not exit in 30s — killing client")
            try:
                proc.kill()
            except Exception:
                pass
        finally:
            state["proc"] = None

        # Read the encoder's own account of what happened, now that it has
        # exited. This is the diagnostic that was missing: when a segment died
        # in ~2s without creating a file, the reason went into an unread pipe
        # and had to be inferred from timestamps instead of simply read.
        seg_rc     = proc.returncode
        seg_stderr = _record_drain_stderr(err_file)   # also closes the handle
        err_file   = None
        if seg_stderr:
            dlog.warning(f"[RECORD] {device} | segment {seg} screenrecord stderr "
                         f"(rc={seg_rc}): {seg_stderr}")

        pulled, reason, probe_dur = _record_pull_segment(device, dlog, remote, local)
        dur = time.time() - t_seg

        if pulled:
            fails = 0
            try:
                size_mb = os.path.getsize(local) / (1024 * 1024)
            except Exception:
                size_mb = 0.0
            state.setdefault("segments", []).append({
                "index": seg,
                "file": os.path.basename(local),
                "path": local,
                "seconds": round(probe_dur if probe_dur else dur, 1),
                "size_mb": round(size_mb, 2),
                "valid": True,
                "validation": reason,
            })
            dlog.info(
                f"[RECORD] {device} | segment {seg} saved and validated "
                f"({dur:.0f}s, {size_mb:.1f}MB) -> {os.path.basename(local)}"
            )
            record_event(device, "recording_segment", segment=seg,
                         file=os.path.basename(local), seconds=round(dur, 1),
                         size_mb=round(size_mb, 2), valid=True)
        else:
            unrecoverable = "unrecoverable" in (reason or "")
            # screenrecord's own words, trimmed for the manifest and the report.
            short_err = (seg_stderr or "").replace("\n", " ")[:500]
            # Recorded explicitly so the manifest and report can name the bad
            # segment and why, instead of silently under-reporting.
            failed_rec = {
                "index": seg,
                "file": os.path.basename(local),
                "reason": reason,
                "valid": False,
                "returncode": seg_rc,
            }
            if short_err:
                failed_rec["stderr"] = short_err
            state.setdefault("failed_segments", []).append(failed_rec)
            state["incomplete"] = True
            _err_kw = {"stderr": short_err} if short_err else {}
            record_event(device, "recording_error", segment=seg,
                         error=reason, valid=False,
                         unrecoverable=unrecoverable,
                         returncode=seg_rc, **_err_kw)

            if unrecoverable:
                # A tunnel-transition casualty, not a sign the recorder is
                # broken. Do NOT count it toward the 3-strike give-up — one lost
                # segment must not end recording for the whole run.
                dlog.warning(
                    f"[RECORD] {device} | segment {seg} lost ({reason}) — "
                    f"not counted as a recorder failure; waiting for ADB to "
                    f"settle, then starting a fresh segment")
                _record_wait_adb_back(device, dlog, timeout=90.0)
                if stop_ev.wait(timeout=1.0):
                    return
                continue

            fails += 1
            dlog.warning(f"[RECORD] {device} | segment {seg} INVALID/not retrieved: "
                         f"{reason} (consecutive failures: {fails})")
            if fails >= 3:
                dlog.error(f"[RECORD] {device} | 3 consecutive failures — stopping recorder")
                state["failed"] = True
                state["error"]  = f"3 consecutive segment failures (last: {reason})"
                return

    dlog.info(f"[RECORD] {device} | segment loop exited after {seg} segment(s)")


def _record_merge_segments(device: str, dlog, state: dict) -> dict:
    """
    Concatenate the VALID segments into a single full_recording.mp4.

    Android's screenrecord has a per-invocation time limit, so a run is always a
    pile of segments — awkward to review. ffmpeg's concat demuxer stitches them
    without re-encoding (stream copy), so this is fast and lossless.

    Only validated segments are included: feeding a truncated file to concat
    produces a broken output, which would be worse than no merge at all.
    ffmpeg is optional — when it is absent the segments are simply left as-is.

    Returns {"merged", "file", "reason", "inputs"}.
    """
    out = {"merged": False, "file": "", "reason": "", "inputs": 0}
    segs = [sg for sg in state.get("segments", []) if sg.get("valid")]
    if not segs:
        out["reason"] = "no valid segments to merge"
        return out

    ffmpeg = _which("ffmpeg")
    if not ffmpeg:
        out["reason"] = "ffmpeg not available — segments left unmerged"
        dlog.info(f"[RECORD] {device} | {out['reason']}")
        return out

    folder = state["folder"]
    target = os.path.join(folder, "full_recording.mp4")
    listf  = os.path.join(folder, "_concat_list.txt")

    try:
        with open(listf, "w", encoding="utf-8") as f:
            for sg in sorted(segs, key=lambda x: x.get("index", 0)):
                path = sg.get("path") or os.path.join(folder, sg["file"])
                # concat demuxer wants forward slashes and escaped quotes
                safe = os.path.abspath(path).replace("\\", "/").replace("'", "'\\''")
                f.write(f"file '{safe}'\n")

        t0 = time.time()
        r = subprocess.run(
            [ffmpeg, "-y", "-f", "concat", "-safe", "0", "-i", listf,
             "-c", "copy", target],
            capture_output=True, text=True, timeout=600)

        if r.returncode == 0:
            ok, reason, dur = _mp4_is_valid(target, dlog)
            if ok:
                size_mb = os.path.getsize(target) / (1024 * 1024)
                out.update(merged=True, file="full_recording.mp4",
                           reason=f"{len(segs)} segment(s) merged ({reason})",
                           inputs=len(segs))
                dlog.info(f"[RECORD] {device} | merged {len(segs)} segment(s) into "
                          f"full_recording.mp4 ({size_mb:.1f}MB, "
                          f"{time.time() - t0:.0f}s)")
                record_event(device, "recording_segment", segment=0,
                             file="full_recording.mp4", merged=True,
                             inputs=len(segs), size_mb=round(size_mb, 2))
            else:
                out["reason"] = f"merged file failed validation: {reason}"
                dlog.warning(f"[RECORD] {device} | {out['reason']}")
        else:
            out["reason"] = f"ffmpeg rc={r.returncode} {(r.stderr or '').strip()[:160]}"
            dlog.warning(f"[RECORD] {device} | merge failed: {out['reason']}")
    except Exception as exc:
        out["reason"] = f"merge raised: {exc}"
        dlog.warning(f"[RECORD] {device} | {out['reason']}")
    finally:
        try:
            if os.path.exists(listf):
                os.remove(listf)
        except Exception:
            pass
        if out["merged"] and not KEEP_SEGMENTS_AFTER_MERGE:
            for sg in segs:
                try:
                    os.remove(sg.get("path") or os.path.join(folder, sg["file"]))
                except Exception:
                    pass
            dlog.info(f"[RECORD] {device} | raw segments removed "
                      f"(KEEP_SEGMENTS_AFTER_MERGE=False)")

    return out


def start_device_recording(device: str, dlog=None, record_video: bool = True):
    """
    Begin recording for one device run.

    Creates recordings/run_<timestamp>/<safe_device_id>/ and starts the event
    timeline immediately, then starts the video thread.  The event log is set up
    first and independently, so a device with no working screenrecord still
    produces a full timeline and report.

    Returns the folder path, or None if nothing could be started.  Never raises.
    """
    if dlog is None:
        dlog = _get_device_logger(device)
    if not record_video:
        _RECORD_ENABLED[device] = False
        return None

    try:
        run_id = _recording_run_id()
        folder = os.path.join(RECORDINGS_ROOT, f"run_{run_id}",
                              _sanitize_device_id(device))
        os.makedirs(folder, exist_ok=True)

        state = {
            "folder":      folder,
            "run_id":      run_id,
            "t0":          time.time(),
            "started_at":  _dt.datetime.now().isoformat(timespec="seconds"),
            "segments":        [],
            "failed_segments": [],
            "incomplete":      False,
            "merge":           {},
            "event_count": 0,
            "type_counts": {},
            "failed":      False,
            "error":       "",
            "stop_event":  _threading.Event(),
            "proc":        None,
            "thread":      None,
        }
        _RECORD_STATE[device] = state
        _EVENT_PATH[device]   = os.path.join(folder, "events.jsonl")

        # Truncate any stale file from a previous run in the same folder.
        with open(_EVENT_PATH[device], "w", encoding="utf-8") as f:
            f.write("")

        _RECORD_ENABLED[device] = True
        record_event(device, "phase", fn="start_device_recording",
                     phase="recording", message="recording started",
                     folder=folder, run_id=run_id)

        t = _threading.Thread(target=_record_worker, args=(device, dlog, state),
                              daemon=True, name=f"record_{_sanitize_device_id(device)}")
        state["thread"] = t
        t.start()

        dlog.info(f"[RECORD] {device} | recording enabled -> {folder}")
        print(f"[{device}] Recording -> {folder}")
        return folder

    except Exception as exc:
        # A recording failure must never fail the run.
        dlog.warning(f"[RECORD] {device} | could not start recording: {exc!r}")
        try:
            append_issue(device, "video_recording_failed", f"start failed: {exc}",
                         fn="start_device_recording", phase="recording")
        except Exception:
            pass
        _RECORD_ENABLED[device] = False
        return None


def stop_device_recording(device: str, dlog=None) -> dict:
    """
    Stop recording, pull the final segment, and write the manifest + report.

    Safe to call unconditionally in a finally block — returns an empty dict when
    recording was never enabled.  Never raises.
    """
    if dlog is None:
        dlog = _get_device_logger(device)
    state = _RECORD_STATE.get(device)
    if not state:
        return {}

    result = {}
    try:
        record_event(device, "phase", fn="stop_device_recording",
                     phase="recording", message="recording stopping")

        # Signal and JOIN only. The recorder thread owns SIGINT-ing screenrecord;
        # killing it from here as well raced the thread's own stop and truncated
        # the final segment.
        state["stop_event"].set()

        t = state.get("thread")
        if t is not None:
            # Generous: the thread still has to SIGINT, wait for a stable remote
            # file, pull it, and validate it.
            t.join(timeout=_RECORD_PULL_TIMEOUT + 120)
            if t.is_alive():
                dlog.warning(f"[RECORD] {device} | recorder thread did not exit in "
                             f"time — sending device-side SIGINT as a last resort")
                _record_kill_device_side(device, dlog)
                t.join(timeout=60)
                if t.is_alive():
                    dlog.error(f"[RECORD] {device} | recorder thread still running")

        state["ended_at"]   = _dt.datetime.now().isoformat(timespec="seconds")
        state["duration_s"] = round(time.time() - state["t0"], 1)

        # Merge only after the thread has stopped, so the segment list is final.
        try:
            state["merge"] = _record_merge_segments(device, dlog, state)
        except Exception as exc:
            dlog.warning(f"[RECORD] {device} | merge step raised: {exc!r}")
            state["merge"] = {"merged": False, "reason": str(exc)}

        # ── Classify BEFORE the manifest and report are written ───────────────
        # They read state["failed"] / state["incomplete"], so the final verdict
        # has to be in place first.
        #
        # These used to be the same value, which made a useful recording
        # indistinguishable from no recording at all: localhost:9035 kept 101s of
        # video across 2 valid segments, lost one 2-second segment, and was
        # reported exactly like a device that recorded nothing.
        #
        #   failed      the recorder gave up, or there is no usable video at all
        #   incomplete  failed, or at least one segment was lost along the way
        bad              = state.get("failed_segments", [])
        valid_count      = len(state.get("segments", []))
        bad_count        = len(bad)
        recorder_gave_up = bool(state.get("failed"))

        failed     = recorder_gave_up or valid_count == 0
        incomplete = failed or bool(state.get("incomplete")) or bad_count > 0

        state["failed"]     = failed
        state["incomplete"] = incomplete

        manifest = _write_recording_manifest(device, dlog, state)
        report   = build_recording_report(device, dlog, state)

        result = {
            "folder":     state["folder"],
            "segments":   valid_count,
            "events":     state.get("event_count", 0),
            "manifest":   manifest,
            "report":     report,
            "duration_s": state["duration_s"],
            "failed":     failed,
            "incomplete": incomplete,
            "merged":     bool(state.get("merge", {}).get("merged")),
            "full_video": state.get("merge", {}).get("file", ""),
            "error":      state.get("error", ""),
        }

        if failed:
            reason = (state.get("error")
                      or (f"{bad_count} invalid/missing segment(s): "
                          f"{[b['index'] for b in bad]}" if bad else "")
                      or "no video segments were produced")
            dlog.warning(f"[RECORD] {device} | recording FAILED — {reason}")
            try:
                append_issue(device, "video_recording_failed", reason,
                             fn="stop_device_recording", phase="recording")
            except Exception:
                pass
        elif incomplete:
            # Video was still produced, so this is NOT an issue-worthy failure.
            # Recording is a diagnostic; losing part of one must not put a red
            # mark against a device whose run was fine.
            dlog.warning(
                f"[RECORD] {device} | recording partially incomplete — "
                f"{valid_count} valid segment(s) retained, "
                f"{bad_count} segment(s) missing/invalid "
                f"{[b['index'] for b in bad]}"
            )

        dlog.info(
            f"[RECORD] {device} | recording stopped — "
            f"{result['segments']} valid segment(s), {bad_count} bad, "
            f"{result['events']} event(s), {result['duration_s']:.0f}s, "
            f"failed={failed} incomplete={incomplete} "
            f"merged={result['merged']} -> {state['folder']}"
        )
        print(f"[{device}] Recording saved: {state['folder']}")

    except Exception as exc:
        dlog.warning(f"[RECORD] {device} | stop failed: {exc!r}")
    finally:
        _RECORD_ENABLED[device] = False

    return result


def _write_recording_manifest(device: str, dlog, state: dict) -> str:
    """Write recording_manifest.json describing this device's recording."""
    path = os.path.join(state["folder"], "recording_manifest.json")
    try:
        data = {
            "device":            device,
            "safe_device_id":    _sanitize_device_id(device),
            "run_id":            state.get("run_id"),
            "started_at":        state.get("started_at"),
            "ended_at":          state.get("ended_at"),
            "duration_s":        state.get("duration_s"),
            "segment_seconds":   RECORD_SEGMENT_SECONDS,
            "bit_rate":          RECORD_BIT_RATE,
            "size":              RECORD_SIZE,
            "segments":            state.get("segments", []),
            "segment_count":       len(state.get("segments", [])),
            "failed_segments":     state.get("failed_segments", []),
            "failed_segment_count": len(state.get("failed_segments", [])),
            "event_count":         state.get("event_count", 0),
            "event_type_counts":   state.get("type_counts", {}),
            "events_file":         "events.jsonl",
            # Only VALID segments are listed above; a file that existed but had
            # no moov atom is reported under failed_segments with its reason.
            #
            # Both read the FINAL verdict that stop_device_recording wrote back
            # into state before calling this. Recomputing them here would risk
            # the manifest and the controller disagreeing about the same run.
            "recording_failed":     bool(state.get("failed")),
            "recording_incomplete": bool(state.get("incomplete")),
            "merge":               state.get("merge", {}),
            "full_recording":      state.get("merge", {}).get("file", ""),
            "keep_segments_after_merge": KEEP_SEGMENTS_AFTER_MERGE,
            "error":               state.get("error", ""),
        }
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)
        return path
    except Exception as exc:
        dlog.warning(f"[RECORD] {device} | manifest write failed: {exc!r}")
        return ""


def _read_events(device: str) -> list:
    """Load events.jsonl back as a list of dicts, skipping any malformed line."""
    path = _EVENT_PATH.get(device)
    out  = []
    if not path or not os.path.exists(path):
        return out
    try:
        with open(path, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    out.append(json.loads(line))
                except Exception:
                    continue
    except Exception:
        pass
    return out


def build_recording_report(device: str, dlog, state: dict) -> str:
    """
    Write recording_report.html: the timeline you actually read after a failure.

    Answers, in one place: what page was seen, what button was clicked, at what
    coordinate, on which attempt, whether the click registered, and what
    happened immediately before the run succeeded or failed.

    Falls back to a plain-text report if HTML generation fails for any reason.
    """
    folder = state["folder"]
    events = _read_events(device)

    try:
        clicks = [e for e in events if e.get("type") == "click"]
        pages  = [e for e in events if e.get("type") == "page_seen"]
        issues = [e for e in events if e.get("type") == "issue"]
        tasks  = [e for e in events if e.get("type") in ("task_start", "task_done", "task_failed")]
        recov  = [e for e in events if e.get("type") in ("recovery", "guard_issue")]
        segs   = state.get("segments", [])

        def esc(v):
            return (str(v).replace("&", "&amp;").replace("<", "&lt;")
                    .replace(">", "&gt;").replace('"', "&quot;"))

        def row(e):
            detail = []
            for k in ("page", "button", "coord", "attempt", "result",
                      "registered", "reason", "signal", "task", "message"):
                if e.get(k) not in (None, ""):
                    detail.append(f"<b>{esc(k)}</b>={esc(e[k])}")
            cls = {
                "click": "ev-click", "page_seen": "ev-page", "issue": "ev-issue",
                "recovery": "ev-rec", "guard_issue": "ev-rec",
                "task_done": "ev-ok", "task_failed": "ev-issue",
            }.get(e.get("type"), "")
            return (f"<tr class='{cls}'><td>{esc(e.get('elapsed_s'))}</td>"
                    f"<td>{esc(e.get('type'))}</td>"
                    f"<td>{esc(e.get('fn', ''))}</td>"
                    f"<td>{esc(e.get('phase', ''))}</td>"
                    f"<td>{' &middot; '.join(detail)}</td></tr>")

        seg_rows = "".join(
            f"<tr><td>{s['index']}</td>"
            f"<td><a href='{esc(s['file'])}'>{esc(s['file'])}</a></td>"
            f"<td>{s['seconds']}s</td><td>{s['size_mb']} MB</td>"
            f"<td>{esc(s.get('validation', 'ok'))}</td></tr>"
            for s in segs
        ) or "<tr><td colspan='5'><i>no valid video segments were produced</i></td></tr>"

        bad = state.get("failed_segments", [])
        bad_rows = "".join(
            f"<tr class='ev-issue'><td>{b['index']}</td><td>{esc(b['file'])}</td>"
            f"<td colspan='3'>{esc(b['reason'])}</td></tr>"
            for b in bad
        ) or "<tr><td colspan='5'><i>none</i></td></tr>"

        merge = state.get("merge", {}) or {}
        if merge.get("merged"):
            full_block = (f"<p><b>Full recording:</b> "
                          f"<a href='{esc(merge['file'])}'>{esc(merge['file'])}</a> "
                          f"&mdash; {esc(merge.get('reason', ''))}</p>")
        else:
            full_block = (f"<p><b>Full recording:</b> <i>not merged &mdash; "
                          f"{esc(merge.get('reason', 'ffmpeg not run'))}</i></p>")

        # Everything in the last 60s before the end — the failure context.
        tail = [e for e in events
                if isinstance(e.get("elapsed_s"), (int, float))
                and e["elapsed_s"] >= (state.get("duration_s", 0) - 60)]

        html = f"""<!DOCTYPE html>
<html><head><meta charset="utf-8"><title>Recording report — {esc(device)}</title>
<style>
 body{{font:13px/1.5 system-ui,Segoe UI,Arial;margin:24px;background:#14141f;color:#d8d8e8}}
 h1{{font-size:20px;margin:0 0 4px}} h2{{font-size:15px;margin:26px 0 8px;color:#f47840}}
 .meta{{color:#8888a8;margin-bottom:18px}}
 table{{border-collapse:collapse;width:100%;margin-bottom:10px}}
 th,td{{border:1px solid #2a2a45;padding:4px 8px;text-align:left;vertical-align:top}}
 th{{background:#1e1e32;color:#aaaac8}}
 tr.ev-click{{background:#1b2438}} tr.ev-page{{background:#18231b}}
 tr.ev-issue{{background:#2e1a1a}} tr.ev-rec{{background:#2e2618}} tr.ev-ok{{background:#152a15}}
 a{{color:#7fb2ff}} .cards{{display:flex;gap:14px;flex-wrap:wrap;margin-bottom:8px}}
 .card{{background:#1a1a2c;border:1px solid #2a2a45;border-radius:6px;padding:10px 16px;min-width:110px}}
 .card b{{display:block;font-size:20px;color:#f47840}}
 code{{background:#1a1a2c;padding:1px 5px;border-radius:3px}}
</style></head><body>
<h1>Recording report — {esc(device)}</h1>
<div class="meta">run <code>{esc(state.get('run_id'))}</code> &middot;
 {esc(state.get('started_at'))} &rarr; {esc(state.get('ended_at'))} &middot;
 {esc(state.get('duration_s'))}s</div>

<div class="cards">
 <div class="card"><b>{len(segs)}</b>valid segments</div>
 <div class="card"><b>{len(bad)}</b>bad segments</div>
 <div class="card"><b>{len(events)}</b>events</div>
 <div class="card"><b>{len(clicks)}</b>clicks</div>
 <div class="card"><b>{len(pages)}</b>pages seen</div>
 <div class="card"><b>{len(issues)}</b>issues</div>
 <div class="card"><b>{len(recov)}</b>recoveries</div>
</div>

<h2>Video</h2>
{full_block}
<table><tr><th>#</th><th>File</th><th>Length</th><th>Size</th><th>Validation</th></tr>
{seg_rows}</table>

<h2>Failed / invalid segments</h2>
<table><tr><th>#</th><th>File</th><th colspan="3">Why it was rejected</th></tr>
{bad_rows}</table>

<h2>Task results</h2>
<table><tr><th>t+s</th><th>Type</th><th>Fn</th><th>Phase</th><th>Detail</th></tr>
{''.join(row(e) for e in tasks) or "<tr><td colspan='5'><i>none</i></td></tr>"}</table>

<h2>Issues</h2>
<table><tr><th>t+s</th><th>Type</th><th>Fn</th><th>Phase</th><th>Detail</th></tr>
{''.join(row(e) for e in issues) or "<tr><td colspan='5'><i>none</i></td></tr>"}</table>

<h2>Guard / recovery actions</h2>
<table><tr><th>t+s</th><th>Type</th><th>Fn</th><th>Phase</th><th>Detail</th></tr>
{''.join(row(e) for e in recov[:200]) or "<tr><td colspan='5'><i>none</i></td></tr>"}</table>

<h2>Clicks — page, button, coordinate, attempt, registration</h2>
<table><tr><th>t+s</th><th>Type</th><th>Fn</th><th>Phase</th><th>Detail</th></tr>
{''.join(row(e) for e in clicks[:400]) or "<tr><td colspan='5'><i>none</i></td></tr>"}</table>

<h2>Last 60 seconds before the run ended</h2>
<table><tr><th>t+s</th><th>Type</th><th>Fn</th><th>Phase</th><th>Detail</th></tr>
{''.join(row(e) for e in tail[-200:]) or "<tr><td colspan='5'><i>none</i></td></tr>"}</table>

<h2>Full timeline</h2>
<table><tr><th>t+s</th><th>Type</th><th>Fn</th><th>Phase</th><th>Detail</th></tr>
{''.join(row(e) for e in events[:3000])}</table>
<p class="meta">Raw event data: <a href="events.jsonl">events.jsonl</a> &middot;
 manifest: <a href="recording_manifest.json">recording_manifest.json</a></p>
</body></html>"""

        path = os.path.join(folder, "recording_report.html")
        with open(path, "w", encoding="utf-8") as f:
            f.write(html)
        return path

    except Exception as exc:
        dlog.warning(f"[RECORD] {device} | HTML report failed ({exc!r}) — writing text")
        try:
            path = os.path.join(folder, "recording_report.txt")
            with open(path, "w", encoding="utf-8") as f:
                f.write(f"Recording report — {device}\n")
                f.write(f"run {state.get('run_id')}  "
                        f"{state.get('started_at')} -> {state.get('ended_at')}\n")
                f.write(f"segments={len(state.get('segments', []))} "
                        f"events={len(events)}\n\n")
                skip = ("ts", "elapsed_s", "device", "type", "fn", "phase")
                for e in events:
                    extra = {k: v for k, v in e.items() if k not in skip}
                    f.write(f"[{e.get('elapsed_s')}s] {e.get('type')} "
                            f"{e.get('fn', '')}/{e.get('phase', '')} {extra}\n")
            return path
        except Exception:
            return ""
# =============================================================================
# UNEXPECTED-PAGE LIBRARY  —  deduplicated, fully background
# -----------------------------------------------------------------------------
# Unknown screens repeat constantly: the same ad, the same event popup, the same
# unmapped dialog, hundreds of times per run. Saving every occurrence produced a
# folder nobody could review. This keeps ONE screenshot per visually distinct
# page and counts the rest.
#
# Everything here runs on a background worker. The automation never waits for a
# diagnostic: submissions are non-blocking, the queue is bounded, and when it is
# full the diagnostic is DROPPED rather than slowing the bot down. Any failure
# is swallowed — a library problem must never fail a device.
#
#   unexpected_pages/library/unlabeled/unexpected_000001.png
#   unexpected_pages/library/metadata.jsonl
#   unexpected_pages/library/labels.json
# =============================================================================

UNEXPECTED_LIB_ROOT      = os.path.join("unexpected_pages", "library")
UNEXPECTED_LIB_IMAGES    = os.path.join(UNEXPECTED_LIB_ROOT, "unlabeled")
UNEXPECTED_LIB_METADATA  = os.path.join(UNEXPECTED_LIB_ROOT, "metadata.jsonl")
UNEXPECTED_LIB_LABELS    = os.path.join(UNEXPECTED_LIB_ROOT, "labels.json")

# dHash on a 16x16 grayscale grid -> 240 bits. Two pages counting as "the same"
# within this many differing bits. 8 is deliberately tight: it merges
# re-captures of one screen but keeps genuinely different dialogs apart.
UNEXPECTED_HASH_SIZE     = 16
UNEXPECTED_HAMMING_MAX   = 8
UNEXPECTED_QUEUE_MAX     = 32

_unexpected_q       = None      # queue.Queue, created lazily
_unexpected_worker  = None
_unexpected_lock    = _threading.Lock()
_unexpected_hashes  = {}        # unique_id -> int hash
_unexpected_counts  = {}        # unique_id -> occurrence count
_unexpected_loaded  = False
_unexpected_dropped = 0


def _dhash_image(img, size: int = UNEXPECTED_HASH_SIZE) -> "int | None":
    """
    Difference hash: grayscale -> (size+1 x size) -> compare adjacent pixels.

    Robust to small rendering differences (timers, animation frames, minor
    colour shifts) while still separating genuinely different layouts.
    """
    try:
        small = img.convert("L").resize((size + 1, size))
        px    = list(small.getdata())
        bits  = 0
        for row in range(size):
            base = row * (size + 1)
            for col in range(size):
                bits = (bits << 1) | (1 if px[base + col] > px[base + col + 1] else 0)
        return bits
    except Exception:
        return None


def _hamming(a: int, b: int) -> int:
    return bin(a ^ b).count("1")


UNEXPECTED_LIB_LOCKFILE   = os.path.join(UNEXPECTED_LIB_ROOT, ".library.lock")
UNEXPECTED_LOCK_TIMEOUT   = 10.0    # diagnostic-only: give up rather than wait
UNEXPECTED_LOCK_STALE     = 60.0    # a lock older than this is assumed abandoned


class _UnexpectedLibLock:
    """
    Exclusive lock across PROCESSES, not just threads.

    Every device runs in its own process but they all share one library folder,
    so `threading.Lock` protects nothing here: two workers could allocate the
    same unexpected_NNNNNN id and overwrite each other's PNG and labels entry.

    Implemented with O_CREAT|O_EXCL, which is atomic on both Windows and POSIX.
    A lock older than UNEXPECTED_LOCK_STALE is treated as abandoned (a worker
    was killed mid-write) and broken, so one crash cannot disable the library
    for the rest of the run.

    Acquisition failure is NOT an error — the job is dropped and the bot
    continues. This only ever runs on the background thread.
    """

    def __init__(self, timeout: float = UNEXPECTED_LOCK_TIMEOUT):
        self.timeout = timeout
        self.fd = None

    def __enter__(self):
        deadline = time.time() + self.timeout
        while time.time() < deadline:
            try:
                os.makedirs(UNEXPECTED_LIB_ROOT, exist_ok=True)
                self.fd = os.open(UNEXPECTED_LIB_LOCKFILE,
                                  os.O_CREAT | os.O_EXCL | os.O_RDWR)
                try:
                    os.write(self.fd, str(os.getpid()).encode())
                except Exception:
                    pass
                return self
            except FileExistsError:
                # Break an abandoned lock rather than stalling the library.
                try:
                    age = time.time() - os.path.getmtime(UNEXPECTED_LIB_LOCKFILE)
                    if age > UNEXPECTED_LOCK_STALE:
                        os.remove(UNEXPECTED_LIB_LOCKFILE)
                        continue
                except Exception:
                    pass
                time.sleep(0.05)
            except Exception:
                return None      # cannot lock at all -> caller drops the job
        return None              # timed out -> caller drops the job

    def __exit__(self, *exc):
        try:
            if self.fd is not None:
                os.close(self.fd)
                os.remove(UNEXPECTED_LIB_LOCKFILE)
        except Exception:
            pass
        return False


def _unexpected_lib_load(force: bool = False) -> None:
    """
    Rebuild the in-memory hash index from metadata.jsonl.

    Called with force=True inside the cross-process lock so this process sees
    ids and hashes written by OTHER device workers before it allocates its own.
    """
    global _unexpected_loaded
    if _unexpected_loaded and not force:
        return
    _unexpected_loaded = True
    if force:
        _unexpected_hashes.clear()
        _unexpected_counts.clear()
    try:
        os.makedirs(UNEXPECTED_LIB_IMAGES, exist_ok=True)
        if not os.path.exists(UNEXPECTED_LIB_METADATA):
            return
        with open(UNEXPECTED_LIB_METADATA, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    rec = json.loads(line)
                except Exception:
                    continue
                uid = rec.get("unique_id")
                h   = rec.get("hash")
                if not uid or h is None:
                    continue
                try:
                    hv = int(h, 16) if isinstance(h, str) else int(h)
                except Exception:
                    continue
                # Later lines are occurrence updates; keep the newest count.
                _unexpected_hashes[uid] = hv
                _unexpected_counts[uid] = max(_unexpected_counts.get(uid, 0),
                                              int(rec.get("occurrence", 1) or 1))
    except Exception:
        pass


def _unexpected_next_id() -> int:
    """
    Highest existing unexpected_NNNNNN across ALL three sources.

    Must be called with the cross-process lock held.

    Checking metadata alone is not enough: a worker killed between saving the
    PNG and appending its metadata line leaves an orphan image, and the next
    allocation would reuse that id and overwrite it. Labels are checked for the
    same reason (stub written before the metadata append).
    """
    top = 0

    def _bump(name: str) -> None:
        nonlocal top
        try:
            if name.startswith("unexpected_"):
                top = max(top, int(name.rsplit("_", 1)[-1].split(".")[0]))
        except Exception:
            pass

    # 1. in-memory index (already refreshed from metadata.jsonl under the lock)
    for k in _unexpected_hashes:
        _bump(k)
    # 2. labels.json keys
    try:
        if os.path.exists(UNEXPECTED_LIB_LABELS):
            with open(UNEXPECTED_LIB_LABELS, "r", encoding="utf-8") as f:
                for k in (json.load(f) or {}):
                    _bump(k)
    except Exception:
        pass
    # 3. PNGs actually on disk — catches orphans from a crashed worker
    try:
        for fn in os.listdir(UNEXPECTED_LIB_IMAGES):
            if fn.startswith("unexpected_") and fn.endswith(".png"):
                _bump(fn)
    except Exception:
        pass
    return top


def _unexpected_lib_append(rec: dict) -> None:
    try:
        os.makedirs(UNEXPECTED_LIB_ROOT, exist_ok=True)
        with open(UNEXPECTED_LIB_METADATA, "a", encoding="utf-8") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
    except Exception:
        pass


def _unexpected_lib_save_png(uid: str, img, device: str = "", dlog=None) -> bool:
    """
    Write unexpected_NNNNNN.png atomically.  True only if the final file exists
    with a non-zero size.

    The caller commits the hash into the deduplication index on the strength of
    this returning True, so a half-written or zero-byte file is worse than no
    file at all: every later occurrence of that screen would be counted against
    an image nobody can open or label, and the page could never be captured
    again. Hence temp file -> size check -> os.replace, rather than saving
    straight to the final name and hoping.
    """
    tmp = ""
    try:
        os.makedirs(UNEXPECTED_LIB_IMAGES, exist_ok=True)
        final = os.path.join(UNEXPECTED_LIB_IMAGES, f"{uid}.png")
        # Leading dot keeps the temp file out of the unexpected_*.png scan in
        # _unexpected_next_id(), and pid+tid keeps two writers apart.
        tmp = os.path.join(
            UNEXPECTED_LIB_IMAGES,
            f".{uid}.{os.getpid()}.{_threading.get_ident()}.tmp.png")
        img.save(tmp, format="PNG")
        if not os.path.exists(tmp) or os.path.getsize(tmp) <= 0:
            raise OSError("temp PNG missing or empty after save")
        os.replace(tmp, final)
        tmp = ""
        if not os.path.exists(final) or os.path.getsize(final) <= 0:
            raise OSError("final PNG missing or empty after replace")
        return True
    except Exception as exc:
        try:
            if tmp and os.path.exists(tmp):
                os.remove(tmp)
        except Exception:
            pass
        if dlog is not None:
            try:
                dlog.debug(f"[PAGE-LIB] {device} | could not save {uid}.png "
                           f"({exc!r}) — page NOT added to the library, so it "
                           f"can still be captured next time")
            except Exception:
                pass
        return False


def _unexpected_lib_label_stub(uid: str, device: str = "", dlog=None) -> None:
    """
    Add an empty entry to labels.json for manual labelling later.

    Deliberately never writes a guessed label and never touches pages.json.

    If the file exists and cannot be parsed, the update is SKIPPED rather than
    replaced with a fresh one-entry dict. That file holds hand-written labels;
    silently erasing them to add one empty stub is not a trade worth making.
    An existing but EMPTY file is treated as {} — there is nothing to lose.
    """
    try:
        data = {}
        if os.path.exists(UNEXPECTED_LIB_LABELS):
            try:
                if os.path.getsize(UNEXPECTED_LIB_LABELS) > 0:
                    with open(UNEXPECTED_LIB_LABELS, "r", encoding="utf-8") as f:
                        data = json.load(f)
            except Exception as exc:
                if dlog is not None:
                    try:
                        dlog.warning(
                            f"[PAGE-LIB] {device} | labels.json is unreadable "
                            f"({exc!r}) — skipping the stub for {uid} rather "
                            f"than overwriting existing manual labels")
                    except Exception:
                        pass
                return
            if not isinstance(data, dict):
                if dlog is not None:
                    try:
                        dlog.warning(
                            f"[PAGE-LIB] {device} | labels.json is not an object "
                            f"({type(data).__name__}) — skipping the stub for "
                            f"{uid} rather than overwriting it")
                    except Exception:
                        pass
                return
        if uid in data:
            return
        data[uid] = {"label": "", "notes": "", "page_name": ""}
        tmp = f"{UNEXPECTED_LIB_LABELS}.{os.getpid()}.tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=1, ensure_ascii=False, sort_keys=True)
        os.replace(tmp, UNEXPECTED_LIB_LABELS)
    except Exception:
        pass


def _unexpected_lib_process(job: dict) -> None:
    """Background handler for one submission. Never raises."""
    try:
        device = job.get("device", "")
        dlog   = job.get("dlog")
        img    = job.get("image")

        # NO device I/O in this worker at all — no screenshot, no activity read,
        # no UIAutomator, no OCR, no adb command of any kind. Every one of those
        # would contend with the automation for the device (screencap in
        # particular shares a per-device lock). The image arrives with the job,
        # already captured by the workflow; the activity string arrives from the
        # caller or stays blank.
        if img is None:
            if dlog is not None:
                dlog.debug(f"[PAGE-LIB] {device} | job has no image — skipped")
            return

        h = _dhash_image(img)
        if h is None:
            return

        # ── Critical section: cross-process AND cross-thread ──────────────
        # Reload -> duplicate check -> id allocation -> PNG -> metadata ->
        # labels must be atomic against every other device worker, otherwise two
        # processes hand out the same unexpected_NNNNNN and clobber each other.
        with _unexpected_lock:                       # threads in THIS process
            with _UnexpectedLibLock() as xlock:      # all OTHER processes
                if xlock is None:
                    if dlog is not None:
                        dlog.debug(f"[PAGE-LIB] {device} | could not take the "
                                   f"library lock — dropping this diagnostic")
                    return

                # Re-read metadata written by other workers since we last looked.
                _unexpected_lib_load(force=True)

                match, best = None, 10 ** 9
                for uid, known in _unexpected_hashes.items():
                    d = _hamming(h, known)
                    if d < best:
                        match, best = uid, d
                duplicate = match is not None and best <= UNEXPECTED_HAMMING_MAX

                if duplicate:
                    _unexpected_counts[match] = _unexpected_counts.get(match, 1) + 1
                    occ, uid, sim = _unexpected_counts[match], match, match
                else:
                    # Only a visually NEW page costs a PNG — and NOTHING is
                    # committed until that PNG is safely on disk.
                    #
                    # The previous order (index first, save second, ignore
                    # failures) could permanently deduplicate a page that has no
                    # labelable image: the hash was in the index, so every later
                    # sighting counted as a duplicate and no screenshot was ever
                    # written for it again. Allocate, save, verify, and only then
                    # commit.
                    uid = f"unexpected_{_unexpected_next_id() + 1:06d}"
                    if not _unexpected_lib_save_png(uid, img, device, dlog):
                        # Index untouched, no labels, no metadata. The next
                        # sighting of this page gets a clean attempt.
                        return
                    _unexpected_hashes[uid] = h
                    _unexpected_counts[uid] = 1
                    occ, sim = 1, None
                    _unexpected_lib_label_stub(uid, device, dlog)

                rec = {
                    "unique_id":        uid,
                    "hash":             f"{h:x}",
                    "timestamp":        _dt.datetime.now().isoformat(timespec="seconds"),
                    "device":           job.get("device", ""),
                    "current_activity": job.get("current_activity", ""),
                    "source_fn":        job.get("source_fn", ""),
                    "context":          job.get("context", ""),
                    "page_guess":       job.get("page_guess", ""),
                    "issue_code":       job.get("issue_code", ""),
                    "occurrence":       occ,
                }
                # Text is recorded ONLY when the caller already had it. Never run
                # OCR here — diagnostics must not cost a ~9s OCR pass.
                if job.get("ocr_text"):
                    rec["ocr_text"] = str(job["ocr_text"])[:1000]
                if job.get("uia_text"):
                    rec["uia_text"] = (job["uia_text"][:80]
                                       if isinstance(job["uia_text"], list)
                                       else str(job["uia_text"])[:1000])
                if sim:
                    rec["similar_to"] = sim
                    rec["hamming"]    = best
                _unexpected_lib_append(rec)

        if dlog is not None:
            if duplicate:
                dlog.debug(f"[PAGE-LIB] {job.get('device','')} | duplicate of {sim} "
                           f"(hamming={best}) occurrence={occ} — no new screenshot")
            else:
                dlog.info(f"[PAGE-LIB] {job.get('device','')} | NEW unexpected page "
                          f"{uid} saved (hash={h:x})")
    except Exception:
        pass


def _unexpected_lib_worker() -> None:
    while True:
        try:
            job = _unexpected_q.get()
        except Exception:
            return
        if job is None:
            return
        try:
            _unexpected_lib_process(job)
        except Exception:
            pass
        finally:
            try:
                _unexpected_q.task_done()
            except Exception:
                pass


def _unexpected_lib_ensure_worker() -> bool:
    global _unexpected_q, _unexpected_worker
    try:
        if _unexpected_q is None:
            import queue as _queue
            _unexpected_q = _queue.Queue(maxsize=UNEXPECTED_QUEUE_MAX)
        if _unexpected_worker is None or not _unexpected_worker.is_alive():
            _unexpected_worker = _threading.Thread(
                target=_unexpected_lib_worker, daemon=True, name="unexpected_page_lib")
            _unexpected_worker.start()
        return True
    except Exception:
        return False


def record_unexpected_page(device: str, dlog, image=None, *,
                           current_activity: str = "",
                           source_fn: str = "", context: str = "",
                           page_guess: str = "", issue_code: str = "",
                           ocr_text: str = "", uia_text=None,
                           capture_if_missing: bool = True) -> None:
    """
    Submit an unexpected/unknown screen to the library. STRICTLY NON-BLOCKING.

    This function performs NO device I/O. It packages what the caller already
    has and calls put_nowait(). No screenshot, no activity read, no UIAutomator
    dump, no OCR happens on the calling thread — an earlier version did
    get_screenshot() and _get_current_activity() here, which put two ADB
    round-trips directly in the recovery path for the sake of a diagnostic.

    `image`             a frame the caller ALREADY has. Strongly preferred.
    `current_activity`  an activity string the caller ALREADY read.
    `capture_if_missing` when no image is supplied, fall back to the last frame
                        the WORKFLOW took, via get_cached_screenshot(). Nothing
                        captures on its behalf — not this thread and not the
                        background worker — because get_screenshot() holds the
                        per-device lock the automation needs. With no recent
                        cached frame the visual diagnostic is simply dropped.

    If the queue is full the job is dropped. A diagnostic must never slow the
    automation down or fail a device.
    """
    global _unexpected_dropped
    try:
        if not _unexpected_lib_ensure_worker():
            return
        if image is None and capture_if_missing:
            # Reuse the last frame the WORKFLOW took. Never capture here — and
            # never let the background worker capture either, because
            # get_screenshot holds the per-device lock the automation needs.
            image = get_cached_screenshot(device)
        if image is None:
            # No recent frame. Drop the visual diagnostic rather than acquire
            # the screenshot lock ahead of the main workflow.
            try:
                dlog.debug(f"[PAGE-LIB] {device} | no recent cached frame "
                           f"(<{UNEXPECTED_CACHE_MAX_AGE:.0f}s) — visual "
                           f"diagnostic skipped")
            except Exception:
                pass
            return
        _unexpected_q.put_nowait({
            "device": device, "dlog": dlog, "image": image,
            "queued_at": time.time(),
            "current_activity": (current_activity or "").strip(),
            "source_fn": source_fn, "context": context,
            "page_guess": page_guess, "issue_code": issue_code,
            "ocr_text": ocr_text, "uia_text": uia_text,
        })
    except Exception as exc:
        # queue.Full lands here — intentional. Drop the diagnostic and move on.
        _unexpected_dropped += 1
        try:
            if _unexpected_dropped in (1, 10, 100) or _unexpected_dropped % 500 == 0:
                dlog.debug(f"[PAGE-LIB] {device} | diagnostic dropped "
                           f"({_unexpected_dropped} total): {exc!r}")
        except Exception:
            pass


class VpnGuard:
    """
    Passive background monitor for setup_vpn().  DETECTS ONLY.

    This guard never clicks, never presses Back, never opens or reinstalls
    ProtonVPN, never closes or relaunches the emulator, and never restarts a
    flow.  It observes, records the first issue it sees, and stops.  Every
    recovery action happens on the main thread inside vpn_guard_checkpoint()
    so the per-run caps in the SETUP CORE block can never be bypassed by a
    background thread racing the main one.

    Lifecycle
    ─────────
        setup_vpn() constructs and start()s it
        shared device checks are live immediately
        set_vpn_opened() enables the VPN-specific page checks
        setup_vpn() stop()s it in a finally block, always

    Detects
    ───────
        device_closed_by_itself        emulator vanished, we did not close it
        device_not_responding          port alive, ADB dead >10s
        screenshot_failed_repeatedly   reported by the main thread
        unexpected_home                Home/launcher >5s after open_vpn
        unexpected_page                non-VPN, non-Home, non-permission page

    'unknown_page' is deliberately NOT emitted here.  A page is only promoted
    to a confirmed unknown_page by the main-thread handler, and only after
    Back x3 has failed to get back to a known VPN page.
    """

    CHECK_INTERVAL = 1.0    # guard cadence — checkpoints must see fresh results

    def __init__(self, device: str, dlog):
        self.device = device
        self.dlog   = dlog

        self._stop_event  = _threading.Event()
        self._result      = None
        self._result_lock = _threading.Lock()

        self._stage      = 1
        self._stage_lock = _threading.Lock()

        # VPN-specific page checks stay off until open_vpn() has succeeded,
        # otherwise the launcher/Home we start from looks like an error.
        self._vpn_opened      = False
        self._vpn_opened_lock = _threading.Lock()

        # Screenshot health is reported by the main thread (the guard itself
        # never takes screenshots — it reads activities, which is far cheaper).
        self._screenshot_none  = False
        self._screenshot_lock  = _threading.Lock()

        self._health     = HealthState()
        self._started_at = time.time()

        self._thread = _threading.Thread(
            target=self._run, daemon=True, name=f"vpn_guard_{device}"
        )

    # ── public API ───────────────────────────────────────────────────────

    def start(self):
        """
        Start the monitor thread, replacing any existing VpnGuard for this
        device first.  Two guards on one device produce duplicate device-lost
        events and double-count recovery, so dedup is mandatory.
        """
        device   = self.device
        existing = _active_vpn_guards.get(device)
        if existing is not None and existing is not self:
            if existing._thread.is_alive():
                self.dlog.warning(
                    f"[VPN-GUARD] {device} | existing VpnGuard alive — stopping it "
                    f"before starting the replacement"
                )
                existing._stop_event.set()
                existing._thread.join(timeout=3.0)
            else:
                self.dlog.debug(f"[VPN-GUARD] {device} | replacing stopped VpnGuard")
        _active_vpn_guards[device] = self
        self.dlog.info(f"[VPN-GUARD] {device} | started stage={self._stage}")
        if not self._thread.is_alive():
            self._thread.start()
        return self

    def stop(self):
        self._stop_event.set()
        try:
            self._thread.join(timeout=3.0)
        except Exception:
            pass
        if _active_vpn_guards.get(self.device) is self:
            _active_vpn_guards.pop(self.device, None)
        self.dlog.info(f"[VPN-GUARD] {self.device} | stopped")

    def set_stage(self, stage: int):
        with self._stage_lock:
            self._stage = stage
        self.dlog.debug(f"[VPN-GUARD] {self.device} | stage -> {stage}")

    def set_vpn_opened(self):
        """Main thread calls this once open_vpn() has succeeded."""
        with self._vpn_opened_lock:
            self._vpn_opened = True
        self.dlog.debug(f"[VPN-GUARD] {self.device} | vpn_opened — page checks enabled")

    def report_screenshot(self, img_is_none: bool):
        """
        Main thread reports each screenshot outcome so the guard can run the
        shared >10s continuous-failure check without duplicating captures.
        """
        with self._screenshot_lock:
            self._screenshot_none = bool(img_is_none)

    def check(self) -> tuple:
        """Non-blocking read of the latest detection result."""
        with self._result_lock:
            if self._result is not None:
                return self._result
        return ("ok",)

    def clear_result(self):
        """Reset detection state so the guard can be re-armed after recovery."""
        with self._result_lock:
            self._result = None
        self._stop_event.clear()
        self._health.reset()
        self._started_at = time.time()

    def is_alive(self) -> bool:
        return self._thread.is_alive()

    # ── internal ─────────────────────────────────────────────────────────

    def _set_result(self, issue: str, stage: int, detail: str = ""):
        """Record the first issue seen and stop the thread."""
        with self._result_lock:
            if self._result is None:
                self._result = (issue, stage, detail)
                self.dlog.warning(
                    f"[VPN-GUARD] {self.device} | DETECTED {issue} "
                    f"(stage={stage}) {detail}"
                )
        self._stop_event.set()

    def _run(self):
        device        = self.device
        dlog          = self.dlog
        home_since    = None
        unknown_since = None

        dlog.info(f"[VPN-GUARD] {device} | monitor loop running (detect-only)")

        while not self._stop_event.is_set():
            with self._stage_lock:
                stage = self._stage
            with self._vpn_opened_lock:
                vpn_opened = self._vpn_opened
            with self._screenshot_lock:
                shot_none = self._screenshot_none

            # ── 1. Shared device health — always active from t=0 ──────────
            issue = shared_device_health(device, self._health, dlog,
                                         img_was_none=shot_none)
            if issue:
                self._set_result(issue, stage, "shared_device_health")
                return

            # ── 2. VPN-specific page checks — only after open_vpn ─────────
            if not vpn_opened:
                self._stop_event.wait(timeout=self.CHECK_INTERVAL)
                continue

            current = (_get_current_activity(device) or "").strip()
            if not current or "null" in current.lower():
                # Transient window between activities — not evidence of anything.
                home_since    = None
                unknown_since = None
                self._stop_event.wait(timeout=self.CHECK_INTERVAL)
                continue

            is_home = ("HomeActivity" in current) or ("launcher" in current.lower())
            is_vpn  = any(k in current for k in _VPN_KNOWN_ACTIVITIES)

            # 2a. Home/launcher persisting after we opened the VPN app
            if is_home:
                unknown_since = None
                now = time.time()
                if home_since is None:
                    home_since = now
                    dlog.info(
                        f"[VPN-GUARD] {device} | Home/launcher seen after open_vpn — "
                        f"{VPN_HOME_TOLERANCE:.0f}s tolerance started"
                    )
                elif now - home_since >= VPN_HOME_TOLERANCE:
                    self._set_result(
                        "unexpected_home", stage,
                        f"Home held {now - home_since:.1f}s "
                        f"(>{VPN_HOME_TOLERANCE:.0f}s) activity={current!r}"
                    )
                    return
                self._stop_event.wait(timeout=self.CHECK_INTERVAL)
                continue

            home_since = None

            # 2b. Known VPN page (including the Android VPN permission dialog,
            #     which lives in _VPN_KNOWN_ACTIVITIES as 'vpndialogs')
            if is_vpn:
                if unknown_since is not None:
                    dlog.info(f"[VPN-GUARD] {device} | back on a known VPN page — timer reset")
                unknown_since = None
                self._stop_event.wait(timeout=self.CHECK_INTERVAL)
                continue

            # 2c. Something else entirely — an ad, a browser, another app
            now = time.time()
            if unknown_since is None:
                unknown_since = now
                dlog.info(
                    f"[VPN-GUARD] {device} | unexpected activity {current!r} — "
                    f"{VPN_HOME_TOLERANCE:.0f}s tolerance started"
                )
            elif now - unknown_since >= VPN_HOME_TOLERANCE:
                self._set_result(
                    "unexpected_page", stage,
                    f"held {now - unknown_since:.1f}s activity={current!r}"
                )
                return

            self._stop_event.wait(timeout=self.CHECK_INTERVAL)

        dlog.info(f"[VPN-GUARD] {device} | monitor loop exited")


# ── VpnGuard main-thread checkpoint + recovery ───────────────────────────────

def _vpn_guard_rearm(guard: "VpnGuard", new_stage: int) -> "VpnGuard":
    """
    Re-arm a VpnGuard after the main thread finished recovering.

    Stops the old thread, clears the consumed result, resets health streaks and
    starts a fresh thread.  Reuses the same object so callers holding a
    reference keep working.
    """
    device = guard.device
    dlog   = guard.dlog
    dlog.info(f"[VPN-GUARD] {device} | re-arming at stage {new_stage}")
    try:
        guard.stop()
    except Exception:
        pass
    guard.clear_result()
    guard.set_stage(new_stage)
    guard._stop_event.clear()
    guard._thread = _threading.Thread(
        target=guard._run, daemon=True, name=f"vpn_guard_{device}"
    )
    _active_vpn_guards[device] = guard
    guard._thread.start()
    dlog.info(f"[VPN-GUARD] {device} | re-armed at stage {new_stage}")
    return guard


def _vpn_guard_handle(device: str, dlog, result: tuple, guard: "VpnGuard",
                      phase: str = "") -> str:
    """
    Act on one VpnGuard detection.  Runs on the MAIN thread only.

    Every branch goes through the capped helpers in SETUP CORE, so no recovery
    path can exceed its per-run budget regardless of how it was reached.

    Returns one of the SIG_* signals, or "ok" when nothing needed doing.
    """
    issue  = result[0]
    stage  = result[1] if len(result) > 1 else None
    detail = result[2] if len(result) > 2 else ""
    fn     = "vpn_guard_checkpoint"

    if issue == "ok":
        return "ok"

    _slog(dlog, device, fn, phase or f"stage{stage}",
          f"handling guard issue: {issue}", detail=detail)

    # ── Emulator closed on its own → relaunch, separate cap ───────────────
    if issue == "device_closed_by_itself":
        return recover_self_closed_device(device, dlog, phase=phase, fn=fn)

    # ── Emulator frozen → deliberate close/reopen, program cap ────────────
    if issue == "device_not_responding":
        return program_reopen_device(device, dlog, reason="device_not_responding",
                                     phase=phase, fn=fn)

    # ── Screenshots dead → health-classified reopen, never change server ──
    if issue == "screenshot_failed_repeatedly":
        return handle_screenshot_failure(device, dlog, phase=phase, fn=fn)

    # ── Bounced back to Home after the VPN was opened ─────────────────────
    if issue == "unexpected_home":
        now = time.time()
        stamps = [t for t in _unexpected_home_timestamps.get(device, [])
                  if now - t < UNEXPECTED_HOME_WINDOW]
        stamps.append(now)
        _unexpected_home_timestamps[device] = stamps
        _slog(dlog, device, fn, phase or "setup_vpn",
              "unexpected_home during VPN setup",
              events=f"{len(stamps)}/{CAP_UNEXPECTED_HOME_EVENTS}"
                     f" in {UNEXPECTED_HOME_WINDOW:.0f}s")

        if len(stamps) >= CAP_UNEXPECTED_HOME_EVENTS:
            # The VPN app keeps dying on launch — reinstalling is the only
            # remaining lever before touching the emulator itself.
            _unexpected_home_timestamps[device] = []
            append_issue(device, "vpn_home_bounce_repeated",
                         f"{len(stamps)} home bounces within "
                         f"{UNEXPECTED_HOME_WINDOW:.0f}s", fn=fn, phase=phase)
            return _vpn_escalate(device, dlog, guard,
                                 phase=phase, reason="repeated_home_bounce")

        # First few bounces: just reopen ProtonVPN and redo stage 1.
        _slog(dlog, device, fn, phase or "setup_vpn",
              "reopening ProtonVPN after home bounce", signal=SIG_RESTART_SETUP_VPN)
        return SIG_RESTART_SETUP_VPN

    # ── Some other app/page took the foreground ───────────────────────────
    if issue == "unexpected_page":
        # Promote to a confirmed unknown_page ONLY after Back x3 fails.
        for attempt in range(1, 4):
            if _stop_requested():
                return SIG_MANUAL_STOP
            try:
                press_back(device)
            except Exception as exc:
                dlog.warning(f"[VPN-GUARD] {device} | press_back raised: {exc!r}")
            time.sleep(1.0)
            current = (_get_current_activity(device) or "").strip()
            known = any(k in current for k in _VPN_KNOWN_ACTIVITIES)
            _slog(dlog, device, fn, phase or "setup_vpn",
                  "Back pressed to clear unexpected page",
                  attempt=f"{attempt}/3", page=current, recovered=known)
            if known:
                return SIG_RESTART_SETUP_VPN

        # Back x3 did not get us home — this is a confirmed unknown_page.
        current = (_get_current_activity(device) or "").strip()
        _slog(dlog, device, fn, phase or "setup_vpn",
              "Back x3 failed — confirmed unknown_page", page=current)
        append_issue(device, "vpn_unknown_page",
                     f"activity={current!r} after Back x3", fn=fn, phase=phase)
        try:
            # `current` was already read for the decision above — no new ADB call.
            # Deliberately NOT calling _svpn_uia_texts() here: that is a fresh
            # UIAutomator dump (4-11s) on the recovery path for a diagnostic.
            record_unexpected_page(
                device, dlog, current_activity=current,
                source_fn="_vpn_guard_handle", context=phase or "setup_vpn",
                page_guess=f"vpn_unknown_{stage}", issue_code="vpn_unknown_page")
        except Exception:
            pass
        return _vpn_escalate(device, dlog, guard,
                             phase=phase, reason="unknown_page")

    dlog.warning(f"[VPN-GUARD] {device} | unhandled guard issue {issue!r} — ignoring")
    return "ok"


def vpn_guard_checkpoint(device: str, dlog, guard: "VpnGuard",
                         phase: str = "") -> str:
    """
    The mandatory VpnGuard checkpoint.

    Call this at least once per second inside every wait loop, and immediately
    before every button click, so the maximum time between a problem appearing
    and the main thread reacting stays close to the guard's 1s cadence.

    Returns:
        "ok"       — nothing detected, keep going
        SIG_*      — a recovery ran (or must run); caller acts on the signal
    """
    if _stop_requested():
        return SIG_MANUAL_STOP

    # Pause gate FIRST — ahead of reading the guard.  A guard result produced
    # while the host was offline describes a dead network, not a broken device,
    # and acting on it would burn recovery budget for nothing.
    gate = wait_while_paused(device, dlog, phase=phase,
                             fn="vpn_guard_checkpoint", context="setup")
    if gate == SIG_MANUAL_STOP:
        return SIG_MANUAL_STOP
    if gate == "resumed":
        try:
            guard.clear_result()      # discard anything detected during the outage
        except Exception:
            pass
        return SIG_RESTART_BEFORE_TARGET_APP

    result = guard.check()
    if result[0] == "ok":
        return "ok"

    outcome = _vpn_guard_handle(device, dlog, result, guard, phase=phase)

    # Consume the result so a stale detection cannot fire twice.
    try:
        guard.clear_result()
    except Exception:
        pass
    return outcome


def _save_unknown_page_screenshot(device: str, dlog, tag: str, image=None,
                                  issue_code: str = "", context: str = "",
                                  current_activity: str = "") -> None:
    """
    Hand an unrecognised page to the deduplicating library. NON-BLOCKING.

    Was: write a timestamped PNG on every occurrence, which produced hundreds of
    near-identical files nobody could review. Now one screenshot is kept per
    visually distinct page and repeats only bump an occurrence counter — and the
    work happens on a background thread, so recovery never waits for it.
    """
    try:
        record_unexpected_page(
            device, dlog, image=image, current_activity=current_activity,
            source_fn="_save_unknown_page_screenshot",
            context=context or tag, page_guess=tag, issue_code=issue_code,
        )
    except Exception as exc:
        dlog.debug(f"[PAGE-LIB] {device} | could not queue unknown page: {exc!r}")


# ------------------------------------------------------------
# 10. WORKFLOW: VPN
# ------------------------------------------------------------
# Global dictionaries to track state per device
# vpn_stage: Tracks which step the device is on (None = start, 1 = startup done, etc.)
# stage_tries: Tracks how many times we've retried the current step to prevent infinite loops

# =============================================================================
# PHASE 1 of prepare_target_app:  setup_device()
# -----------------------------------------------------------------------------
# Everything that must be true about the DEVICE and the INSTALLED APPS before
# we touch ProtonVPN or Target Application.  Previously this work was scattered across
# setup_vpn stages 1-2 (boot, startup internet, VPN install) and setup_target_app
# stages 1-2 (TargetApp install, version, APK/XAPK, FatalAPKError).  Consolidating it
# here means setup_vpn and setup_target_app can assume a healthy, correctly-provisioned
# device and stay focused on their own app.
#
# No phase guard runs during setup_device.  Guards are phase-scoped
# (setup_vpn -> VpnGuard, setup_target_app -> TargetAppGuard) and there is deliberately no
# third common guard thread, so this phase does its device-health checks inline
# through the same shared helpers the guards use.
# =============================================================================

def _sd_health_checkpoint(device: str, dlog, state: HealthState,
                          phase: str, img_was_none: "bool | None" = None) -> str:
    """
    Inline device-health checkpoint for setup_device.

    Uses exactly the same shared checks as VpnGuard/TargetAppGuard so a self-closed
    emulator is counted identically no matter which phase noticed it.

    Returns "ok" or a SIG_* signal.
    """
    if _stop_requested():
        return SIG_MANUAL_STOP

    issue = shared_device_health(device, state, dlog, img_was_none=img_was_none)
    if not issue:
        return "ok"

    fn = "setup_device"
    _slog(dlog, device, fn, phase, f"device health issue: {issue}")

    if issue == "device_closed_by_itself":
        return recover_self_closed_device(device, dlog, phase=phase, fn=fn)
    if issue == "device_not_responding":
        return program_reopen_device(device, dlog, reason="device_not_responding",
                                     phase=phase, fn=fn)
    if issue == "screenshot_failed_repeatedly":
        return handle_screenshot_failure(device, dlog, phase=phase, fn=fn)
    return "ok"


def _sd_wait_device_ready(device: str, dlog, state: HealthState) -> str:
    """
    Make sure the BlueStacks instance is running, connected and past boot.

    Launches the instance if ADB does not know about it, then waits for any
    non-null foreground activity (the reliable "Android is up" signal), then
    gives HomeActivity a short grace window.  Not reaching Home is logged but
    not fatal — some instances land on a different launcher activity and the
    rest of the flow copes fine.
    """
    phase = "device_ready"
    t0    = time.time()
    _slog(dlog, device, "setup_device", phase, "waiting for device readiness")
    print(f"[{device}] setup_device: waiting for device to be ready...")
    start_clock(device, "DeviceStartUp")

    # ── Make sure ADB can see it at all; launch the instance if not ───────
    if not _device_exists_in_adb(device):
        _slog(dlog, device, "setup_device", phase,
              "device absent from adb — launching BlueStacks instance")
        try:
            _launch_device_for_worker(device)
        except Exception as exc:
            dlog.error(f"[SETUP] {device} | _launch_device_for_worker raised: {exc!r}")
        try:
            _adb_wait_for_device(device, timeout=90, interval=3)
        except Exception:
            pass

    # ── Wait for a real foreground activity (max 100s) ────────────────────
    startup_detected = False
    current          = ""
    while time.time() - t0 < 100.0:
        chk = _sd_health_checkpoint(device, dlog, state, phase)
        if chk != "ok":
            return chk

        current = (_get_current_activity(device) or "")
        if current.strip() and "null" not in current.lower():
            startup_detected = True
            _slog(dlog, device, "setup_device", phase, "first activity detected",
                  page=current.strip(), elapsed=time.time() - t0)
            break
        random_delay(0.8, 1.2)

    if not startup_detected:
        _slog(dlog, device, "setup_device", phase,
              "device never produced an activity — program reopen",
              elapsed=time.time() - t0)
        append_issue(device, "device_boot_timeout",
                     "no foreground activity within 100s",
                     fn="setup_device", phase=phase)
        return program_reopen_device(device, dlog, reason="device_boot_timeout",
                                     phase=phase, fn="setup_device")

    # ── Home screen grace window (informational only) ──────────────────────
    if "HomeActivity" in current or on_home_screen(device):
        _slog(dlog, device, "setup_device", phase, "already on Home")
    else:
        t_home = time.time()
        reached_home = False
        while time.time() - t_home < 5.0:
            chk = _sd_health_checkpoint(device, dlog, state, phase)
            if chk != "ok":
                return chk
            cur_now = (_get_current_activity(device) or "")
            if "HomeActivity" in cur_now or on_home_screen(device):
                reached_home = True
                break
            random_delay(0.8, 1.2)
        _slog(dlog, device, "setup_device", phase,
              "Home confirmed" if reached_home
              else "Home not seen in 5s — proceeding anyway (device is up)",
              page=(_get_current_activity(device) or "").strip())

    duration = stop_clock(device, "DeviceStartUp")
    _slog(dlog, device, "setup_device", phase, "device ready", elapsed=duration)
    print(f"[{device}] Startup: {duration:.2f}s")
    update_status(device, "DeviceStartup", f"{duration:.2f}s")
    return SIG_SUCCESS


def _sd_check_display_and_touch(device: str, dlog) -> str:
    """
    STRICT display/DPI validation, then touch-device validation.

    Every coordinate in this bot is calibrated for 1920x1080 @ 240dpi and every
    tap goes through the cached touch input node.  If either is wrong, taps land
    somewhere else and the run misbehaves in ways that look like game bugs.  So
    this step is deliberately fail-hard: a device that cannot be verified does
    not proceed to setup_vpn or setup_target_app.

    The live device is the only source of truth.  The BlueStacks config is read
    purely as a debugging breadcrumb and can never pass or fail a device.
    """
    phase = "display_touch"

    # Informational only — never contributes to the verdict.
    try:
        _preflight_display_from_config(device, dlog)
    except Exception:
        pass

    # ── Display: up to 3 attempts, unreadable output is retried ───────────────
    details = None
    for attempt in range(1, DISPLAY_CHECK_ATTEMPTS + 1):
        if _stop_requested():
            return SIG_MANUAL_STOP

        try:
            details = check_display(device, dlog, return_details=True)
        except Exception as exc:
            dlog.error(f"[SETUP] {device} | check_display raised: {exc!r}")
            details = None

        if details is not None and details.get("readable"):
            _slog(dlog, device, "setup_device", phase, "display values read",
                  attempt=f"{attempt}/{DISPLAY_CHECK_ATTEMPTS}",
                  size=details["size_str"], density=details["density_str"],
                  size_raw=repr(details["size_out"]),
                  density_raw=repr(details["density_out"]),
                  result="PASS" if details["ok"] else "FAIL",
                  reason=details["reason"])
            break

        raw_s = repr(details.get("size_out", "")) if details else "n/a"
        raw_d = repr(details.get("density_out", "")) if details else "n/a"
        _slog(dlog, device, "setup_device", phase,
              "display values UNREADABLE — retrying",
              attempt=f"{attempt}/{DISPLAY_CHECK_ATTEMPTS}",
              size_raw=raw_s, density_raw=raw_d)

        if attempt < DISPLAY_CHECK_ATTEMPTS:
            # Short guarded wait — the window right after boot is the usual
            # cause of an empty wm response.
            if stop_aware_sleep(device, 2.0, dlog) == SIG_MANUAL_STOP:
                return SIG_MANUAL_STOP
    else:
        details = None

    # ── Unreadable after all attempts ─────────────────────────────────────────
    if details is None or not details.get("readable"):
        raw_s = repr(details.get("size_out", "")) if details else "n/a"
        raw_d = repr(details.get("density_out", "")) if details else "n/a"
        _slog(dlog, device, "setup_device", phase,
              "could not verify display after all attempts — failing device",
              attempt=f"{DISPLAY_CHECK_ATTEMPTS}/{DISPLAY_CHECK_ATTEMPTS}",
              size_raw=raw_s, density_raw=raw_d, signal=SIG_FAIL_DEVICE)
        dlog.error(
            f"[DISPLAY] {device} | FINAL wm size output: {raw_s}\n"
            f"[DISPLAY] {device} | FINAL wm density output: {raw_d}"
        )
        append_issue(device, "display_check_failed",
                     f"could not verify wm size/density after "
                     f"{DISPLAY_CHECK_ATTEMPTS} tries",
                     fn="setup_device", phase=phase)
        return SIG_FAIL_DEVICE

    # ── Readable but wrong ────────────────────────────────────────────────────
    if not details["ok"]:
        _slog(dlog, device, "setup_device", phase,
              "display/DPI MISMATCH — every tap coordinate would be wrong",
              size=details["size_str"], density=details["density_str"],
              expected=f"{EXPECTED_WIDTH}x{EXPECTED_HEIGHT}@{EXPECTED_DENSITY}",
              reason=details["reason"], signal=SIG_FAIL_DEVICE)
        dlog.error(
            f"[DISPLAY] {device} | raw wm size:    {details['size_out']!r}\n"
            f"[DISPLAY] {device} | raw wm density: {details['density_out']!r}\n"
            f"[DISPLAY] {device} | parsed: size={details['size_str']} "
            f"density={details['density_str']}"
        )
        append_issue(
            device, "display_mismatch",
            f"expected {EXPECTED_WIDTH}x{EXPECTED_HEIGHT} @ {EXPECTED_DENSITY}dpi, "
            f"got size={details['size_str']}, density={details['density_str']}",
            fn="setup_device", phase=phase,
        )
        return SIG_FAIL_DEVICE

    _slog(dlog, device, "setup_device", phase, "display verified",
          size=details["size_str"], density=details["density_str"])

    # ── Touch device, only after display passed ───────────────────────────────
    try:
        touch_ok = _verify_touch_device(device, dlog)
    except Exception as exc:
        dlog.warning(f"[SETUP] {device} | _verify_touch_device raised: {exc!r}")
        touch_ok = True          # a probe failure alone should not fail the device

    if not touch_ok:
        _slog(dlog, device, "setup_device", phase, "touch input device not found",
              signal=SIG_FAIL_DEVICE)
        append_issue(device, "touch_device_missing",
                     "BlueStacks Virtual Touch not located",
                     fn="setup_device", phase=phase)
        return SIG_FAIL_DEVICE

    _slog(dlog, device, "setup_device", phase, "display + touch verified",
          size=details["size_str"], density=details["density_str"])
    return SIG_SUCCESS


def _sd_startup_internet(device: str, dlog) -> str:
    """
    The first internet check after boot.  The VPN is NOT up yet at this point.

    A failure here splits two ways and the distinction matters a lot:
      * host internet down  -> pause the whole controller, touch nothing,
                               do NOT close/reopen this device
      * host internet up    -> this device's networking is broken, so a
                               program-initiated reopen is the right fix
    """
    phase = "startup_internet"
    _slog(dlog, device, "setup_device", phase, "startup internet check (pre-VPN)")

    net = check_network_and_maybe_pause(device, dlog, phase=phase, fn="setup_device")

    if net == "ok":
        _slog(dlog, device, "setup_device", phase, "device internet confirmed")
        return SIG_SUCCESS

    if net == SIG_MANUAL_STOP:
        return SIG_MANUAL_STOP

    if net == SIG_RESTART_BEFORE_TARGET_APP:
        # Host outage: we paused and it came back.  Restart cleanly; the device
        # was never touched and no counter moved.
        _slog(dlog, device, "setup_device", phase,
              "host internet restored after pause — restarting prepare_target_app",
              signal=SIG_RESTART_BEFORE_TARGET_APP)
        return SIG_RESTART_BEFORE_TARGET_APP

    # net == "device_only": host is fine, this emulator's network is not.
    _slog(dlog, device, "setup_device", phase,
          "device-specific startup internet failure (host is up) — program reopen")
    append_issue(device, "startup_internet_failed",
                 "device has no internet while host internet is up",
                 fn="setup_device", phase=phase)
    return program_reopen_device(device, dlog, reason="startup_internet_failed",
                                 phase=phase, fn="setup_device")


def _sd_target_app_install_and_version(device: str, dlog) -> str:
    """
    Target Application install + version/APK/XAPK checks.

    Ported from the old setup_target_app stages 1-2 with the safety behaviour intact:
      * missing app                -> install from APK_FOLDER
      * installed == available     -> nothing to do
      * installed >  available     -> write the newer version back to F2, and
                                      raise FatalAPKError if that APK is not in
                                      APK_FOLDER (stops ALL devices, because
                                      every other device is about to hit the
                                      same wall)
      * installed <  available     -> update if the APK exists, otherwise log
                                      and proceed rather than blocking the run

    FatalAPKError is intentionally allowed to propagate untouched.
    """
    global _available_version
    phase = "target_app_install"

    # ── Install if missing ────────────────────────────────────────────────
    for attempt in range(1, 3):
        if _stop_requested():
            return SIG_MANUAL_STOP

        if find_target_app(device):
            _slog(dlog, device, "setup_device", phase, "TargetApp installed",
                  attempt=f"{attempt}/2")
            break

        if target_app_install_attempts.get(device) and attempt > 1:
            _slog(dlog, device, "setup_device", phase,
                  "TargetApp install loop detected — aborting")
            append_issue(device, "target_app_install_loop",
                         "install attempted twice, app still missing",
                         fn="setup_device", phase=phase)
            return SIG_FAIL_DEVICE

        _slog(dlog, device, "setup_device", phase,
              "TargetApp not installed — running install_target_app()", attempt=f"{attempt}/2")
        print(f"[{device}] TargetApp not found — installing...")
        try:
            install_target_app(device)
        except FatalAPKError:
            raise                       # stops all devices — by design
        except Exception as exc:
            dlog.error(f"[SETUP] {device} | install_target_app raised: {exc!r}")
        target_app_install_attempts[device] = True

        t_inst   = time.time()
        installed = False
        while time.time() - t_inst < 100.0:
            if _stop_requested():
                return SIG_MANUAL_STOP
            if find_target_app(device):
                installed = True
                break
            time.sleep(2.0)
        _slog(dlog, device, "setup_device", phase,
              "TargetApp install poll finished", elapsed=time.time() - t_inst,
              installed=installed)
        if installed:
            break
    else:
        _slog(dlog, device, "setup_device", phase,
              "TargetApp still not installed after 2 attempts — program reopen")
        append_issue(device, "target_app_install_failed", "not installed after 2 attempts",
                     fn="setup_device", phase=phase)
        return program_reopen_device(device, dlog, reason="target_app_install_failed",
                                     phase=phase, fn="setup_device")

    # ── Version / APK / XAPK check ────────────────────────────────────────
    phase = "target_app_version"
    installed_version = None
    try:
        out = _adb_shell(device, "dumpsys", "package",
                         TARGET_APP_PACKAGE, timeout=10)
        for line in out.splitlines():
            if "versionName" in line:
                m = re.search(r"versionName=(\S+)", line)
                if m:
                    installed_version = m.group(1)
                break
    except Exception as exc:
        dlog.warning(f"[SETUP] {device} | version read failed: {exc!r}")

    def _parse_ver(v):
        try:
            return tuple(int(x) for x in re.split(r"[._\-]", v))
        except Exception:
            return (0,)

    avail = _available_version          # read from sheet F2 at startup
    _slog(dlog, device, "setup_device", phase, "version comparison",
          installed=installed_version, available=avail or "(empty)")

    if not avail:
        _slog(dlog, device, "setup_device", phase,
              "available version empty (F2 not read) — skipping version check")
        return SIG_SUCCESS

    if not installed_version:
        _slog(dlog, device, "setup_device", phase,
              "installed version unreadable — skipping version check")
        return SIG_SUCCESS

    inst_t, avail_t = _parse_ver(installed_version), _parse_ver(avail)

    if inst_t == avail_t:
        _slog(dlog, device, "setup_device", phase, "version match — no update needed")
        return SIG_SUCCESS

    if inst_t > avail_t:
        # The device is ahead of the sheet.  Publish the newer version so every
        # other worker stops trying to "update" down to the older one.
        _slog(dlog, device, "setup_device", phase,
              "installed is NEWER than F2 — writing new version to F2")
        try:
            ws = _get_control_ws()
            _sheets_call(ws.update_acell, "F2", installed_version)
            _available_version = installed_version
            _slog(dlog, device, "setup_device", phase, "F2 updated",
                  available=installed_version)
        except Exception as exc:
            dlog.warning(f"[SETUP] {device} | F2 write failed: {exc!r}")

        apk_found = False
        try:
            for fname in os.listdir(APK_FOLDER):
                if installed_version in fname and "app" in fname.lower():
                    apk_found = True
                    break
        except Exception as exc:
            dlog.warning(f"[SETUP] {device} | APK folder scan failed: {exc!r}")

        if not apk_found:
            msg = (f"Newer TargetApp version {installed_version} found on device but "
                   f"its APK is NOT in APK_FOLDER — stopping all devices")
            _slog(dlog, device, "setup_device", phase, "FATAL: " + msg)
            append_issue(device, "fatal_apk_missing", msg,
                         fn="setup_device", phase=phase)
            print(f"[{device}] FATAL: {msg}")
            raise FatalAPKError(msg)

        _slog(dlog, device, "setup_device", phase,
              "APK for the newer version is present — proceeding")
        return SIG_SUCCESS

    # ── installed < available: update if we actually have the APK ─────────
    apk_file = None
    try:
        for fname in os.listdir(APK_FOLDER):
            if avail in fname and "app" in fname.lower():
                apk_file = os.path.join(APK_FOLDER, fname)
                break
    except Exception as exc:
        dlog.warning(f"[SETUP] {device} | APK folder scan failed: {exc!r}")

    if not apk_file:
        _slog(dlog, device, "setup_device", phase,
              "APK for the available version not in folder — proceeding without update",
              available=avail)
        return SIG_SUCCESS

    if target_app_install_attempts.get(device) is True:
        _slog(dlog, device, "setup_device", phase,
              "update install loop — already attempted once, aborting")
        append_issue(device, "target_app_update_loop",
                     f"update to {avail} attempted twice",
                     fn="setup_device", phase=phase)
        return SIG_FAIL_DEVICE

    _slog(dlog, device, "setup_device", phase, "updating TargetApp",
          installed=installed_version, available=avail, apk=os.path.basename(apk_file))
    print(f"[{device}] Updating Target Application to {avail}...")
    try:
        install_target_app(device)
    except FatalAPKError:
        raise
    except Exception as exc:
        dlog.error(f"[SETUP] {device} | install_target_app (update) raised: {exc!r}")
    target_app_install_attempts[device] = True

    t_upd = time.time()
    while time.time() - t_upd < 100.0:
        if _stop_requested():
            return SIG_MANUAL_STOP
        if find_target_app(device):
            _slog(dlog, device, "setup_device", phase, "update install confirmed",
                  elapsed=time.time() - t_upd)
            return SIG_SUCCESS
        time.sleep(2.0)

    _slog(dlog, device, "setup_device", phase, "update install did not complete in 100s")
    append_issue(device, "target_app_update_failed", f"target={avail}",
                 fn="setup_device", phase=phase)
    return program_reopen_device(device, dlog, reason="target_app_update_failed",
                                 phase=phase, fn="setup_device")


def _sd_vpn_install(device: str, dlog) -> str:
    """
    Make sure ProtonVPN is installed.

    Uses the SHARED install/reinstall cap (CAP_VPN_INSTALL per device per run).
    An install here and a later recovery reinstall draw from the same budget, so
    the two paths cannot combine to reinstall more times than the cap allows.
    If ProtonVPN is already present nothing is counted.
    """
    phase = "vpn_install"

    if find_vpn(device):
        _slog(dlog, device, "setup_device", phase,
              "ProtonVPN already installed — cap not consumed",
              used=f"{_ctr_get(_vpn_install_count, device)}/{CAP_VPN_INSTALL}")
        return SIG_SUCCESS

    if not vpn_install_allowed(device, dlog, reason="setup_device_missing",
                               phase=phase, fn="setup_device"):
        return SIG_FAIL_DEVICE

    _slog(dlog, device, "setup_device", phase, "ProtonVPN missing — installing")
    print(f"[{device}] ProtonVPN not found — installing...")
    try:
        install_vpn(device)
    except Exception as exc:
        dlog.error(f"[SETUP] {device} | install_vpn raised: {exc!r}")

    t0 = time.time()
    while time.time() - t0 < 100.0:
        if _stop_requested():
            return SIG_MANUAL_STOP
        if find_vpn(device):
            _slog(dlog, device, "setup_device", phase, "ProtonVPN install confirmed",
                  elapsed=time.time() - t0)
            return SIG_SUCCESS
        random_delay(1.5, 2.5)

    _slog(dlog, device, "setup_device", phase, "ProtonVPN install did not complete in 100s")
    append_issue(device, "vpn_install_failed", "not present 100s after install_vpn",
                 fn="setup_device", phase=phase)
    return program_reopen_device(device, dlog, reason="vpn_install_failed",
                                 phase=phase, fn="setup_device")


def _sd_force_stop_apps(device: str, dlog) -> None:
    """
    Force-stop ProtonVPN and TargetApp so setup_vpn and setup_target_app each start from a
    known-cold app state rather than inheriting whatever was left running.
    """
    _slog(dlog, device, "setup_device", "cleanup",
          "force-stopping ProtonVPN + TargetApp for a clean phase start")
    try:
        refresh_device(device)
    except Exception as exc:
        dlog.warning(f"[SETUP] {device} | refresh_device raised: {exc!r}")


def setup_device(device: str, force_stop_first: bool = False) -> str:
    """
    Phase 1 of prepare_target_app: get the device and its apps into a known-good state.

    Order is deliberate:
        readiness -> display/touch -> internet -> TargetApp install/version ->
        ProtonVPN install -> force-stop both apps

    Internet is checked before any install because installing over a dead
    connection just wastes a minute and then fails confusingly.  Both installs
    happen before the apps are force-stopped so the next two phases start cold.

    Returns a SIG_* signal.  FatalAPKError propagates to the controller.
    """
    dlog  = _get_device_logger(device)
    t0    = time.time()
    state = HealthState()

    dlog.info("=" * 70)
    _slog(dlog, device, "setup_device", "start",
          "PHASE 1 begin", force_stop_first=force_stop_first,
          counters=_counters_snapshot(device))
    print(f"[{device}] setup_device: starting")

    steps = (
        ("device_ready",     lambda: _sd_wait_device_ready(device, dlog, state)),
        ("display_touch",    lambda: _sd_check_display_and_touch(device, dlog)),
        ("startup_internet", lambda: _sd_startup_internet(device, dlog)),
        ("target_app_install",      lambda: _sd_target_app_install_and_version(device, dlog)),
        ("vpn_install",      lambda: _sd_vpn_install(device, dlog)),
    )

    for name, step in steps:
        if _stop_requested():
            _slog(dlog, device, "setup_device", name, "manual stop",
                  signal=SIG_MANUAL_STOP)
            return SIG_MANUAL_STOP

        t_step = time.time()
        sig    = _sig_or_stop(step())
        _slog(dlog, device, "setup_device", name, "step finished",
              elapsed=time.time() - t_step, signal=sig)

        if sig != SIG_SUCCESS:
            _slog(dlog, device, "setup_device", "end",
                  "PHASE 1 aborted", elapsed=time.time() - t0, signal=sig)
            return sig

    _sd_force_stop_apps(device, dlog)

    _slog(dlog, device, "setup_device", "end", "PHASE 1 complete",
          elapsed=time.time() - t0, signal=SIG_SUCCESS,
          counters=_counters_snapshot(device))
    print(f"[{device}] setup_device: done ({time.time() - t0:.1f}s)")
    return SIG_SUCCESS


CAP_BEFORE_TARGET_APP_CYCLES = 3   # full setup restarts inside one prepare_target_app() call


def prepare_target_app(device: str, force_stop_first: bool = False) -> bool:
    """
    Top-level device setup.  The ONLY public entry point the controller calls.

    Orchestrates the three phases and converts the internal signal vocabulary
    into the True/False the controller expects:

        setup_device  ->  setup_vpn  ->  (2s stop-aware wait)  ->  setup_target_app

    force_stop_first=True is passed for every device-opening / start-over flow
    (first open, emulator reopened, controller retry, internet-restored
    restart).  It force-stops ProtonVPN and TargetApp so setup begins from a cold
    app state.  It is NOT used during mid-task guard recovery.

    Design rules this function exists to enforce:
      * prepare_target_app() is never called recursively.  Recovery helpers return
        SIG_RESTART_BEFORE_TARGET_APP and the loop below re-runs the phases, so the
        stack depth stays flat no matter how many recoveries happen.
      * Every phase returns a signal; only this function converts to bool.
      * FatalAPKError propagates untouched — the controller stops all devices.
    """
    dlog = _get_device_logger(device)
    t0   = time.time()

    dlog.info("=" * 70)
    _slog(dlog, device, "prepare_target_app", "start", "SETUP BEGIN",
          force_stop_first=force_stop_first, counters=_counters_snapshot(device))
    record_event(device, "prepare_target_app_start", fn="prepare_target_app", phase="start",
                 force_stop_first=force_stop_first)
    print(f"[{device}] prepare_target_app: starting (force_stop_first={force_stop_first})")

    def _finish(sig: str, cycle: int) -> bool:
        ok = (sig == SIG_SUCCESS)
        _slog(dlog, device, "prepare_target_app", "end",
              "SETUP COMPLETE" if ok else "SETUP FAILED",
              elapsed=time.time() - t0, signal=sig, cycle=cycle,
              returning=ok, counters=_counters_snapshot(device))
        dlog.info("=" * 70)
        record_event(device, "prepare_target_app_done", fn="prepare_target_app", phase="end",
                     result="success" if ok else "failed", signal=sig,
                     cycle=cycle, seconds=round(time.time() - t0, 1))
        print(f"[{device}] prepare_target_app: {'done' if ok else 'FAILED'} "
              f"({time.time() - t0:.1f}s, signal={sig})")
        return ok

    try:
        for cycle in range(1, CAP_BEFORE_TARGET_APP_CYCLES + 1):
            if _stop_requested():
                return _finish(SIG_MANUAL_STOP, cycle)

            _slog(dlog, device, "prepare_target_app", "cycle", "setup cycle begin",
                  attempt=f"{cycle}/{CAP_BEFORE_TARGET_APP_CYCLES}")

            # Cold-start the two apps so each phase begins from a known state.
            if force_stop_first:
                _slog(dlog, device, "prepare_target_app", "cycle",
                      "force-stopping ProtonVPN + TargetApp before setup")
                try:
                    _adb_shell(device, "am", "force-stop",
                               "ch.protonvpn.android", timeout=5)
                    _adb_shell(device, "am", "force-stop",
                               TARGET_APP_PACKAGE, timeout=5)
                except Exception as exc:
                    dlog.warning(f"[SETUP] {device} | force-stop raised: {exc!r}")
                time.sleep(1.5)

            # ── PHASE 1 ───────────────────────────────────────────────────
            t_phase = time.time()
            sig = _sig_or_stop(setup_device(device, force_stop_first))
            _slog(dlog, device, "prepare_target_app", "phase1",
                  "setup_device returned", elapsed=time.time() - t_phase, signal=sig)

            if sig == SIG_RESTART_BEFORE_TARGET_APP:
                continue
            if sig != SIG_SUCCESS:
                return _finish(sig, cycle)

            # ── PHASE 2 ───────────────────────────────────────────────────
            t_phase = time.time()
            sig = _sig_or_stop(setup_vpn(device))
            _slog(dlog, device, "prepare_target_app", "phase2",
                  "setup_vpn returned", elapsed=time.time() - t_phase, signal=sig)

            if sig in (SIG_RESTART_BEFORE_TARGET_APP, SIG_RESTART_SETUP_VPN):
                continue
            if sig != SIG_SUCCESS:
                return _finish(sig, cycle)

            # ── stop-aware gap so the VPN route settles before TargetApp opens ──
            _slog(dlog, device, "prepare_target_app", "gap", "2s stop-aware wait before TargetApp")
            gap = stop_aware_sleep(device, 2.0, dlog)
            if gap == SIG_MANUAL_STOP:
                return _finish(SIG_MANUAL_STOP, cycle)
            if gap == SIG_RESTART_BEFORE_TARGET_APP:
                # Paused between phases; restart the cycle so setup_target_app never
                # starts against a device whose state we stopped tracking.
                _slog(dlog, device, "prepare_target_app", "gap",
                      "paused during the inter-phase gap — restarting setup cycle")
                continue

            # ── Final VPN gate before TargetApp is allowed to open ──────────────
            # setup_vpn already verifies tun0, but the tunnel can drop during the
            # 2s settle window. This is the last point where refusing is cheap:
            # after this, TargetApp is open and any leak has already happened.
            _vpn_gate = require_vpn_up_or_fail(
                device, dlog, fn="prepare_target_app", phase="pre_setup_target_app",
                issue_code="vpn_down_prepare_target_app",
                detail="setup_vpn did not leave tun0 active; refusing to open TargetApp",
            )
            if _vpn_gate == SIG_RESTART_BEFORE_TARGET_APP:
                continue
            if _vpn_gate != SIG_SUCCESS:
                _slog(dlog, device, "prepare_target_app", "pre_setup_target_app",
                      "refusing to start setup_target_app without VPN", signal=_vpn_gate)
                return _finish(_vpn_gate, cycle)

            # ── PHASE 3 ───────────────────────────────────────────────────
            t_phase = time.time()
            sig = _sig_or_stop(setup_target_app(device))
            _slog(dlog, device, "prepare_target_app", "phase3",
                  "setup_target_app returned", elapsed=time.time() - t_phase, signal=sig)

            if sig in (SIG_RESTART_BEFORE_TARGET_APP, SIG_RESTART_SETUP_TARGET_APP):
                continue
            return _finish(sig, cycle)

        # Every cycle asked for a restart and we ran out of budget.  The
        # controller's own retry loop sits above this and may try again.
        _slog(dlog, device, "prepare_target_app", "end",
              "setup cycles exhausted", attempt=f"{CAP_BEFORE_TARGET_APP_CYCLES}"
              f"/{CAP_BEFORE_TARGET_APP_CYCLES}")
        append_issue(device, "prepare_target_app_cycles_exhausted",
                     f"{CAP_BEFORE_TARGET_APP_CYCLES} full setup cycles without success",
                     fn="prepare_target_app", phase="cycle")
        return _finish(SIG_RESTART_BEFORE_TARGET_APP, CAP_BEFORE_TARGET_APP_CYCLES)

    except FatalAPKError:
        # Missing APK affects every device — let the controller stop the run.
        _slog(dlog, device, "prepare_target_app", "end",
              "FatalAPKError — propagating to controller",
              elapsed=time.time() - t0)
        raise
    except Exception:
        dlog.exception("prepare_target_app() unhandled exception")
        append_issue(device, "prepare_target_app_exception", "unhandled exception",
                     fn="prepare_target_app", phase="exception")
        return _finish(SIG_FAIL_DEVICE, 0)


def _reopen_device_capped(device: str, dlog, offline: bool = False) -> bool:
    """
    Backwards-compatible wrapper kept for runtime callers such as
    _handle_vpn_recovery_failed_full_restart().

    Both the old "offline" and "non-offline" paths now route to the correct
    new counter so the two reopen budgets stay honest:

        offline=True   the emulator was already gone  -> self-closed cap (5)
        offline=False  we are choosing to reopen it   -> program cap (2)

    Returns True when the device came back, False when the cap was exhausted
    or the reopen failed.
    """
    if offline:
        sig = recover_self_closed_device(device, dlog, phase="legacy_wrapper",
                                         fn="_reopen_device_capped")
    else:
        sig = program_reopen_device(device, dlog, reason="legacy_wrapper",
                                    phase="legacy_wrapper",
                                    fn="_reopen_device_capped")
    ok = (sig == SIG_RESTART_BEFORE_TARGET_APP)
    dlog.info(
        f"[COMPAT] _reopen_device_capped({device}, offline={offline}) "
        f"-> signal={sig} returning={ok}"
    )
    return ok

def _click_and_verify(
    device: str,
    dlog,
    tap_x: int,
    tap_y: int,
    verify_changed_from: str = None,
    verify_any_of: list = None,
    timeout: float = 5.0,
    max_clicks: int = 3,
) -> bool:
    """
    Click a point and verify the page actually changed.

    After each click, polls for up to `timeout` seconds checking:
        - If `verify_changed_from` is set: current activity no longer contains it
        - If `verify_any_of` is set: current activity contains any of these strings

    If no change detected, clicks again. Repeats up to `max_clicks` times.

    Returns True if the change was confirmed, False if all attempts exhausted.
    """
    for attempt in range(1, max_clicks + 1):
        before = _get_current_activity(device).strip()
        dlog.debug(
            f"── _click_and_verify ── attempt {attempt}/{max_clicks} "
            f"tap ({tap_x},{tap_y}), before='{before}'"
        )
        guard_check_and_recover(device, dlog, None, context="_click_and_verify")
        _raw_tap(device, tap_x, tap_y)

        t0 = time.time()
        while time.time() - t0 < timeout:
            time.sleep(0.5)
            current = _get_current_activity(device).strip()

            # Check if activity changed from the original
            if verify_changed_from and verify_changed_from not in current:
                dlog.info(
                    f"── _click_and_verify ── Activity changed from "
                    f"'{verify_changed_from}' → '{current}' ✓"
                )
                return True

            # Check if we reached one of the expected targets
            if verify_any_of:
                for frag in verify_any_of:
                    if frag in current:
                        dlog.info(
                            f"── _click_and_verify ── Reached '{frag}' ✓"
                        )
                        return True

            # If neither verification mode is set, just check it's different
            if not verify_changed_from and not verify_any_of:
                if current != before and current and "null" not in current.lower():
                    dlog.info(
                        f"── _click_and_verify ── Activity changed: "
                        f"'{before}' → '{current}' ✓"
                    )
                    return True

        dlog.warning(
            f"── _click_and_verify ── No change after {timeout:.0f}s "
            f"(attempt {attempt}/{max_clicks}) — retrying"
        )

    dlog.error(
        f"── _click_and_verify ── No change after {max_clicks} clicks "
        f"at ({tap_x},{tap_y})"
    )
    return False

vpn_stage = {}
stage_tries = {}
install_attempts = {}

# ── Legacy recovery counters ─────────────────────────────────────────────
# Only _device_reopen_offline_count and _vpn_kill_reopen_count are still live.
#   _device_reopen_count       -> superseded by _program_device_reopen_count
#   _vpn_reinstall_count       -> superseded by the shared _vpn_install_count
# Both replacements live in the SETUP CORE block with their caps enforced by
# program_reopen_device() and vpn_install_allowed().  The two names below are
# NOT redefined here: re-binding them after the core block would silently give
# the new code a second, empty counter dict and defeat the caps.
_device_reopen_offline_count: dict = {}  # legacy offline reopens
_vpn_kill_reopen_count: dict = {}        # force-stop + reopen ProtonVPN, cap CAP_VPN_KILL_REOPEN

# ── _match_vpn_label ──────────────────────────────────────────────────────────
def _match_vpn_label(
    label: str,
    boxes: list,
    dlog,
) -> tuple[int, int] | None:
    """
    Scan a pre-fetched text_detect result list for a VPN button label.
    Called by any code that already has a screenshot + OCR result and needs
    to check multiple labels without retaking a screenshot for each one.

    Exact match first, then substring match with false-positive guard.
    Returns (cx, cy) or None.
    """
    if not isinstance(boxes, list) or not boxes:
        return None

    target_lower = label.strip().lower()
    false_positive_suffixes = ("ion", "ing", "ed", "ivity", "or", "s")

    for item in boxes:
        text = item.get("text", "").strip()
        if text.lower() == target_lower:
            bbox = item.get("bbox")
            if bbox and len(bbox) == 4:
                x1, y1, x2, y2 = bbox
                cx, cy = (x1 + x2) // 2, (y1 + y2) // 2
                dlog.debug(f"── _match_vpn_label ── '{label}' exact '{text}' → ({cx},{cy})")
                return cx, cy

    for item in boxes:
        text       = item.get("text", "").strip()
        text_lower = text.lower()
        if target_lower in text_lower:
            idx   = text_lower.find(target_lower)
            after = text_lower[idx + len(target_lower):]
            if after and any(after.startswith(s) for s in false_positive_suffixes):
                continue
            bbox = item.get("bbox")
            if bbox and len(bbox) == 4:
                x1, y1, x2, y2 = bbox
                cx, cy = (x1 + x2) // 2, (y1 + y2) // 2
                dlog.debug(f"── _match_vpn_label ── '{label}' substring '{text}' → ({cx},{cy})")
                return cx, cy

    return None


# ── Per-label activity gate ───────────────────────────────────────────────────
# If the device is not on the expected activity for a given label, _find_vpn_button
# returns None immediately — no screenshot, no OCR wasted.
# Tuple value = any of the listed substrings is acceptable.
_VPN_BUTTON_ACTIVITY: dict[str, str | tuple] = {
    "connect":           "RoutingActivity",
    "change server":     "RoutingActivity",
    "cancel":            "RoutingActivity",
    "got it":            "RoutingActivity",
    "continue as guest": "AddAccountActivity",
    "not now":           "UpgradeOnboardingDialogActivity",
    "ok":                ("vpndialogs", "RoutingActivity"),
    "allow":             "vpndialogs",
}


# ==============================================================================
# UIAutomator VPN primitives  (add these near _find_vpn_button)
# ==============================================================================
import xml.etree.ElementTree as _ET


def _vpn_uia_dump(device: str, dlog) -> "_ET.Element | None":
    """
    UIAutomator XML dump → parsed root.
    Returns None if the dump fails or is empty.
    """
    try:
        _adb_shell(device, "uiautomator", "dump", "/sdcard/vpn_ui.xml", timeout=10)
        xml_raw = _adb_shell(device, "cat", "/sdcard/vpn_ui.xml", timeout=8)
        if not xml_raw or "<hierarchy" not in xml_raw:
            dlog.debug("── _vpn_uia_dump ── empty / invalid dump")
            return None
        root = _ET.fromstring(xml_raw)
        dlog.debug("── _vpn_uia_dump ── dump OK")
        return root
    except Exception as exc:
        dlog.warning(f"── _vpn_uia_dump ── exception: {exc}")
        return None

def _vpn_uia_find(
    device: str,
    label: str,
    dlog,
    *,
    exact: bool = True,
    clickable_only: bool = True,
    root: "_ET.Element | None" = None,
) -> "tuple[int, int] | None":
    if root is None:
        root = _vpn_uia_dump(device, dlog)
    if root is None:
        return None

    target = label.strip().lower()

    # Build parent map once — needed for clickable-ancestor fallback
    parent_map: dict = {}
    for parent_node in root.iter():
        for child in parent_node:
            parent_map[child] = parent_node

    def _center(node, src="text"):
        pos = _vpn_uia_bounds_center(node, label, dlog)
        if pos:
            dlog.info(f"── _vpn_uia_find ── '{label}' via {src}")
        return pos

    def _clickable_ancestor(node):
        """Walk up parent_map until we find a clickable node."""
        current = parent_map.get(node)
        while current is not None:
            if current.attrib.get("clickable", "false") == "true":
                return current
            current = parent_map.get(current)
        return None

    # Pass 1 — exact text + clickable on same node (ideal case)
    for node in root.iter("node"):
        text = (node.attrib.get("text", "") or "").strip().lower()
        match = (text == target) if exact else (target in text)
        if not match:
            continue
        if node.attrib.get("clickable", "false") == "true":
            return _center(node, "text+clickable")

    # Pass 2 — content-desc + clickable on same node
    for node in root.iter("node"):
        desc = (node.attrib.get("content-desc", "") or "").strip().lower()
        match = (desc == target) if exact else (target in desc)
        if not match:
            continue
        if node.attrib.get("clickable", "false") == "true":
            return _center(node, "content-desc+clickable")

    # Pass 3 — text on non-clickable inner node → walk up to clickable parent
    # Handles ProtonVPN compound button: FrameLayout(clickable) > TextView(text)
    if clickable_only:
        for node in root.iter("node"):
            text = (node.attrib.get("text", "") or "").strip().lower()
            match = (text == target) if exact else (target in text)
            if not match:
                continue
            ancestor = _clickable_ancestor(node)
            if ancestor is not None:
                dlog.info(
                    f"── _vpn_uia_find ── '{label}' found via non-clickable "
                    f"child → clickable ancestor"
                )
                return _vpn_uia_bounds_center(ancestor, label, dlog)
            # No clickable ancestor — return the text node's own center
            # (tap will still land on the button area)
            dlog.info(
                f"── _vpn_uia_find ── '{label}' found via non-clickable node "
                f"(no clickable ancestor) — using node center"
            )
            return _center(node, "non-clickable-text")

    # Pass 4 — any node ignoring clickability (only reached when clickable_only=False)
    for node in root.iter("node"):
        text = (node.attrib.get("text", "") or "").strip().lower()
        match = (text == target) if exact else (target in text)
        if match:
            return _center(node, "text-any")

    # Debug: log all text/desc values in dump when target not found
    all_texts = [
        (node.attrib.get("text", "") or "").strip()
        for node in root.iter("node")
        if (node.attrib.get("text", "") or "").strip()
    ]
    dlog.debug(
        f"── _vpn_uia_find ── '{label}' not found. "
        f"All text nodes in dump: {all_texts[:30]}"
    )
    return None


def _vpn_uia_bounds_center(node, label: str, dlog) -> "tuple[int, int] | None":
    """Parse [x1,y1][x2,y2] bounds and return centre."""
    bounds = node.attrib.get("bounds", "")
    m = re.match(r"\[(\d+),(\d+)\]\[(\d+),(\d+)\]", bounds)
    if not m:
        dlog.debug(f"── _vpn_uia_bounds_center ── '{label}' bad bounds {bounds!r}")
        return None
    x1, y1, x2, y2 = int(m[1]), int(m[2]), int(m[3]), int(m[4])
    cx, cy = (x1 + x2) // 2, (y1 + y2) // 2
    dlog.info(f"── _vpn_uia_find ── '{label}' bounds={bounds} → ({cx},{cy})")
    return cx, cy


def _vpn_uia_text_present(
    device: str,
    label: str,
    dlog,
    *,
    root: "_ET.Element | None" = None,
) -> bool:
    """
    Return True if ANY node contains `label` (case-insensitive),
    regardless of clickability.  Used for status checks.
    """
    if root is None:
        root = _vpn_uia_dump(device, dlog)
    if root is None:
        return False
    target = label.strip().lower()
    for node in root.iter("node"):
        text = (node.attrib.get("text", "") or "").strip().lower()
        if target in text:
            dlog.debug(f"── _vpn_uia_text_present ── '{label}' found in '{text}'")
            return True
    return False


# ==============================================================================
# _find_vpn_button  — UIAutomator, drop-in replacement for OCR version
# ==============================================================================
def _find_vpn_button(device: str, label: str) -> "tuple[int, int] | None":
    """
    Locate a ProtonVPN button by exact label via UIAutomator.
    Never confuses 'Free connection' label with the 'Connect' button.
    """
    dlog = _get_device_logger(device)
    dlog.debug(f"── _find_vpn_button ── UIAutomator search for '{label}'")
    root = _vpn_uia_dump(device, dlog)
    return _vpn_uia_find(device, label, dlog, exact=True, clickable_only=True, root=root)


# ==============================================================================
# _vpn_ui_is_connected  — UIAutomator, no OCR
# ==============================================================================
def _vpn_ui_is_connected(device: str, dlog) -> bool:
    """
    Return True if the ProtonVPN UI shows a connected state.
    Checks: Disconnect button, Protected label, browsing safely, Change server button.
    """
    root = _vpn_uia_dump(device, dlog)
    if root is None:
        return False
    for node in root.iter("node"):
        text = (node.attrib.get("text", "") or "").strip().lower()
        clickable = node.attrib.get("clickable", "false") == "true"

        if text == "disconnect" and clickable:
            dlog.debug("── _vpn_ui_is_connected ── 'Disconnect' button → connected")
            return True
        if text == "protected":
            dlog.debug("── _vpn_ui_is_connected ── 'Protected' label → connected")
            return True
        if "protected" in text and "unprotected" not in text:
            dlog.debug(f"── _vpn_ui_is_connected ── '{text}' → connected")
            return True
        if "browsing safely" in text:
            dlog.debug("── _vpn_ui_is_connected ── 'browsing safely' → connected")
            return True
        if text == "change server" and clickable:
            dlog.debug("── _vpn_ui_is_connected ── 'Change server' button → connected")
            return True

    dlog.debug("── _vpn_ui_is_connected ── no connected indicator found")
    return False


# ==============================================================================
# _classify_protonvpn_ui  — UIAutomator, full state classifier
# ==============================================================================
def _classify_protonvpn_ui(device: str, dlog=None, root=None) -> dict:
    """
    Classify the current ProtonVPN UI state via UIAutomator XML.

    States:
        disconnected_connect          — "Connect" button visible; "You are unprotected"
        disconnected_connect_fallback — "You are unprotected" visible but the Connect
                                        label/bounds are missing from the dump. Some
                                        ProtonVPN builds never expose Connect as a text
                                        node, so this is a DETECTION gap on a perfectly
                                        healthy Connect screen — callers must treat it
                                        as a Connect screen and use the fallback
                                        coordinate, never as a broken app.
        protected_change_available    — Protected + "Change server" clickable, no timer
        protected_change_timer_unavailable — Protected + "Change server" row exists but
                                          timer text present ("Available in Xs" or \\d:\\d\\d)
        connecting_or_changing        — "Protecting your digital identity" / "Changing server…"
        onboarding_welcome            — pre-login/onboarding welcome screen, before RoutingActivity
        unknown                       — none of the above matched

    Returns dict:
        {
            "state":              str,
            "connect_bounds":     tuple|None,   # (cx,cy) center of Connect button
            "change_server_bounds": tuple|None, # (cx,cy) center of Change server row
            "timer_text":         str|None,     # timer string if found
            "protected":          bool,
            "disconnect_visible": bool,
            "change_available":   bool,         # True if Change server clickable + no timer
        }
    """
    if dlog is None:
        dlog = _get_device_logger(device)
    result = {
        "state":                  "unknown",
        "connect_bounds":         None,
        "connect_bounds_loose":   None,   # substring / non-clickable match
        "connect_source":         None,   # "exact" | "loose" | None
        "change_server_bounds":   None,
        "timer_text":             None,
        "protected":              False,
        "unprotected":            False,
        "disconnect_visible":     False,
        "change_available":       False,
        "onboarding":             False,
        "texts":                  [],
    }

    # `root` may be supplied by the caller so ONE dump serves the whole fast
    # path. uiautomator dump costs 4-7s on these instances, and the previous
    # flow paid that twice on the same unchanged screen.
    if root is None:
        _t_dump = time.time()
        dlog.info(f"[VPN-UI] {device} | UIA dump start")
        root = _vpn_uia_dump(device, dlog)
        dlog.info(f"[VPN-UI] {device} | UIA dump end  elapsed={time.time() - _t_dump:.1f}s "
                  f"result={'ok' if root is not None else 'FAILED'}")
    else:
        dlog.debug(f"[VPN-UI] {device} | reusing caller-supplied UIA dump (no re-dump)")

    if root is None:
        dlog.debug("[VPN-UI] _classify_protonvpn_ui — UIAutomator dump failed")
        return result

    import re as _re

    # Collect all node texts + attributes in one pass
    connect_pos   = None
    connect_loose = None
    change_pos    = None
    timer_text    = None
    protected     = False
    disconnect    = False
    connecting    = False
    unprotected   = False
    onboarding    = False
    all_texts     = []

    for node in root.iter("node"):
        text    = (node.attrib.get("text",         "") or "").strip()
        desc    = (node.attrib.get("content-desc", "") or "").strip()
        clickable = node.attrib.get("clickable", "false") == "true"
        bounds  = node.attrib.get("bounds", "")

        def _center(b):
            """Parse '[x1,y1][x2,y2]' → ((x1+x2)//2, (y1+y2)//2)"""
            m = _re.findall(r'\d+', b)
            if len(m) == 4:
                return (int(m[0]) + int(m[2])) // 2, (int(m[1]) + int(m[3])) // 2
            return None

        tl = text.lower()
        dl = desc.lower()

        if text:
            all_texts.append(text)
        if desc:
            all_texts.append(desc)

        blob = f"{tl} {dl}".strip()

        if tl == "connect" and clickable:
            connect_pos = _center(bounds) or (960, 828)
            dlog.debug(f"[VPN-UI] found Connect button at {connect_pos}")
        elif ("connect" in blob
              and "disconnect" not in blob and "reconnect" not in blob
              and "connection" not in blob):
            # Loose match, captured in the SAME walk. Some ProtonVPN builds put
            # the label on a non-clickable child, or render it "CONNECT" /
            # "Connect now" — previously this needed a second full dump to find.
            c = _center(bounds)
            if c and connect_loose is None:
                connect_loose = c
                dlog.debug(f"[VPN-UI] loose Connect match {text or desc!r} at {c}")

        if any(w in blob for w in _VPN_WELCOME_MARKERS):
            onboarding = True

        if tl == "change server" and clickable:
            change_pos = _center(bounds) or (960, 828)
            dlog.debug(f"[VPN-UI] found Change server button at {change_pos}")

        if tl == "protected" or ("protected" in tl and "unprotected" not in tl):
            protected = True
        if "unprotected" in tl or "unprotected" in dl:
            unprotected = True
        if tl in ("disconnect",) and clickable:
            disconnect = True
        if "protecting your digital identity" in tl or "changing server" in tl:
            connecting = True

        # Timer detection: "Available in 40 seconds" / "00:35" / "09:56"
        if "available in" in dl.lower() or _re.search(r'\b\d{1,2}:\d{2}\b', text):
            timer_text = text or desc
            dlog.debug(f"[VPN-UI] timer text found: {timer_text!r}")

        # Timer text nodes near Change server row
        if _re.search(r'\b\d{1,2}:\d{2}\b', tl):
            timer_text = text
            dlog.debug(f"[VPN-UI] timer text (time pattern): {timer_text!r}")

    # ── Classify ──────────────────────────────────────────────────────────────
    if timer_text is not None:
        # Timer text means Change Server is currently unavailable regardless of
        # whether the Change server node is clickable.  Log explicitly.
        dlog.info(f"[VPN-UI] timer detected — Change Server unavailable  timer={timer_text!r}")

    if connecting:
        result["state"] = "connecting_or_changing"
    elif protected and timer_text is not None:
        # Timer present → Change Server unavailable even if change_pos node exists.
        result["state"] = "protected_change_timer_unavailable"
        result["change_available"] = False
        dlog.info("[VPN-UI] Protected + timer — not clicking Change Server")
    elif protected and change_pos is not None:
        result["state"] = "protected_change_available"
        result["change_available"] = True
    elif onboarding and connect_pos is None and not unprotected:
        # First-launch welcome screen: no Connect button exists yet.
        result["state"] = "onboarding_welcome"
        dlog.info("[VPN-UI] ProtonVPN welcome/onboarding screen detected — "
                  "state=onboarding_welcome (no Connect button on this screen)")
    elif connect_pos is not None:
        result["state"] = "disconnected_connect"
    elif unprotected:
        # Unprotected screen with no readable Connect label/bounds.
        #
        # Previously fell through to "unknown", which sent the runtime and
        # change-server paths into force-stop/reinstall escalation for what is
        # only a text-detection gap. setup_vpn already worked around this with
        # _svpn_unprotected_screen(); classifying it here fixes the shared paths
        # too.
        result["state"] = "disconnected_connect_fallback"
        result["connect_bounds"] = None
        dlog.info("[VPN-UI] unprotected screen but no Connect label/bounds — "
                  "state=disconnected_connect_fallback (detection gap, not a "
                  "broken app)")
    elif protected or disconnect:
        # Protected but no Change server visible and no timer
        result["state"] = "protected_change_available"
        result["protected"] = True
    # else: remains "unknown"

    result["protected"]            = protected
    result["unprotected"]          = unprotected
    result["onboarding"]           = onboarding
    result["disconnect_visible"]   = disconnect
    result["connect_bounds"]       = connect_pos
    result["connect_bounds_loose"] = connect_loose
    result["connect_source"]       = ("exact" if connect_pos
                                      else ("loose" if connect_loose else None))
    result["change_server_bounds"] = change_pos
    result["timer_text"]           = timer_text
    result["texts"]                = all_texts

    dlog.info(
        f"[VPN-UI] state={result['state']!r} "
        f"protected={protected} unprotected={unprotected} onboarding={onboarding} "
        f"disconnect={disconnect} connect_exact={connect_pos} "
        f"connect_loose={connect_loose} source={result['connect_source']} "
        f"change_pos={change_pos} timer={timer_text!r}"
    )
    return result


# Every state that means "this is the disconnected Connect screen".  Consumers
# must test against this set, not against "disconnected_connect" alone, or the
# fallback state silently reads as an unknown page.
VPN_CONNECT_SCREEN_STATES = ("disconnected_connect", "disconnected_connect_fallback")


def _vpn_connect_click_point(device: str, dlog, ui: dict) -> "tuple[int, int]":
    """
    Where to tap for Connect, given a classifier result.

    Detected bounds always win; the orientation-derived fallback coordinate is
    only used when nothing could be read.
    """
    pos = (ui or {}).get("connect_bounds")
    if pos:
        dlog.info(f"[VPN-UI] using detected Connect bounds {pos}")
        return pos
    pos = _svpn_connect_fallback_coord(device, dlog)
    dlog.info(f"[VPN-UI] no Connect bounds — using fallback coordinate {pos}")
    return pos
def _dismiss_onboarding(device: str, dlog) -> bool:
    """
    Dismiss the ProtonVPN UpgradeOnboarding dialog via UIAutomator.
    Falls back to Back key if no button found.
    """
    root = _vpn_uia_dump(device, dlog)
    for candidate in ("Not now", "Maybe later", "Skip", "No thanks"):
        pos = _vpn_uia_find(device, candidate, dlog,
                            exact=True, clickable_only=True, root=root)
        if pos is not None:
            nx, ny = pos
            dlog.info(f"── _dismiss_onboarding ── Clicking '{candidate}' at ({nx},{ny})")
            _adb_shell(device, "input", "tap", str(nx), str(ny))
            time.sleep(1)
            return True
    dlog.warning("── _dismiss_onboarding ── No dismiss button found — pressing Back")
    press_back(device)
    time.sleep(1)
    return True


# ==============================================================================
# _vpn_tap_ok_allow  — UIAutomator helper for vpndialogs
# ==============================================================================
def _vpn_tap_ok_allow(device: str, dlog) -> bool:
    """
    Find and tap OK / Allow in a VPN permission dialog using UIAutomator.
    Falls back to hardcoded position (1288,671) if not found.
    Returns True always (caller continues regardless).
    """
    root = _vpn_uia_dump(device, dlog)
    for btn in ("OK", "Allow", "ALLOW", "Ok", "Accept"):
        pos = _vpn_uia_find(device, btn, dlog, exact=True, clickable_only=True, root=root)
        if pos is not None:
            ax, ay = pos
            dlog.info(f"── _vpn_tap_ok_allow ── Tapping '{btn}' at ({ax},{ay})")
            _adb_shell(device, "input", "tap", str(ax), str(ay))
            return True
    dlog.warning("── _vpn_tap_ok_allow ── Not found via UIAutomator — hardcoded (1288,671)")
    _adb_shell(device, "input", "tap", "1288", "671")
    return True


# ==============================================================================
# _setup_vpn_inner  — ALL VPN interaction via UIAutomator, zero OCR/screenshots
# ==============================================================================
def vpn_activity(device: str) -> bool:
    """
    Returns True if the VPN tunnel (tun0) interface is active (UP).
    """
    link_out = _adb_shell(device, "ip", "link", "show", "tun0")
    result   = "UP,LOWER_UP" in link_out
    # [DIAG] log raw output so we know exactly what the kernel reports
    _get_device_logger(device).debug(
        f"[DIAG] vpn_activity ── raw: {link_out.strip()!r} → {'UP' if result else 'DOWN'}"
    )
    return result


def on_home_screen(device: str) -> bool:
    """
    Returns True if the device is currently showing the BlueStacks home screen.
    """
    out = _adb_shell(device, "dumpsys", "window", "windows")
    for line in out.splitlines():
        if "mCurrentFocus" in line:
            result = "HomeActivity" in line
            # [DIAG] log what focus line was actually seen
            _get_device_logger(device).debug(
                f"[DIAG] on_home_screen ── focus line: {line.strip()!r} → {result}"
            )
            return result
    _get_device_logger(device).debug("[DIAG] on_home_screen ── mCurrentFocus line NOT FOUND in dumpsys output")
    return False


def _get_current_activity(device: str) -> str:
    """
    Return the current foreground activity string from mCurrentFocus.
    """
    out = _adb_shell(device, "dumpsys", "window", "windows")
    for line in out.splitlines():
        if "mCurrentFocus" in line:
            start = line.find("u0 ")
            if start != -1:
                activity = line[start + 3:].rstrip("}")
                # [DIAG] log every resolution so we can trace exact activity transitions
                _get_device_logger(device).debug(
                    f"[DIAG] _get_current_activity ── {activity.strip()!r}"
                )
                return activity
            _get_device_logger(device).debug(
                f"[DIAG] _get_current_activity ── raw line (no u0): {line.strip()!r}"
            )
            return line
    _get_device_logger(device).debug("[DIAG] _get_current_activity ── mCurrentFocus NOT FOUND")
    return ""


def open_vpn(device: str) -> bool:
    """
    Launches ProtonVPN via am start. Returns True on success.
    """
    dlog = _get_device_logger(device)
    t_start = time.time()
    dlog.info("── open_vpn ── Launching ProtonVPN via am start")
    dlog.info(f"[DIAG] open_vpn ── call timestamp: {t_start:.3f}")
    try:
        result = subprocess.run(
            ["adb", "-s", device, "shell", "am", "start",
             "-n", "ch.protonvpn.android/.RoutingActivity"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        out     = (result.stdout or "") + (result.stderr or "")
        success = "Starting: Intent" in out or "brought to the front" in out
        elapsed = time.time() - t_start
        dlog.info(
            f"── open_vpn ── am start result: {'success' if success else 'FAILED'} | "
            f"output: {out.strip()!r}"
        )
        dlog.info(
            f"[DIAG] open_vpn ── completed in {elapsed:.3f}s | "
            f"returncode={result.returncode}"
        )
        return success
    except Exception as e:
        dlog.error(f"── open_vpn ── Exception: {e}")
        dlog.error(f"[DIAG] open_vpn ── exception after {time.time()-t_start:.3f}s: {e}")
        return False


# ==============================================================================
# _vpn_change_server  — UIAutomator only
# ==============================================================================
# Per-device state for _vpn_change_server failure reason and instability tracking
_last_vpn_change_failure_reason: dict = {}    # device → str
_last_guard_recovery_reason:     dict = {}    # device → str  (e.g. "device_closed_recovered")
_vpn_app_unstable_timestamps:    dict = {}    # device → [float, ...]
_vpn_reinstall_for_instability:  dict = {}    # device → int  (0 or 1)
# Recursion guard: True while _force_reset_vpn_only is active for a device,
# prevents _vpn_change_server (called from within) from looping back.
_vpn_only_reset_active:          dict = {}    # device → bool


def _vpn_change_health_check(
    device: str,
    dlog,
    expect_vpn_foreground: bool = False,
) -> dict:
    """
    Quick health check called at critical points inside _vpn_change_server.
    TargetAppGuard is paused while we are inside the VPN app, so this function
    performs the checks that guard would normally catch.

    Returns:
        {"ok": True}
        {"ok": False, "reason": "device_closed"}
        {"ok": False, "reason": "adb_reconnect_failed"}
        {"ok": False, "reason": "adb_lost"}       — emulator alive but ADB still gone
        {"ok": False, "reason": "vpn_app_left_foreground"}
    """
    # ── A/B: ADB state ────────────────────────────────────────────────────────
    if not _adb_ping(device):
        emulator_alive = is_emulator_process_alive(device)

        if not emulator_alive:
            dlog.warning(
                f"[Scenario D][change_server] emulator closed during VPN server change "
                f"— confirmed by netstat (port not LISTENING)"
            )
            return {"ok": False, "reason": "device_closed"}

        # Emulator alive but ADB disconnected — KEEP reconnecting until ADB
        # comes back or netstat says the emulator is closed. VPN tunnel
        # transitions can take longer than a fixed timeout; failing on a short
        # window produced false adb_reconnect_failed reports.
        dlog.warning(
            f"[Scenario C][change_server] ADB lost but emulator alive — waiting"
        )
        print(f"[Scenario C][change_server][{device}] ADB lost but emulator alive — waiting")
        t_rec    = time.time()
        last_log = t_rec
        while True:
            if _stop_requested():
                elapsed = time.time() - t_rec
                dlog.info(
                    f"[Scenario C][change_server] stop requested while waiting for ADB "
                    f"— exiting (elapsed={elapsed:.1f}s)"
                )
                print(f"[Scenario C][change_server][{device}] stop requested — exiting")
                return {"ok": False, "reason": "stopped"}

            if not is_emulator_process_alive(device):
                elapsed = time.time() - t_rec
                dlog.warning(
                    f"[Scenario D][change_server] emulator closed during ADB wait"
                    f" — confirmed by netstat (elapsed={elapsed:.1f}s)"
                )
                print(f"[Scenario D][change_server][{device}] emulator closed during ADB wait")
                return {"ok": False, "reason": "device_closed"}

            _adb_connect_quiet(device)
            time.sleep(1.0)
            if _adb_ping(device):
                elapsed = time.time() - t_rec
                dlog.info(
                    f"[Scenario C][change_server] ADB restored after {elapsed:.1f}s"
                    f" — continuing ✓"
                )
                print(f"[Scenario C][change_server][{device}] ADB restored after {elapsed:.1f}s — continuing")
                return {"ok": True}

            now = time.time()
            if now - last_log >= 10.0:
                dlog.info(
                    f"[Scenario C][change_server] still waiting for ADB, "
                    f"elapsed={now - t_rec:.0f}s"
                )
                last_log = now

    # ── C: VPN foreground check (when inside VPN navigation) ─────────────────
    if expect_vpn_foreground:
        cur = _get_current_activity(device).strip()
        # ProtonVPN activity or Android VPN permission dialog are both acceptable
        vpn_fg = (
            "ch.protonvpn.android" in cur
            or "com.android.vpndialogs" in cur
        )
        if not vpn_fg:
            dlog.warning(
                f"[Scenario B5][change_server] VPN app left foreground: {cur!r}"
            )
            return {"ok": False, "reason": "vpn_app_left_foreground"}

    return {"ok": True}


def _vpn_change_server(
    device:       str,
    dlog,
    guard:        "TargetAppGuard | None" = None,
    force_change: bool = False,
) -> bool:
    """
    Change the ProtonVPN server and wait for tun0 to come back UP.

    Rules:
    - Never calls setup_vpn().
    - Never force-stops ProtonVPN or TargetApp.
    - Performs exactly 3 full attempts.
    - Handles emulator close (Scenario D), ADB disconnect (Scenario C),
      and VPN app instability (Scenario B5) internally, without TargetAppGuard.
    - Sets _last_vpn_change_failure_reason[device] on failure.
    - Returns True on success, False on any failure.

    force_change=True: change server even if already Protected/tun0 up.
    Used when VPN dropped >3 times in 60s or CI appeared >5 times in 60s.

    _last_vpn_change_failure_reason[device] values:
        "device_closed"         — emulator went away mid-change
        "adb_reconnect_failed"  — emulator alive but ADB won't come back
        "vpn_app_unstable"      — VPN app kept leaving foreground repeatedly
        "vpn_app_not_foreground"— VPN could not be brought foreground
        "button_missing"        — Change Server button never appeared
        "no_tun0"               — 3 attempts exhausted, tun0 never confirmed
        "permission_failed"     — VPN permission dialog handling failed
    """
    # ── Fix 1: Auto-resolve guard from _target_app_guards if not passed by caller ────
    if guard is None:
        guard = _target_app_guards.get(device)

    # Clear any stale failure reason from a previous call so callers never
    # act on an out-of-date reason after a new call succeeds or fails differently.
    _last_vpn_change_failure_reason.pop(device, None)

    _t_vcs_start = time.time()
    _slog(dlog, device, "_vpn_change_server", "entry",
          "runtime VPN change-server begin", force_change=force_change,
          counters=_counters_snapshot(device))

    # ── Host internet gate ────────────────────────────────────────────────────
    # Nothing below this line is worth doing while the PC itself is offline:
    # clicking Connect, changing servers or reinstalling ProtonVPN would all
    # fail and burn recovery budget for a cause that has nothing to do with
    # this device.  Pause in place until host internet returns instead.
    if not host_internet_ok():
        _slog(dlog, device, "_vpn_change_server", "entry",
              "host internet DOWN at entry — pausing before any VPN action")
        pause_sig = pause_controller_until_host_internet_back(
            device, dlog, phase="vpn_change_server", fn="_vpn_change_server"
        )
        if pause_sig == SIG_MANUAL_STOP:
            _last_vpn_change_failure_reason[device] = "manual_stop"
            return False
        _slog(dlog, device, "_vpn_change_server", "entry",
              "host internet back — continuing with VPN recovery")

    # ── Pause TargetAppGuard — it would see RoutingActivity as unexpected page ──────
    # Both mechanisms are used on purpose: the page-check lockout covers the
    # window before the thread actually stops, and stopping the thread covers
    # the long tail while we are navigating ProtonVPN.
    _saved_target_app_stage = None
    target_app_guard_pause_page_checks(device, 300.0,
                                reason="vpn_change_server", dlog=dlog)
    if guard is not None:
        with guard._stage_lock:
            _saved_target_app_stage = guard._stage
        _slog(dlog, device, "_vpn_change_server", "entry",
              "pausing TargetAppGuard for VPN navigation", stage=_saved_target_app_stage)
        guard.stop()

    def _set_failure(reason: str) -> bool:
        _last_vpn_change_failure_reason[device] = reason
        _slog(dlog, device, "_vpn_change_server", "exit",
              "returning False", reason=reason,
              elapsed=time.time() - _t_vcs_start,
              counters=_counters_snapshot(device))
        return False

    def _succeed(where: str) -> bool:
        """
        Common success path.

        The tunnel being up is not enough — the caller is a task or Loading()
        that needs Target Application back in the foreground.  Reopening TargetApp here (and
        confirming it) is what lets callers resume immediately instead of
        tripping TargetAppGuard's unexpected_page check on the next tick.
        """
        _slog(dlog, device, "_vpn_change_server", "success",
              "tunnel restored — reopening TargetApp before returning", where=where,
              elapsed=time.time() - _t_vcs_start)
        try:
            open_target_app(device, context="vpn_change_server success")
        except Exception as exc:
            dlog.warning(f"[VPN-CHG] {device} | open_target_app raised: {exc!r}")

        if _wait_for_target_app_foreground(device, dlog, timeout=45.0):
            _slog(dlog, device, "_vpn_change_server", "success",
                  "TargetApp foreground confirmed", where=where,
                  elapsed=time.time() - _t_vcs_start, returning=True)
            return True

        _slog(dlog, device, "_vpn_change_server", "success",
              "tunnel is up but TargetApp never came back to the foreground",
              where=where, elapsed=time.time() - _t_vcs_start)
        return _set_failure("target_app_not_foreground_after_vpn_fix")

    def _hc(expect_fg: bool = False) -> dict:
        """Inline health-check shorthand."""
        return _vpn_change_health_check(device, dlog, expect_vpn_foreground=expect_fg)

    try:
        # ── Track whether a VPN reinstall has already been done ───────────────
        _vpn_reinstall_done = _vpn_reinstall_for_instability.get(device, 0) >= 1

        # ── Inner helper: run one full cycle of 3 change-server attempts ──────
        # Returns: True (success), False (failed), or the string "reinstall_needed"
        # when VPN app instability reaches threshold mid-cycle.
        # Callers must never pass after_reinstall=True themselves — it is set
        # internally so the post-reinstall retry cannot recurse further.
        def _run_attempts(after_reinstall: bool = False) -> "bool | str":
            nonlocal _vpn_reinstall_done

            cycle_label = "post-reinstall" if after_reinstall else "normal"
            dlog.info(f"── [Scenario B3] starting {cycle_label} 3-attempt cycle")

            # ── Inner helper: try clicking Connect if UI shows disconnected state ─
            def _try_click_connect_if_visible(reason: str) -> "bool | None":
                """
                Classify ProtonVPN UI and click Connect if visible/disconnected.
                Returns:
                    True  — Connect clicked and tun0 confirmed UP.
                    False — Connect clicked but tun0 did not come UP within 30s.
                    None  — Connect/disconnected UI not visible; caller should decide.
                """
                _ui = _classify_protonvpn_ui(device, dlog)
                _st = _ui["state"]
                # Both Connect-screen states count. Treating only
                # "disconnected_connect" as a Connect screen meant the fallback
                # state fell through to a text search and then to None, so a
                # healthy screen with an unreadable label looked like an
                # unknown page.
                _cp = None
                if _st in VPN_CONNECT_SCREEN_STATES:
                    _cp = _ui.get("connect_bounds")
                if _cp is None:
                    _cp = _find_vpn_button(device, "Connect")
                if _cp is None and _st == "disconnected_connect_fallback":
                    _cp = _svpn_connect_fallback_coord(device, dlog)
                    dlog.info(
                        f"[VPN-RECOVERY] {reason}: unprotected screen with no "
                        f"Connect label — using fallback coordinate {_cp}")
                if _cp is None:
                    return None
                dlog.info(
                    f"[VPN-RECOVERY] {reason}: "
                    f"disconnected/Connect visible — clicking Connect "
                    f"instead of Change server (state={_st!r} pos={_cp})"
                )
                _cx2, _cy2 = _cp
                _adb_shell(device, "input", "tap", str(_cx2), str(_cy2))
                time.sleep(0.5)
                _cur2 = _get_current_activity(device)
                if "com.android.vpndialogs" in _cur2:
                    dlog.info("[VPN-RECOVERY] Permission dialog after Connect — tapping OK")
                    _vpn_tap_ok_allow(device, dlog)
                    time.sleep(1.0)
                _t2 = time.time()
                while time.time() - _t2 < 30.0:
                    if vpn_activity(device):
                        dlog.info("[VPN-RECOVERY] tun0 UP after Connect click — success")
                        return True
                    time.sleep(1.0)
                dlog.warning("[VPN-RECOVERY] tun0 not UP after Connect click")
                return False

            for _attempt in range(1, 4):
                # Charge exactly one real attempt to the shared counter here —
                # not the whole cap before the loop starts. This is the counter
                # every FINAL COUNTERS / Issues / recovery-reason readout reads,
                # so it must reflect how many attempts actually ran.
                _change_server_attempts[device] = min(
                    _ctr_get(_change_server_attempts, device) + 1,
                    CAP_CHANGE_SERVER_ATTEMPTS,
                )
                dlog.info(f"── [Scenario B3] change-server attempt {_attempt}/3 ({cycle_label})")

                # ── Health check before open_vpn ──────────────────────────────
                hc = _hc()
                if not hc["ok"]:
                    if hc["reason"] == "device_closed":
                        dlog.error(f"[Scenario D][change_server] confirmed emulator closed by netstat/process")
                        dlog.error(f"[Scenario D][change_server] returning False with reason=device_closed")
                        _set_failure("device_closed"); return False
                    _set_failure(hc["reason"]); return False

                # ── Open VPN app (no force-stop) ──────────────────────────────
                go_home(device)
                if not open_vpn(device):
                    dlog.warning(
                        f"── [Scenario B3] open_vpn() failed on attempt {_attempt}/3 "
                        f"— health checking"
                    )
                    hc = _hc()
                    if not hc["ok"]:
                        if hc["reason"] == "device_closed":
                            dlog.error("[Scenario D][change_server] confirmed emulator closed by netstat/process")
                            dlog.error("[Scenario D][change_server] returning False with reason=device_closed")
                            _set_failure("device_closed"); return False
                        _set_failure(hc["reason"]); return False
                    time.sleep(2.0)
                    continue

                # ── Grace window 3s after open_vpn before counting fg loss ────
                dlog.info(
                    f"── [Scenario B3] grace window (3s) after open_vpn "
                    f"— waiting for ProtonVPN foreground"
                )
                t_grace   = time.time()
                vpn_in_fg = False
                while time.time() - t_grace < 3.0:
                    hc_g = _hc()
                    if not hc_g["ok"]:
                        if hc_g["reason"] == "device_closed":
                            dlog.error("[Scenario D][change_server] confirmed emulator closed during grace")
                            _set_failure("device_closed"); return False
                        _set_failure(hc_g["reason"]); return False
                    cur_g = _get_current_activity(device).strip()
                    if "ch.protonvpn.android" in cur_g or "com.android.vpndialogs" in cur_g:
                        vpn_in_fg = True
                        break
                    time.sleep(0.5)
                dlog.info(
                    f"── [Scenario B3] grace done — "
                    f"vpn_in_fg={vpn_in_fg} after {time.time()-t_grace:.1f}s"
                )

                # ── Wait for RoutingActivity (20s, 1s poll + health checks) ───
                dlog.info(
                    f"── [Scenario B3] waiting for RoutingActivity (20s) — attempt {_attempt}"
                )
                routing_reached = False
                t_routing       = time.time()

                while time.time() - t_routing < 20.0:
                    hc = _hc(expect_fg=True)
                    if not hc["ok"]:
                        if hc["reason"] == "device_closed":
                            dlog.error("[Scenario D][change_server] confirmed emulator closed by netstat/process")
                            dlog.error("[Scenario D][change_server] returning False with reason=device_closed")
                            _set_failure("device_closed"); return False

                        if hc["reason"] in ("adb_reconnect_failed", "adb_lost"):
                            _set_failure(hc["reason"]); return False

                        if hc["reason"] == "vpn_app_left_foreground":
                            now_b5 = time.time()
                            ts_b5  = _vpn_app_unstable_timestamps.setdefault(device, [])
                            ts_b5.append(now_b5)
                            _vpn_app_unstable_timestamps[device] = [
                                t for t in ts_b5 if now_b5 - t <= 60.0
                            ]
                            vpn_left_fg_count = len(_vpn_app_unstable_timestamps[device])
                            dlog.warning(
                                f"[Scenario B5][change_server] VPN app left foreground "
                                f"(#{vpn_left_fg_count} in 60s) during RoutingActivity wait"
                            )
                            if vpn_left_fg_count >= 3:
                                if _vpn_reinstall_done or after_reinstall:
                                    dlog.error(
                                        "[Scenario B5][change_server] VPN app still unstable "
                                        "after reinstall — giving up"
                                    )
                                    _set_failure("vpn_app_unstable"); return False
                                # Signal caller to reinstall and retry
                                return "reinstall_needed"
                            else:
                                open_vpn(device)
                                t_routing = time.time()
                                time.sleep(1.0)
                                continue

                    cur = _get_current_activity(device).strip()
                    if "RoutingActivity" in cur or "ch.protonvpn.android" in cur:
                        routing_reached = True
                        break
                    time.sleep(1.0)

                if not routing_reached:
                    dlog.warning(f"── [Scenario B3] RoutingActivity not reached on attempt {_attempt}/3")
                    continue

                dlog.info(f"── [Scenario B3] RoutingActivity confirmed (attempt {_attempt})")

                # ── force_change=False: skip if already Protected ─────────────
                if not force_change and vpn_activity(device):
                    ui_connected = (
                        _vpn_uia_text_present(device, "Disconnect", dlog) or
                        _vpn_uia_text_present(device, "Protected",  dlog) or
                        _vpn_uia_text_present(device, "browsing safely", dlog)
                    )
                    if ui_connected:
                        dlog.info(
                            f"── [Scenario B3] VPN already Protected/tun0 up "
                            f"(force_change=False) — returning success ✓"
                        )
                        go_home(device); return True

                # ── Classify ProtonVPN UI state before deciding what to click ──
                hc = _hc(expect_fg=True)
                if not hc["ok"]:
                    if hc["reason"] == "device_closed":
                        dlog.error("[Scenario D][change_server] confirmed emulator closed by netstat/process")
                        dlog.error("[Scenario D][change_server] returning False with reason=device_closed")
                        _set_failure("device_closed"); return False
                    _set_failure(hc["reason"]); return False

                ui_state = _classify_protonvpn_ui(device, dlog)
                state = ui_state["state"]
                dlog.info(f"[VPN-UI] state={state!r}")

                # ── Handle Connect screen (5A) ──────────────────────────────────
                # Includes disconnected_connect_fallback: same screen, label just
                # was not readable.
                if state in VPN_CONNECT_SCREEN_STATES:
                    dlog.info(f"[VPN-UI] Connect screen (state={state!r}) — "
                              f"clicking Connect")
                    cx, cy = _vpn_connect_click_point(device, dlog, ui_state)
                    _adb_shell(device, "input", "tap", str(cx), str(cy))
                    time.sleep(0.5)
                    # Handle VPN permission dialog
                    cur_after = _get_current_activity(device)
                    if "com.android.vpndialogs" in cur_after:
                        dlog.info("[VPN-UI] Permission dialog after Connect — tapping OK")
                        _vpn_tap_ok_allow(device, dlog)
                        time.sleep(1.0)
                    # Poll tun0 for 30s
                    t_conn = time.time()
                    confirmed_c = False
                    while time.time() - t_conn < 30.0:
                        if vpn_activity(device):
                            dlog.info("[VPN-UI] tun0 UP — success after Connect click")
                            confirmed_c = True
                            break
                        time.sleep(1.0)
                    if confirmed_c:
                        go_home(device); return True
                    # Not connected after 30s — fall through to next attempt
                    dlog.warning("[VPN-UI] tun0 not UP after Connect click — retrying")
                    continue

                # ── Handle Protected + timer (5C): do NOT click Change Server ──
                if state == "protected_change_timer_unavailable":
                    dlog.info(
                        f"[VPN-UI] Change Server unavailable/timer — not clicking, "
                        f"VPN protected  timer={ui_state['timer_text']!r}"
                    )
                    # VPN is already connected (Protected); treat as success.
                    go_home(device); return True

                # ── Handle connecting/changing state (5D) ──────────────────────
                if state == "connecting_or_changing":
                    dlog.info("[VPN-UI] connecting/changing — waiting for tun0")
                    t_wait = time.time()
                    confirmed_w = False
                    while time.time() - t_wait < 30.0:
                        if vpn_activity(device):
                            dlog.info("[VPN-UI] tun0 UP — success after connecting/changing wait")
                            confirmed_w = True
                            break
                        time.sleep(1.0)
                    if confirmed_w:
                        go_home(device); return True
                    # Timed out — re-classify and continue to Change Server if available
                    ui_state = _classify_protonvpn_ui(device, dlog)
                    state    = ui_state["state"]
                    dlog.info(f"[VPN-UI] re-classified after connecting wait: state={state!r}")
                    if state == "protected_change_timer_unavailable":
                        dlog.info("[VPN-UI] Change Server unavailable/timer after wait — treating as connected")
                        go_home(device); return True
                    if not ui_state["change_available"]:
                        dlog.warning("[VPN-UI] still not connected and Change Server not available — retrying")
                        continue

                # ── Handle unknown UI state ────────────────────────────────────
                # "unknown" can mean the classifier missed a disconnected screen
                # (e.g. partial UIA dump showed Connect but was not classified).
                # Check for Connect before treating it as wrong screen/reopen.
                if state == "unknown":
                    _unk_result = _try_click_connect_if_visible(
                        f"state=unknown attempt {_attempt}/3"
                    )
                    if _unk_result is True:
                        go_home(device); return True
                    if _unk_result is False:
                        dlog.warning(
                            "[VPN-RECOVERY] state=unknown: Connect clicked but tun0 "
                            f"not UP — retrying (attempt {_attempt}/3)"
                        )
                        continue
                    # _unk_result is None — Connect not visible, likely launcher/wrong screen
                    dlog.warning(
                        f"[VPN-RECOVERY] ProtonVPN UI not ready/wrong screen "
                        f"(state=unknown, Connect not visible) — reopening VPN "
                        f"(attempt {_attempt}/3)"
                    )
                    open_vpn(device)
                    time.sleep(2.0)
                    continue

                # ── Find + click Change Server (5B) ────────────────────────────
                # Only reached when state==protected_change_available or after
                # connecting_or_changing timeout with change_available=True.
                if ui_state.get("timer_text"):
                    dlog.info(
                        f"[VPN-UI] skipping _find_vpn_button because timer/unavailable is present "
                        f"(timer={ui_state['timer_text']!r})"
                    )
                    change_pos = None
                else:
                    change_pos = ui_state.get("change_server_bounds") or _find_vpn_button(device, "Change server")
                if change_pos is None:
                    dlog.warning(f"── [Scenario B3] 'Change server' not found on attempt {_attempt}/3")
                    hc = _hc(expect_fg=True)
                    if not hc["ok"]:
                        if hc["reason"] == "device_closed":
                            _set_failure("device_closed"); return False
                        now_b5 = time.time()
                        ts_b5  = _vpn_app_unstable_timestamps.setdefault(device, [])
                        ts_b5.append(now_b5)
                        _vpn_app_unstable_timestamps[device] = [
                            t for t in ts_b5 if now_b5 - t <= 60.0
                        ]
                        if len(_vpn_app_unstable_timestamps[device]) >= 3:
                            if _vpn_reinstall_done or after_reinstall:
                                _set_failure("vpn_app_unstable"); return False
                            return "reinstall_needed"
                    # Before declaring button_missing, check whether ProtonVPN is
                    # showing the disconnected/Connect screen (classifier may have
                    # returned unknown or change_server_bounds may have been missing).
                    _cs_result = _try_click_connect_if_visible(
                        f"Change server missing attempt {_attempt}/3"
                    )
                    if _cs_result is True:
                        go_home(device); return True
                    if _cs_result is False:
                        # Connect clicked but tun0 didn't come up — retry
                        dlog.warning(
                            "[VPN-RECOVERY] change_pos None: Connect clicked but tun0 not UP "
                            f"— retrying (attempt {_attempt}/3)"
                        )
                        continue
                    # _cs_result is None — Connect not visible either
                    if _attempt == 3:
                        _set_failure("button_missing"); return False
                    time.sleep(2.0)
                    continue

                cx, cy = change_pos
                dlog.info(f"── [Scenario B3] Clicking Change server at ({cx},{cy}) attempt {_attempt}")
                _adb_shell(device, "input", "tap", str(cx), str(cy))

                # ── Health check immediately after click ───────────────────────
                time.sleep(0.5)
                hc = _hc()
                if not hc["ok"]:
                    if hc["reason"] == "device_closed":
                        dlog.error("[Scenario D][change_server] confirmed emulator closed by netstat/process")
                        dlog.error("[Scenario D][change_server] returning False with reason=device_closed")
                        _set_failure("device_closed"); return False
                    _set_failure(hc["reason"]); return False

                # ── Stabilise ADB after routing-table shift ────────────────────
                time.sleep(1.0)
                _t_stab = time.time()
                for _ in range(10):
                    try:
                        subprocess.run(["adb", "connect", device], capture_output=True, timeout=2)
                    except Exception:
                        pass
                    if _adb_get_state(device) == "device":
                        dlog.info(f"── [Scenario B3] ADB stabilised ({time.time()-_t_stab:.1f}s) ✓")
                        break
                    time.sleep(0.5)

                # ── tun0/Protected wait (30s, 1s poll, VPN fg check) ───────────
                dlog.info(f"── [Scenario B3] Polling tun0 (30s) — attempt {_attempt}")
                t_poll           = time.time()
                confirmed        = False
                conn_req_handled = False

                while time.time() - t_poll < 30.0:
                    # Check tun0/protected FIRST — success wins over any foreground event.
                    # This prevents a simultaneous connect+foreground-loss from being
                    # wrongly counted as VPN app instability.
                    if vpn_activity(device):
                        confirmed = True
                        break

                    # Foreground health check (only runs when tun0 is not yet confirmed)
                    hc = _hc(expect_fg=True)
                    if not hc["ok"]:
                        if hc["reason"] == "device_closed":
                            dlog.error(
                                "[Scenario D][change_server] confirmed emulator closed "
                                "by netstat/process during tun0 wait"
                            )
                            dlog.error(
                                "[Scenario D][change_server] returning False with reason=device_closed"
                            )
                            _set_failure("device_closed"); return False
                        if hc["reason"] in ("adb_reconnect_failed", "adb_lost"):
                            _set_failure(hc["reason"]); return False
                        if hc["reason"] == "vpn_app_left_foreground":
                            # Re-check tun0 once more before counting instability —
                            # VPN may have connected at the exact moment it went Home
                            if vpn_activity(device):
                                confirmed = True
                                break
                            now_b5 = time.time()
                            ts_b5  = _vpn_app_unstable_timestamps.setdefault(device, [])
                            ts_b5.append(now_b5)
                            _vpn_app_unstable_timestamps[device] = [
                                t for t in ts_b5 if now_b5 - t <= 60.0
                            ]
                            vpn_tun_count = len(_vpn_app_unstable_timestamps[device])
                            dlog.warning(
                                f"[Scenario B5][change_server] VPN app left foreground "
                                f"during tun0 wait (#{vpn_tun_count} in 60s)"
                            )
                            if vpn_tun_count >= 3:
                                if _vpn_reinstall_done or after_reinstall:
                                    _set_failure("vpn_app_unstable"); return False
                                return "reinstall_needed"
                            else:
                                open_vpn(device)
                                time.sleep(1.0)
                                continue

                    if not conn_req_handled:
                        try:
                            cur = _get_current_activity(device)
                            if "com.android.vpndialogs" in cur:
                                dlog.info("── [Scenario B3] Permission dialog — tapping OK/Allow")
                                if not _vpn_tap_ok_allow(device, dlog):
                                    dlog.warning("── [Scenario B3] permission dialog tap failed")
                                    _last_vpn_change_failure_reason[device] = "permission_failed"
                                conn_req_handled = True
                                time.sleep(1.0)
                                continue
                        except Exception:
                            pass

                    time.sleep(1.0)

                if confirmed:
                    dlog.info(
                        f"── [Scenario B3] tun0/protected confirmed — "
                        f"server changed ✓ (attempt {_attempt})"
                    )
                    go_home(device); return True

                dlog.warning(f"── [Scenario B3] attempt {_attempt}/3 — tun0 not confirmed after 30s")

            dlog.warning(f"── [Scenario B3] {cycle_label} cycle — all 3 attempts exhausted")
            _set_failure("no_tun0")
            # If not after_reinstall, caller (_run_attempts normal cycle) may still
            # attempt a reinstall cycle; do not add the VPN-only reset here.
            return False

        # ── Run the normal 3-attempt cycle ────────────────────────────────────
        # Cap bookkeeping: the inner loop performs up to 3 change-server
        # attempts, matching CAP_CHANGE_SERVER_ATTEMPTS.  Recording them on the
        # shared counter keeps the runtime path visible in _counters_snapshot()
        # and in every Issues entry written from here on.
        result = _run_attempts(after_reinstall=False)
        if result is True:
            return _succeed("normal_cycle")
        if result is False:
            # Normal cycle failed. Before giving up, if host internet is OK
            # and the emulator is still alive, try a VPN-only reset once as
            # a last-ditch emulator-only internet recovery.
            # Recursion guard: skip if already called from _force_reset_vpn_only.
            reason_now = _last_vpn_change_failure_reason.get(device, "")
            if reason_now == "no_tun0" and not _vpn_only_reset_active.get(device):
                dlog.warning("[VPN-RESET][change_server] emulator internet still down after normal VPN work")
                # Re-check the host before escalating: the outage may have
                # started mid-cycle, in which case pausing is correct and any
                # further recovery here would be wasted effort.
                if host_internet_ok():
                    _slog(dlog, device, "_vpn_change_server", "escalate",
                          "host internet OK — emulator-only VPN reset")
                    reset_ok = _force_reset_vpn_only(
                        device,
                        dlog,
                        reason="change_server no_tun0 after normal attempts"
                    )
                    if reset_ok:
                        _slog(dlog, device, "_vpn_change_server", "escalate",
                              "VPN-only reset succeeded")
                        return _succeed("force_reset_vpn_only")
                    # Still failed — fall through to return False
                else:
                    _slog(dlog, device, "_vpn_change_server", "escalate",
                          "host internet DOWN mid-cycle — pausing instead of escalating")
                    pause_sig = pause_controller_until_host_internet_back(
                        device, dlog, phase="vpn_change_server_escalate",
                        fn="_vpn_change_server"
                    )
                    if pause_sig == SIG_MANUAL_STOP:
                        return _set_failure("manual_stop")
                    # Host is back. Report failure so the caller restarts from a
                    # clean checkpoint rather than resuming mid-recovery.
                    return _set_failure("host_internet_recovered_restart")
            return False

        # result == "reinstall_needed"
        dlog.warning(
            "[Scenario B5][change_server] VPN app instability threshold reached "
            "— performing one VPN reinstall then retrying"
        )
        if _vpn_reinstall_done:
            return _set_failure("vpn_app_unstable")

        # Shared install/reinstall cap.  This is the same budget setup_device's
        # first install draws from, so the two paths cannot combine to exceed
        # CAP_VPN_INSTALL for one device in one run.
        if not vpn_install_allowed(device, dlog, reason="change_server_instability",
                                   phase="vpn_change_server",
                                   fn="_vpn_change_server"):
            return _set_failure("vpn_install_cap_exhausted")

        _vpn_reinstall_for_instability[device] = 1
        _vpn_reinstall_done                    = True
        _vpn_app_unstable_timestamps[device]   = []

        ok_uninstall = uninstall_proton(device)
        if not ok_uninstall:
            dlog.warning(
                "[Scenario B5][change_server] uninstall_proton() returned False "
                "— may already be gone, continuing"
            )
        ok_install = install_vpn(device)
        if not ok_install:
            dlog.error("[Scenario B5][change_server] install_vpn() failed after reinstall")
            return _set_failure("vpn_reinstall_failed")
        ok_open = open_vpn(device)
        if not ok_open:
            dlog.error("[Scenario B5][change_server] open_vpn() failed after reinstall")
            return _set_failure("vpn_reinstall_open_failed")

        dlog.info(
            "[Scenario B5][change_server] VPN reinstall + open successful ✓ "
            "— running fresh 3-attempt post-reinstall cycle"
        )

        # ── One fresh 3-attempt cycle after reinstall (no further reinstall) ──
        post_result = _run_attempts(after_reinstall=True)
        if post_result is True:
            return _succeed("post_reinstall_cycle")
        # post_result is False or "reinstall_needed" (treated as failure here)
        if post_result == "reinstall_needed":
            return _set_failure("vpn_app_unstable")
        return False

    finally:
        # ── Always restore TargetAppGuard when we leave the VPN app ────────────────
        # This runs on every exit path including exceptions.  Leaving the page
        # checks paused, or the guard thread stopped, would blind the runtime
        # to a genuinely broken device for the rest of the run.
        target_app_guard_resume_page_checks(device, dlog)
        if guard is not None and _saved_target_app_stage is not None:
            _target_app_guard_rearm(guard, _saved_target_app_stage)
            try:
                guard.set_target_app_opened()
            except Exception:
                pass
            _slog(dlog, device, "_vpn_change_server", "cleanup",
                  "TargetAppGuard re-armed", stage=_saved_target_app_stage,
                  elapsed=time.time() - _t_vcs_start)


# =============================================================================
# PHASE 2 of prepare_target_app:  setup_vpn()
# -----------------------------------------------------------------------------
# Stage 1 gets ProtonVPN open and standing on RoutingActivity.
# Stage 2 gets tun0 up, via Connect or via a setup-time Change Server.
#
# VpnGuard is active for the whole phase and is stopped in a finally block no
# matter how we leave.  The guard only DETECTS; every click below goes through
# _svpn_guarded_click(), which enforces the same five-step pattern every time:
#
#     find button -> checkpoint -> reconfirm page -> reconfirm button -> click
#                 -> wait for registration, checkpointing throughout
#
# Doing it in one helper rather than inline at each call site is what makes the
# "checkpoint before every action" rule actually hold.
# =============================================================================

CAP_VPN_KILL_REOPEN = 2     # force-stop + reopen ProtonVPN, per device per run
CAP_STAGE_CYCLES    = 3     # full stage1+stage2 retries inside one setup_vpn call

_VPN_CONNECT_REG_WINDOW = 5.0    # click counts as registered within this window
_VPN_CONNECT_FAIL_EARLY = 3.0    # nothing at all by here == attempt failed
_VPN_TUN0_WAIT          = 30.0   # after a registered Connect, wait this long for tun0


# ── low-level detection helpers (detect only — never click) ──────────────────

def _svpn_activity(device: str) -> str:
    return (_get_current_activity(device) or "").strip()


def _svpn_on_activity(device: str, *fragments: str) -> "str | None":
    """Return the first fragment present in the current activity, else None."""
    current = _svpn_activity(device)
    for frag in fragments:
        if frag in current:
            return frag
    return None


def _svpn_permission_dialog_visible(device: str) -> bool:
    """Android's own 'Connection request' VPN permission dialog."""
    current = _svpn_activity(device).lower()
    return "vpndialogs" in current or "novpnpermission" in current


# Connect-button search budgets.  The initial search was 8s, which on a slow or
# still-rendering ProtonVPN screen was not enough for either detector to answer —
# and a miss escalated all the way to reinstalling the app.
CONNECT_FIND_TIMEOUT_INITIAL   = 15.0
CONNECT_FIND_TIMEOUT_RECONFIRM = 9.0

# Fallback Connect coordinates, used ONLY when the VPN screen is confirmed to be
# the unprotected/disconnected one but no detector could read the label.
_CONNECT_FALLBACK_LANDSCAPE = (960, 828)
_CONNECT_FALLBACK_PORTRAIT  = (540, 1668)

_UNPROTECTED_MARKERS = ("you are unprotected", "unprotected")

# Strings unique to the ProtonVPN first-launch welcome/onboarding screen.
# Recognising it lets the fast path route straight to the onboarding handler
# instead of burning the 15s Connect race on a screen that has no Connect button.
_VPN_WELCOME_MARKERS = (
    "welcome to proton vpn",
    "certified no-logs vpn",
    "browse private",
    "continue as guest",
    "sign up",
    "get started",
)


def _svpn_screen_orientation(device: str, dlog) -> str:
    """
    Read the live screen size and report "landscape" or "portrait".

    Measured, never assumed — the fallback Connect coordinate is meaningless if
    the orientation guess is wrong.
    """
    try:
        d = check_display(device, dlog, return_details=True)
        w, h = d.get("width"), d.get("height")
        if w and h:
            return "landscape" if w >= h else "portrait"
    except Exception as exc:
        dlog.debug(f"[VPN-FIND] {device} | orientation probe failed: {exc!r}")
    return "landscape"


def _svpn_connect_fallback_coord(device: str, dlog) -> "tuple[int, int]":
    orient = _svpn_screen_orientation(device, dlog)
    coord = (_CONNECT_FALLBACK_LANDSCAPE if orient == "landscape"
             else _CONNECT_FALLBACK_PORTRAIT)
    dlog.info(f"[VPN-FIND] {device} | orientation={orient} fallback Connect={coord}")
    return coord


def _svpn_uia_texts(device: str, dlog) -> list:
    """Every text / content-desc string in the current UIAutomator dump."""
    out = []
    try:
        root = _vpn_uia_dump(device, dlog)
        if root is None:
            return out
        for node in root.iter("node"):
            for attr in ("text", "content-desc"):
                v = (node.attrib.get(attr, "") or "").strip()
                if v:
                    out.append(v)
    except Exception as exc:
        dlog.debug(f"[VPN-FIND] {device} | UIA text dump failed: {exc!r}")
    return out


def _svpn_unprotected_screen(device: str, dlog) -> bool:
    """
    True when this is unmistakably the disconnected ProtonVPN home screen:
    RoutingActivity in the foreground AND an "unprotected" string on it.

    This is the signal that lets a missing "Connect" label be treated as a
    detection miss rather than a broken app.
    """
    if "RoutingActivity" not in _svpn_activity(device):
        return False
    texts = [t.lower() for t in _svpn_uia_texts(device, dlog)]
    hit = any(any(m in t for m in _UNPROTECTED_MARKERS) for t in texts)
    if hit:
        dlog.info(f"[VPN-FIND] {device} | unprotected VPN screen confirmed "
                  f"(RoutingActivity + unprotected text)")
    return hit


def _svpn_connect_from_dump(device: str, dlog, root=None) -> tuple:
    """
    Mine ONE UIAutomator dump for a usable Connect coordinate.

    Deliberately more permissive than _find_vpn_button (exact text + clickable):
    ProtonVPN often renders the label on a non-clickable child inside a clickable
    row, or as "CONNECT" / "Connect now". Those were being seen in the debug dump
    and then thrown away, while the flow fell through to a 15-second miss.

    Returns (pos_or_None, texts, unprotected).
    """
    texts = []
    pos = None
    unprotected = False
    try:
        if root is None:
            # Only dumps when the caller has none. The fast path always supplies
            # one so this screen is never dumped twice.
            root = _vpn_uia_dump(device, dlog)
        if root is None:
            return (None, texts, False)

        import re as _re

        def _center(bounds):
            m = _re.findall(r"\d+", bounds or "")
            if len(m) == 4:
                return ((int(m[0]) + int(m[2])) // 2, (int(m[1]) + int(m[3])) // 2)
            return None

        exact_hit = None
        loose_hit = None
        for node in root.iter("node"):
            txt  = (node.attrib.get("text", "") or "").strip()
            desc = (node.attrib.get("content-desc", "") or "").strip()
            for v in (txt, desc):
                if v:
                    texts.append(v)
            blob = f"{txt} {desc}".strip().lower()
            if "unprotected" in blob:
                unprotected = True
            if not blob:
                continue
            c = _center(node.attrib.get("bounds", ""))
            if c is None:
                continue
            if blob == "connect":
                exact_hit = exact_hit or c
            elif "connect" in blob and "disconnect" not in blob and "reconnect" not in blob:
                loose_hit = loose_hit or c

        pos = exact_hit or loose_hit
        if pos:
            dlog.info(f"[VPN-FIND] {device} | Connect mined from UIA dump at {pos} "
                      f"({'exact' if exact_hit else 'substring'} match)")
    except Exception as exc:
        dlog.debug(f"[VPN-FIND] {device} | dump mining failed: {exc!r}")
    return (pos, texts, unprotected)


def _svpn_save_connect_debug(device: str, dlog, texts: list, ocr_note: str,
                             blocking: bool = False) -> None:
    """
    Persist a screenshot + UIAutomator XML for a Connect miss.

    Runs on a daemon thread by default. This used to execute inline inside the
    detection race, adding a second screenshot and a 15-second UIA dump to every
    miss — which is most of why a visible Connect button was not clicked for
    30-40 seconds. Diagnostics must never sit between "we cannot read the label"
    and "click the fallback coordinate".
    """
    def _work():
        try:
            folder = "unknown_pages"
            os.makedirs(folder, exist_ok=True)
            stamp = _dt.datetime.now().strftime("%Y%m%d-%H%M%S")
            base  = os.path.join(folder,
                                 f"{_sanitize_device_id(device)}_connect_{stamp}")
            try:
                img = get_screenshot(device)
                if img is not None:
                    img.save(base + ".png")
            except Exception:
                pass
            try:
                xml = _adb_shell(device, "uiautomator", "dump", "/dev/tty", timeout=6)
                with open(base + ".xml", "w", encoding="utf-8") as f:
                    f.write(xml or "")
            except Exception:
                pass
            dlog.error(
                f"[VPN-FIND] {device} | Connect NOT found — debug saved to {base}.*\n"
                f"[VPN-FIND] {device} | UIA text nodes ({len(texts)}): {texts}\n"
                f"[VPN-FIND] {device} | OCR: {ocr_note}"
            )
        except Exception as exc:
            dlog.debug(f"[VPN-FIND] {device} | debug artifact save failed: {exc!r}")

    if blocking:
        _work()
        return
    try:
        _threading.Thread(target=_work, daemon=True,
                          name=f"vpn_debug_{_sanitize_device_id(device)}").start()
    except Exception:
        pass


def _svpn_find_button_race(device: str, dlog, label: str,
                           timeout: float = CONNECT_FIND_TIMEOUT_INITIAL,
                           stage: str = "initial") -> "tuple[int, int] | None":
    """
    Locate a ProtonVPN button by racing UIAutomator against OCR.

    Both workers are pure detectors: they return coordinates and nothing else,
    and the main thread does the clicking.  UIAutomator is usually faster and
    more precise, but some ProtonVPN builds simply do not expose the Connect
    label as a text node — the dump shows only "You are unprotected",
    "India · <ip>", "Home", "Countries", "Profiles", "Settings".  That is exactly
    when the OCR paths matter.

    Three detectors, first answer wins:
      1. UIAutomator exact label
      2. EasyOCR full-screen
      3. Tesseract over the lower Connect-button band (cheap, different engine —
         catches cases where EasyOCR misreads the stylised button text)
    """
    found = {"pos": None, "src": None}
    lock  = _threading.Lock()
    done  = _threading.Event()
    notes = []

    def _record(pos, src):
        if pos is None:
            return
        with lock:
            if found["pos"] is None:
                found["pos"] = pos
                found["src"] = src
                done.set()

    def _worker_uia():
        try:
            _record(_find_vpn_button(device, label), "uiautomator")
        except Exception as exc:
            notes.append(f"uia_error={exc!r}")
            dlog.debug(f"[VPN-FIND] {device} | UIA worker failed: {exc!r}")

    def _worker_ocr():
        t0 = time.time()
        notes.append("easyocr_started")
        try:
            boxes = text_detect(device=device, engine="easyocr",
                                return_boxes=True, to_gray=True)
            if not boxes:
                notes.append("easyocr_no_boxes")
            else:
                notes.append(f"easyocr_boxes={len(boxes)}")
            _record(_match_vpn_label(label, boxes, dlog), "easyocr")
            notes.append(f"easyocr_done_{time.time()-t0:.1f}s")
        except Exception as exc:
            notes.append(f"easyocr_failed={exc!r}")
            dlog.debug(f"[VPN-FIND] {device} | EasyOCR worker failed: {exc!r}")

    def _worker_tess():
        # Lower band of a 1080p screen — where the free-server Connect button sits.
        t0 = time.time()
        notes.append("tesseract_started")
        try:
            boxes = text_detect(device=device, engine="tesseract",
                                return_boxes=True, to_gray=True)
            if not boxes:
                notes.append("tesseract_no_boxes")
            else:
                notes.append(f"tesseract_boxes={len(boxes)}")
            _record(_match_vpn_label(label, boxes, dlog), "tesseract")
            notes.append(f"tesseract_done_{time.time()-t0:.1f}s")
        except Exception as exc:
            notes.append(f"tesseract_failed={exc!r}")
            dlog.debug(f"[VPN-FIND] {device} | Tesseract worker failed: {exc!r}")

    threads = [
        _threading.Thread(target=_worker_uia,  daemon=True, name=f"vpnfind_uia_{device}"),
        _threading.Thread(target=_worker_ocr,  daemon=True, name=f"vpnfind_ocr_{device}"),
        _threading.Thread(target=_worker_tess, daemon=True, name=f"vpnfind_tess_{device}"),
    ]
    t0 = time.time()
    for t in threads:
        t.start()
    done.wait(timeout=timeout)
    elapsed = time.time() - t0

    with lock:
        pos, src = found["pos"], found["src"]

    dlog.info(
        f"[VPN-FIND] {device} | stage={stage} label={label!r} timeout={timeout:.0f}s "
        f"{'FOUND at ' + str(pos) + ' via ' + str(src) if pos else 'NOT FOUND'} "
        f"in {elapsed:.1f}s | ocr: {', '.join(notes) or 'n/a'}"
    )
    # Deliberately NO debug artifact save here. It used to run inline on every
    # miss, costing another screenshot + UIA dump before the fallback could be
    # clicked. The caller saves diagnostics later, off the critical path, and
    # only once the fallback has also failed.
    return pos


# ── guarded wait + guarded click ─────────────────────────────────────────────

def _svpn_wait_activity(device: str, dlog, guard: "VpnGuard", *fragments: str,
                        timeout: float = 30.0, phase: str = "") -> tuple:
    """
    Wait for any of `fragments` to appear in the foreground activity, running a
    VpnGuard checkpoint on every 1s iteration.

    Returns ("found", fragment) | ("timeout", last_activity) | (SIG_*, "").
    """
    t0 = time.time()
    while time.time() - t0 < timeout:
        chk = vpn_guard_checkpoint(device, dlog, guard, phase=phase)
        if chk != "ok":
            return (chk, "")

        hit = _svpn_on_activity(device, *fragments)
        if hit:
            _slog(dlog, device, "setup_vpn", phase, "activity reached",
                  page=hit, elapsed=time.time() - t0)
            return ("found", hit)
        time.sleep(1.0)

    last = _svpn_activity(device)
    _slog(dlog, device, "setup_vpn", phase, "activity wait TIMEOUT",
          expected="|".join(fragments), page=last, elapsed=time.time() - t0)
    return ("timeout", last)


# How stale an initial coordinate may be before it is no longer trusted as a
# tap target. Derived from the reconfirm budget rather than picked: the only
# thing that elapsed between finding the coordinate and deciding to use it is
# the reconfirm search itself, plus a little slack for the safety re-checks.
CONNECT_INITIAL_COORD_MAX_AGE = CONNECT_FIND_TIMEOUT_RECONFIRM + 3.0


# ── V2 diagnostic: capture an unclassifiable ProtonVPN Connect screen ────────
# 23 of 57 classifications on the 4 Aug run returned state="unknown" with
# unprotected=False, all on the new 95xx/98xx instances. Their UIA tree contains
# neither the "unprotected" text nor readable Connect bounds, so the fast path
# never engages and every one falls into the 15s race.
#
# This writes ONE artifact set per device per run so the two populations can be
# compared. It is a pure diagnostic: it re-serialises the tree the classifier
# ALREADY dumped, never dumps again, never takes a screenshot, never touches the
# screenshot lock, never runs OCR, and never changes what the classifier decides.
_vpn_unknown_captured: dict = {}          # device -> True, once per run


def _vpn_capture_unknown_ui(device: str, dlog, root, ui: dict,
                            activity: str = "") -> str:
    """
    Save the UIA tree + classifier verdict for an unknown Connect screen.

    `root` must be the tree the caller already has. Returns the XML path, or ""
    when nothing was written. Never raises.
    """
    try:
        if _vpn_unknown_captured.get(device):
            return ""
        if root is None:
            dlog.debug(f"[VPN-UNKNOWN] {device} | no cached UIA tree — nothing to save")
            return ""
        _vpn_unknown_captured[device] = True

        folder = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                              "unknown_pages")
        os.makedirs(folder, exist_ok=True)
        stamp = _dt.datetime.now().strftime("%Y%m%d_%H%M%S")
        base  = os.path.join(folder,
                             f"{_sanitize_device_id(device)}_vpn_unknown_{stamp}")

        # 1. the tree exactly as the classifier saw it
        xml_path = f"{base}.xml"
        with open(xml_path, "w", encoding="utf-8") as f:
            f.write(_ET.tostring(root, encoding="unicode"))

        # 2. every node, flattened — this is what a comparison actually reads
        nodes = []
        try:
            for el in root.iter():
                a = el.attrib
                if not any(a.get(k) for k in ("text", "content-desc", "resource-id")):
                    continue
                nodes.append({
                    "text":         a.get("text", ""),
                    "content-desc": a.get("content-desc", ""),
                    "resource-id":  a.get("resource-id", ""),
                    "class":        a.get("class", ""),
                    "clickable":    a.get("clickable", ""),
                    "enabled":      a.get("enabled", ""),
                    "selected":     a.get("selected", ""),
                    "bounds":       a.get("bounds", ""),
                })
        except Exception:
            pass

        meta = {
            "device":               device,
            "timestamp":            _dt.datetime.now().isoformat(timespec="seconds"),
            "activity":             activity,
            "classifier_state":     ui.get("state", "unknown"),
            "protected":            ui.get("protected"),
            "unprotected":          ui.get("unprotected"),
            "connecting_or_changing": ui.get("state") == "connecting_or_changing",
            "change_available":     ui.get("change_available"),
            "onboarding":           ui.get("onboarding"),
            "connect_bounds":       ui.get("connect_bounds"),
            "connect_bounds_loose": ui.get("connect_bounds_loose"),
            "connect_source":       ui.get("connect_source"),
            "change_server_bounds": ui.get("change_server_bounds"),
            "timer_text":           ui.get("timer_text"),
            "classifier_texts":     ui.get("texts", [])[:200],
            "node_count":           len(nodes),
            "nodes":                nodes,
        }
        # Optional extras ONLY from data already in hand — no extra device calls.
        try:
            b = root.attrib.get("bounds") or root.find(".//node").attrib.get("bounds")
            if b:
                meta["root_bounds"] = b
        except Exception:
            pass

        json_path = f"{base}.json"
        with open(json_path, "w", encoding="utf-8") as f:
            json.dump(meta, f, indent=2, ensure_ascii=False)

        # 3. the passive cached frame, if the workflow happens to have one.
        #    Never captures: get_screenshot holds the per-device lock.
        png_path = ""
        try:
            img = get_cached_screenshot(device)
            if img is not None:
                png_path = f"{base}.png"
                img.save(png_path)
        except Exception:
            png_path = ""

        dlog.warning(f"[VPN-UNKNOWN] {device} | unclassifiable Connect screen saved "
                     f"({len(nodes)} node(s)) -> {xml_path}"
                     + (f" + cached PNG" if png_path else " (no cached frame)"))
        return xml_path
    except Exception as exc:
        try:
            dlog.debug(f"[VPN-UNKNOWN] {device} | capture failed: {exc!r}")
        except Exception:
            pass
        return ""


def _svpn_guarded_click(device: str, dlog, guard: "VpnGuard", *,
                        phase: str, label: str, expect_activity: str,
                        find_fn, registered_fn,
                        max_attempts: int = 3,
                        reg_timeout: float = 3.0,
                        counter_store: "dict | None" = None,
                        use_initial_on_reconfirm_miss: bool = False) -> str:
    """
    The one and only click pattern used in setup_vpn.

    For each attempt:
        1. locate the button (detection only)
        2. VpnGuard checkpoint
        3. reconfirm we are still on the expected page
        4. reconfirm the button is still where we found it
        5. click once
        6. poll for click registration, checkpointing every second

    Returns "registered" | "not_found" | "exhausted" | SIG_*.

    `counter_store`, when given, is a per-device attempt counter so the cap
    survives across re-entries into this phase (used for Connect and Change
    Server, which must not reset their budget on every retry loop).

    `use_initial_on_reconfirm_miss` — OPT-IN, default False, currently enabled
    only for the Connect slow path.

        The 4 Aug run showed the reconfirm search missing a button that was
        demonstrably still there: on localhost:9585 the identical coordinate
        (443, 651) was found on four separate attempts, yet 13 of 32 successful
        initial finds were discarded because the shorter reconfirm search failed.
        Worse, step 4 then returned "registered" for a tap that was never sent,
        so the caller spent ~35s waiting for a tun0 that could not appear.

        With this enabled a reconfirm miss no longer claims success. Every
        safety check is re-run (the reconfirm may have burned 9s), and the
        stored initial coordinate is tapped only when the screen genuinely has
        not moved. Left False everywhere else: "Continue as guest", "Not now",
        "Change server" and the onboarding buttons keep the original behaviour.
    """
    for attempt in range(1, max_attempts + 1):
        # PEEK only — do not consume an attempt yet.
        #
        # The counter used to be incremented here, before the button was even
        # located, so a pure detection miss burned budget and the first real
        # fallback click reported attempt 2/4. An attempt now means "a tap was
        # actually sent"; the increment moved down to step 5.
        if counter_store is not None:
            used = _ctr_get(counter_store, device)
            if used >= max_attempts:
                _slog(dlog, device, "setup_vpn", phase,
                      f"{label}: attempt cap reached",
                      attempt=f"{used}/{max_attempts}")
                return "exhausted"
            shown = f"{used + 1}/{max_attempts}"
        else:
            shown = f"{attempt}/{max_attempts}"

        chk = vpn_guard_checkpoint(device, dlog, guard, phase=phase)
        if chk != "ok":
            return chk

        # 1. find (initial, generous budget)
        t_find = time.time()
        pos    = find_fn(stage="initial")
        _slog(dlog, device, "setup_vpn", phase, f"{label}: initial search finished",
              elapsed=time.time() - t_find, found=pos is not None)
        if pos is None:
            _slog(dlog, device, "setup_vpn", phase, f"{label}: button NOT found",
                  attempt=shown, elapsed=time.time() - t_find,
                  page=_svpn_activity(device))
            return "not_found"
        cx, cy = pos
        # Remembered so a reconfirm miss has something trustworthy to fall back
        # on. monotonic, because this is an age measurement.
        initial_x, initial_y = cx, cy
        initial_found_at = time.monotonic()

        # 2. checkpoint immediately before acting (this also runs the pause gate,
        #    so we never tap into a paused device)
        chk = vpn_guard_checkpoint(device, dlog, guard, phase=phase)
        if chk != "ok":
            return chk

        # 3. reconfirm page — one activity read, not two
        cur_activity = _svpn_activity(device)
        if expect_activity and expect_activity not in cur_activity:
            if not use_initial_on_reconfirm_miss:
                _slog(dlog, device, "setup_vpn", phase,
                      f"{label}: page changed before click — treating as registered",
                      attempt=shown, expected=expect_activity, page=cur_activity)
                return "registered"

            # Connect only. A page change is NOT registration evidence: no tap
            # has been sent, so reporting "registered" sent setup_vpn into a
            # ~35s tun0 wait for an action that never happened. Only a real
            # signal counts.
            try:
                _already = bool(registered_fn())
            except Exception:
                _already = False
            try:
                _tun0 = bool(vpn_activity(device))
            except Exception:
                _tun0 = False
            if _already or _tun0:
                _slog(dlog, device, "setup_vpn", phase,
                      f"{label}: page changed before click — genuinely registered",
                      attempt=shown, expected=expect_activity, page=cur_activity,
                      tun0=str(_tun0).lower(), action="no_tap_registered")
                return "registered"
            _slog(dlog, device, "setup_vpn", phase,
                  f"{label}: page changed before click with no registration",
                  attempt=shown, expected=expect_activity, page=cur_activity,
                  tun0="false", action="no_tap_page_changed_unregistered")
            return "not_found"

        # 4. reconfirm button (shorter budget than the initial search — the
        #    button was just located, so this only guards against it vanishing)
        _t_recon = time.time()
        pos2 = find_fn(stage="reconfirm")
        _slog(dlog, device, "setup_vpn", phase, f"{label}: reconfirm search finished",
              elapsed=time.time() - _t_recon, found=pos2 is not None)
        if pos2 is None:
            if not use_initial_on_reconfirm_miss:
                # Unchanged behaviour for every non-Connect button.
                _slog(dlog, device, "setup_vpn", phase,
                      f"{label}: button vanished during reconfirm — re-evaluating",
                      attempt=shown)
                return "registered"

            # ── Connect only: a reconfirm miss is not proof of anything ──────
            # The reconfirm search may have taken the full budget, so nothing
            # learned before it can be trusted now. Re-check everything from
            # scratch before deciding.
            coord_age = time.monotonic() - initial_found_at

            # C. guard / pause first — they outrank any click decision.
            chk = vpn_guard_checkpoint(device, dlog, guard, phase=phase)
            if chk != "ok":
                _slog(dlog, device, "setup_vpn", phase,
                      f"{label} reconfirm missed — guard signal during re-check",
                      initial_coord=f"({initial_x},{initial_y})",
                      initial_coord_age=round(coord_age, 1),
                      action="no_tap", signal=chk)
                return chk
            if _pause_requested():
                gate = wait_while_paused(device, dlog, phase=phase,
                                         fn="_svpn_guarded_click", context="setup")
                if gate == SIG_MANUAL_STOP:
                    return SIG_MANUAL_STOP
                _slog(dlog, device, "setup_vpn", phase,
                      f"{label} reconfirm missed — paused during re-check",
                      action="no_tap", signal=SIG_RESTART_BEFORE_TARGET_APP)
                return SIG_RESTART_BEFORE_TARGET_APP

            cur_activity = _svpn_activity(device)
            try:
                tun0_up = bool(vpn_activity(device))
            except Exception:
                tun0_up = False
            try:
                already = bool(registered_fn())
            except Exception:
                already = False

            # A. it already happened — the click either landed earlier or the
            #    app connected on its own. Tapping now would be a second click.
            if already or tun0_up:
                _slog(dlog, device, "setup_vpn", phase,
                      f"{label} reconfirm missed — already registered",
                      initial_coord=f"({initial_x},{initial_y})",
                      initial_coord_age=round(coord_age, 1),
                      activity=cur_activity, tun0=str(tun0_up).lower(),
                      action="no_tap_already_registered")
                return "registered"

            # B. the screen moved. The stored coordinate belongs to a page that
            #    is no longer showing, so tapping it could hit anything — and
            #    with registered_fn and tun0 both already false above, there is
            #    no evidence a click ever landed. "not_found" is the honest
            #    answer; "registered" would buy another pointless tun0 wait.
            if expect_activity and expect_activity not in cur_activity:
                _slog(dlog, device, "setup_vpn", phase,
                      f"{label} reconfirm missed — page changed during re-check",
                      initial_coord=f"({initial_x},{initial_y})",
                      initial_coord_age=round(coord_age, 1),
                      activity=cur_activity, expected=expect_activity,
                      tun0=str(tun0_up).lower(),
                      action="no_tap_page_changed_unregistered")
                return "not_found"

            # Too old to trust. Report honestly rather than claim a click.
            if coord_age > CONNECT_INITIAL_COORD_MAX_AGE:
                _slog(dlog, device, "setup_vpn", phase,
                      f"{label} reconfirm missed — initial coordinate too old",
                      initial_coord=f"({initial_x},{initial_y})",
                      initial_coord_age=round(coord_age, 1),
                      max_age=CONNECT_INITIAL_COORD_MAX_AGE,
                      activity=cur_activity, tun0=str(tun0_up).lower(),
                      action="no_tap_stale_coordinate")
                return "not_found"

            # D. still on the expected page, tunnel still down, coordinate
            #    fresh: the button did not go anywhere, the reconfirm search
            #    simply missed it. Use what the initial search found.
            _slog(dlog, device, "setup_vpn", phase,
                  f"{label} reconfirm missed",
                  initial_coord=f"({initial_x},{initial_y})",
                  initial_coord_age=round(coord_age, 1),
                  activity=cur_activity, tun0=str(tun0_up).lower(),
                  action="using_initial_coordinate")
            cx, cy = initial_x, initial_y
            click_source = "initial_after_reconfirm_miss"
        else:
            cx, cy = pos2
            click_source = "reconfirm"

        # 5. click — final pause check in the last moment before the tap
        if _pause_requested():
            gate = wait_while_paused(device, dlog, phase=phase,
                                     fn="_svpn_guarded_click", context="setup")
            if gate == SIG_MANUAL_STOP:
                return SIG_MANUAL_STOP
            _slog(dlog, device, "setup_vpn", phase,
                  f"{label}: paused just before the tap — restarting setup",
                  signal=SIG_RESTART_BEFORE_TARGET_APP)
            return SIG_RESTART_BEFORE_TARGET_APP

        # Consume the attempt HERE — a tap is about to be sent for real.
        if counter_store is not None:
            used  = _ctr_inc(counter_store, device, dlog, f"{label}_attempts")
            shown = f"{used}/{max_attempts}"

        _slog(dlog, device, "setup_vpn", phase, f"{label}: clicking",
              button=label, coord=f"({cx},{cy})", attempt=shown,
              source=click_source, page=_svpn_activity(device))
        try:
            tap_on_device(cx, cy, device, dlog=dlog)
        except Exception as exc:
            dlog.warning(f"[SETUP] {device} | tap raised: {exc!r}")

        # 6. wait for registration, checkpointing throughout
        t_click = time.time()
        while time.time() - t_click < reg_timeout:
            chk = vpn_guard_checkpoint(device, dlog, guard, phase=phase)
            if chk != "ok":
                return chk
            if registered_fn():
                _slog(dlog, device, "setup_vpn", phase, f"{label}: click REGISTERED",
                      attempt=shown, elapsed=time.time() - t_click,
                      page=_svpn_activity(device))
                record_event(device, "click", fn="_svpn_guarded_click", phase=phase,
                             button=label, coord=f"({cx},{cy})", attempt=shown,
                             source=click_source,
                             page=expect_activity, registered=True,
                             result="registered",
                             elapsed_since_click=round(time.time() - t_click, 2))
                return "registered"
            time.sleep(0.5)

        _slog(dlog, device, "setup_vpn", phase, f"{label}: click NOT registered",
              attempt=shown, elapsed=time.time() - t_click,
              page=_svpn_activity(device))
        record_event(device, "click", fn="_svpn_guarded_click", phase=phase,
                     button=label, coord=f"({cx},{cy})", attempt=shown,
                     source=click_source,
                     page=expect_activity, registered=False,
                     result="not_registered",
                     elapsed_since_click=round(time.time() - t_click, 2))

    return "exhausted"


# ── Stage 1 sub-flows ────────────────────────────────────────────────────────

def _svpn_handle_add_account(device: str, dlog, guard: "VpnGuard") -> str:
    """
    AddAccountActivity -> click "Continue as guest".

    Registration means the page moved on at all: away from AddAccount, or
    straight to UpgradeOnboarding or Routing.
    """
    phase = "stage1_add_account"
    _slog(dlog, device, "setup_vpn", phase, "AddAccountActivity — need Continue as guest")

    def _find(stage: str = "initial"):
        return _svpn_find_button_race(device, dlog, "Continue as guest",
                                      timeout=10.0, stage=stage)

    def _registered():
        cur = _svpn_activity(device)
        return ("AddAccountActivity" not in cur
                or "UpgradeOnboardingDialogActivity" in cur
                or "RoutingActivity" in cur)

    result = _svpn_guarded_click(
        device, dlog, guard, phase=phase, label="Continue as guest",
        expect_activity="AddAccountActivity",
        find_fn=_find, registered_fn=_registered,
        max_attempts=3, reg_timeout=3.0,
    )
    if result in _ALL_SIGNALS:
        return result
    if result in ("not_found", "exhausted"):
        _slog(dlog, device, "setup_vpn", phase,
              "Continue as guest failed", result=result)
        append_issue(device, "vpn_guest_click_failed", f"result={result}",
                     fn="setup_vpn", phase=phase)
        return _vpn_escalate(device, dlog, guard, phase=phase,
                             reason="continue_as_guest_failed")

    # Registered — give the app up to 5s to land on Upgrade or Routing.
    outcome, hit = _svpn_wait_activity(
        device, dlog, guard,
        "RoutingActivity", "UpgradeOnboardingDialogActivity",
        timeout=5.0, phase=phase,
    )
    if outcome in _ALL_SIGNALS:
        return outcome
    if outcome == "found" and hit == "RoutingActivity":
        return SIG_SUCCESS
    if outcome == "found" and hit == "UpgradeOnboardingDialogActivity":
        return _svpn_handle_upgrade_onboarding(device, dlog, guard)

    _slog(dlog, device, "setup_vpn", phase,
          "no known page 5s after guest click", page=_svpn_activity(device))
    return _vpn_escalate(device, dlog, guard, phase=phase,
                         reason="no_page_after_guest_click")


def _svpn_handle_upgrade_onboarding(device: str, dlog, guard: "VpnGuard") -> str:
    """
    UpgradeOnboardingDialogActivity -> click "Not now".

    We only ever search for "Not now" here; clicking anything else on this
    dialog starts a paid upgrade flow.  If it cannot be found or clicked, a
    single Back press usually dismisses the dialog straight to Routing.
    """
    phase = "stage1_upgrade_dialog"
    _slog(dlog, device, "setup_vpn", phase, "UpgradeOnboarding dialog — need Not now")

    def _find(stage: str = "initial"):
        return _svpn_find_button_race(device, dlog, "Not now",
                                      timeout=10.0, stage=stage)

    def _registered():
        cur = _svpn_activity(device)
        return ("UpgradeOnboardingDialogActivity" not in cur
                or "RoutingActivity" in cur)

    result = _svpn_guarded_click(
        device, dlog, guard, phase=phase, label="Not now",
        expect_activity="UpgradeOnboardingDialogActivity",
        find_fn=_find, registered_fn=_registered,
        max_attempts=3, reg_timeout=3.0,
    )
    if result in _ALL_SIGNALS:
        return result

    if result == "registered":
        outcome, hit = _svpn_wait_activity(device, dlog, guard, "RoutingActivity",
                                           timeout=5.0, phase=phase)
        if outcome in _ALL_SIGNALS:
            return outcome
        if outcome == "found":
            return SIG_SUCCESS

    # Not found, or clicked but still stuck: one Back press, then confirm Routing.
    _slog(dlog, device, "setup_vpn", phase,
          "falling back to a single Back press", result=result)
    chk = vpn_guard_checkpoint(device, dlog, guard, phase=phase)
    if chk != "ok":
        return chk
    try:
        press_back(device)
    except Exception as exc:
        dlog.warning(f"[SETUP] {device} | press_back raised: {exc!r}")

    outcome, hit = _svpn_wait_activity(device, dlog, guard, "RoutingActivity",
                                       timeout=3.0, phase=phase)
    if outcome in _ALL_SIGNALS:
        return outcome
    if outcome == "found":
        _slog(dlog, device, "setup_vpn", phase, "Routing reached after Back")
        return SIG_SUCCESS

    append_issue(device, "vpn_upgrade_dialog_stuck",
                 f"Not now failed ({result}) and Back did not reach Routing",
                 fn="setup_vpn", phase=phase)
    return _vpn_escalate(device, dlog, guard, phase=phase,
                         reason="upgrade_dialog_stuck")


def _setup_vpn_stage1_routing(device: str, dlog, guard: "VpnGuard") -> str:
    """
    Stage 1: open ProtonVPN and confirm RoutingActivity.

    Stage 2 is never entered without that confirmation — clicking Connect
    coordinates on the wrong page was a recurring source of silent failures.
    """
    phase = "stage1_routing"
    guard.set_stage(1)

    # A brand-new ProtonVPN session: per-session attempt budgets start over.
    _ctr_reset_session(device)

    # ── Open the app (up to 3 launch attempts) ────────────────────────────
    opened = False
    for attempt in range(1, 4):
        chk = vpn_guard_checkpoint(device, dlog, guard, phase=phase)
        if chk != "ok":
            return chk
        t_open = time.time()
        try:
            opened = bool(open_vpn(device))
        except Exception as exc:
            dlog.error(f"[SETUP] {device} | open_vpn raised: {exc!r}")
            opened = False
        _slog(dlog, device, "setup_vpn", phase, "open_vpn attempt",
              attempt=f"{attempt}/3", result="ok" if opened else "failed",
              elapsed=time.time() - t_open)
        if opened:
            break
        random_delay(1.5, 2.5)

    if not opened:
        append_issue(device, "vpn_open_failed", "open_vpn failed 3 times",
                     fn="setup_vpn", phase=phase)
        return _vpn_escalate(device, dlog, guard, phase=phase, reason="open_vpn_failed")

    # From here the VPN app is up, so page-level checks become meaningful.
    guard.set_vpn_opened()
    guard.set_stage(2)

    outcome, hit = _svpn_wait_activity(
        device, dlog, guard,
        "RoutingActivity", "AddAccountActivity", "UpgradeOnboardingDialogActivity",
        timeout=30.0, phase=phase,
    )
    if outcome in _ALL_SIGNALS:
        return outcome
    if outcome == "timeout":
        append_issue(device, "vpn_no_activity_30s",
                     f"last activity={hit!r}", fn="setup_vpn", phase=phase)
        return _vpn_escalate(device, dlog, guard, phase=phase,
                             reason="no_vpn_activity_30s")

    if hit == "RoutingActivity":
        _slog(dlog, device, "setup_vpn", phase, "RoutingActivity confirmed",
              signal=SIG_SUCCESS)
        return SIG_SUCCESS

    if hit == "AddAccountActivity":
        sig = _svpn_handle_add_account(device, dlog, guard)
    else:
        sig = _svpn_handle_upgrade_onboarding(device, dlog, guard)

    if sig != SIG_SUCCESS:
        return sig

    # Final confirmation — stage 2 requires Routing, no exceptions.
    outcome, hit = _svpn_wait_activity(device, dlog, guard, "RoutingActivity",
                                       timeout=5.0, phase=phase)
    if outcome in _ALL_SIGNALS:
        return outcome
    if outcome == "found":
        _slog(dlog, device, "setup_vpn", phase,
              "RoutingActivity confirmed after onboarding", signal=SIG_SUCCESS)
        return SIG_SUCCESS

    append_issue(device, "vpn_routing_not_confirmed",
                 f"onboarding done but activity={hit!r}", fn="setup_vpn", phase=phase)
    return _vpn_escalate(device, dlog, guard, phase=phase,
                         reason="routing_not_confirmed")


# ── Stage 2: connect ─────────────────────────────────────────────────────────

def _svpn_handle_permission_dialog(device: str, dlog, guard: "VpnGuard",
                                   phase: str) -> bool:
    """
    Accept Android's VPN permission dialog.  Up to 3 taps — the dialog
    occasionally swallows the first one while it is still animating in.
    """
    for attempt in range(1, 4):
        if not _svpn_permission_dialog_visible(device):
            return True
        chk = vpn_guard_checkpoint(device, dlog, guard, phase=phase)
        if chk != "ok":
            return False
        _slog(dlog, device, "setup_vpn", phase,
              "VPN permission dialog — tapping OK/Allow", attempt=f"{attempt}/3")
        try:
            _vpn_tap_ok_allow(device, dlog)
        except Exception as exc:
            dlog.warning(f"[SETUP] {device} | _vpn_tap_ok_allow raised: {exc!r}")
        time.sleep(1.5)
    still = _svpn_permission_dialog_visible(device)
    _slog(dlog, device, "setup_vpn", phase, "permission dialog handling finished",
          dismissed=not still)
    return not still


def _setup_vpn_stage2_connect(device: str, dlog, guard: "VpnGuard") -> str:
    """
    Stage 2: get tun0 up.

    tun0 is checked FIRST.  If the tunnel is already established there is
    nothing to click, and we deliberately do not call go_home() — leaving the
    VPN app in the foreground is harmless and go_home() used to race the next
    phase's app launch.
    """
    phase = "stage2_connect"
    guard.set_stage(3)

    # ── Already connected? ────────────────────────────────────────────────
    try:
        if vpn_activity(device):
            _slog(dlog, device, "setup_vpn", phase,
                  "tun0 already UP — stage 2 complete (no go_home)",
                  signal=SIG_SUCCESS)
            return SIG_SUCCESS
    except Exception as exc:
        dlog.warning(f"[SETUP] {device} | vpn_activity raised: {exc!r}")

    def _find_connect(stage: str = "initial"):
        budget = (CONNECT_FIND_TIMEOUT_INITIAL if stage == "initial"
                  else CONNECT_FIND_TIMEOUT_RECONFIRM)
        return _svpn_find_button_race(device, dlog, "Connect",
                                      timeout=budget, stage=stage)

    def _connect_click_now(cx: int, cy: int, source: str) -> str:
        """
        Send one real Connect tap and judge registration.

        Shared by the fast path and the fallback path so both consume exactly one
        attempt, log the same way, and keep the same safety checks.

        Returns "registered" | "not_registered" | SIG_*.
        """
        chk = vpn_guard_checkpoint(device, dlog, guard, phase=phase)
        if chk != "ok":
            return chk
        if _pause_requested():
            gate = wait_while_paused(device, dlog, phase=phase,
                                     fn="_setup_vpn_stage2_connect", context="setup")
            if gate == SIG_MANUAL_STOP:
                return SIG_MANUAL_STOP
            return SIG_RESTART_BEFORE_TARGET_APP

        # Safety checks preserved: right page, tunnel genuinely down.
        if "RoutingActivity" not in _svpn_activity(device):
            return SIG_RESTART_SETUP_VPN
        try:
            if vpn_activity(device):
                return "registered"      # tunnel came up on its own
        except Exception:
            pass

        used = _ctr_inc(_connect_attempts, device, dlog, "connect_attempts")
        _slog(dlog, device, "setup_vpn", phase, "clicking Connect",
              button=f"Connect({source})", coord=f"({cx},{cy})",
              attempt=f"{used}/{CAP_CONNECT_ATTEMPTS}")
        try:
            tap_on_device(cx, cy, device, dlog=dlog)
        except Exception as exc:
            dlog.warning(f"[SETUP] {device} | Connect tap raised: {exc!r}")

        t_click = time.time()
        while time.time() - t_click < _VPN_CONNECT_REG_WINDOW:
            chk = vpn_guard_checkpoint(device, dlog, guard, phase=phase)
            if chk != "ok":
                return chk
            if _connect_registered():
                _slog(dlog, device, "setup_vpn", phase, "Connect click REGISTERED",
                      button=f"Connect({source})", coord=f"({cx},{cy})",
                      attempt=f"{used}/{CAP_CONNECT_ATTEMPTS}",
                      elapsed=time.time() - t_click)
                record_event(device, "click", fn="_setup_vpn_stage2_connect",
                             phase=phase, button="Connect", coord=f"({cx},{cy})",
                             attempt=f"{used}/{CAP_CONNECT_ATTEMPTS}",
                             source=source, registered=True, result="registered")
                return "registered"
            time.sleep(0.5)

        _slog(dlog, device, "setup_vpn", phase, "Connect click did NOT register",
              button=f"Connect({source})", coord=f"({cx},{cy})",
              attempt=f"{used}/{CAP_CONNECT_ATTEMPTS}", elapsed=time.time() - t_click)
        record_event(device, "click", fn="_setup_vpn_stage2_connect", phase=phase,
                     button="Connect", coord=f"({cx},{cy})",
                     attempt=f"{used}/{CAP_CONNECT_ATTEMPTS}", source=source,
                     registered=False, result="not_registered")
        return "not_registered"

    def _connect_registered():
        try:
            if vpn_activity(device):
                return True
        except Exception:
            pass
        if _svpn_permission_dialog_visible(device):
            return True
        try:
            ui = _classify_protonvpn_ui(device, dlog)
            state = ui.get("state", "unknown")
            if state in ("connecting_or_changing", "protected_change_available",
                         "protected_change_timer_unavailable"):
                return True
            if ui.get("protected"):
                return True
            if state in VPN_CONNECT_SCREEN_STATES and ui.get("connect_bounds") is None:
                # Connect no longer readable after the click. For
                # disconnected_connect that means the button went away (i.e. the
                # click landed); for the fallback state it was never readable, so
                # this is not evidence either way and must not count.
                return state == "disconnected_connect"
        except Exception:
            pass
        return False

    while True:
        if _stop_requested():
            return SIG_MANUAL_STOP

        used = _ctr_get(_connect_attempts, device)
        if used >= CAP_CONNECT_ATTEMPTS:
            _slog(dlog, device, "setup_vpn", phase,
                  "Connect attempt cap reached for this ProtonVPN session",
                  attempt=f"{used}/{CAP_CONNECT_ATTEMPTS}")
            append_issue(device, "vpn_connect_failed",
                         f"{used} Connect attempts in one session",
                         fn="setup_vpn", phase=phase)
            return _vpn_escalate(device, dlog, guard, phase=phase,
                                 reason="connect_attempts_exhausted")

        # Preconditions for a Connect click: right page, tunnel actually down.
        chk = vpn_guard_checkpoint(device, dlog, guard, phase=phase)
        if chk != "ok":
            return chk
        if "RoutingActivity" not in _svpn_activity(device):
            _slog(dlog, device, "setup_vpn", phase,
                  "not on RoutingActivity — returning to stage 1",
                  page=_svpn_activity(device), signal=SIG_RESTART_SETUP_VPN)
            return SIG_RESTART_SETUP_VPN

        # ── FAST PATH — exactly ONE UIAutomator dump ─────────────────────
        # uiautomator dump costs 4-7s on these instances. The previous flow paid
        # it twice on the same unchanged screen: once in _classify_protonvpn_ui()
        # and again in _svpn_connect_from_dump(). That duplication was the whole
        # of the remaining 11s between RoutingActivity and the tap.
        #
        # Now: dump once, hand the SAME parsed tree to both readers.
        _t_dump = time.time()
        _slog(dlog, device, "setup_vpn", phase, "UIA dump start (single dump)")
        try:
            fast_root = _vpn_uia_dump(device, dlog)
        except Exception as exc:
            dlog.debug(f"[SETUP] {device} | UIA dump raised: {exc!r}")
            fast_root = None
        _dump_ms = time.time() - _t_dump
        _slog(dlog, device, "setup_vpn", phase, "UIA dump end",
              elapsed=_dump_ms, result="ok" if fast_root is not None else "failed")

        try:
            fast_ui = _classify_protonvpn_ui(device, dlog, root=fast_root)
        except Exception as exc:
            dlog.debug(f"[SETUP] {device} | fast classify raised: {exc!r}")
            fast_ui = {}
        fast_state = fast_ui.get("state", "unknown")
        _slog(dlog, device, "setup_vpn", phase, "classifier result",
              state=fast_state,
              connect_exact=fast_ui.get("connect_bounds"),
              connect_loose=fast_ui.get("connect_bounds_loose"),
              source=fast_ui.get("connect_source"),
              unprotected=fast_ui.get("unprotected"),
              onboarding=fast_ui.get("onboarding"),
              elapsed_since_dump=time.time() - _t_dump)

        # ── D4/D8: first-launch welcome screen has no Connect button ──────
        # Route to the SPECIFIC onboarding handlers, never to the whole of
        # _setup_vpn_stage1_routing(). That function carries its own escalation
        # ladder, so a failed "Continue as guest" force-stopped ProtonVPN from
        # inside stage 2 and cascaded — 55 of 77 routes failed to reach Routing,
        # one device burned 345s that way.
        if fast_state == "onboarding_welcome":
            _slog(dlog, device, "setup_vpn", phase,
                  "ProtonVPN welcome/onboarding screen — routing to the specific "
                  "onboarding handler (no stage-1 escalation ladder)",
                  state=fast_state)

            cur = _svpn_activity(device)
            if "UpgradeOnboardingDialogActivity" in cur:
                ob_sig = _svpn_handle_upgrade_onboarding(device, dlog, guard)
            else:
                # AddAccountActivity, or the welcome screen that leads to it.
                ob_sig = _svpn_handle_add_account(device, dlog, guard)

            _slog(dlog, device, "setup_vpn", phase, "onboarding handler returned",
                  page=cur, signal=ob_sig)

            if ob_sig == SIG_SUCCESS:
                outcome, hit = _svpn_wait_activity(device, dlog, guard,
                                                   "RoutingActivity",
                                                   timeout=5.0, phase=phase)
                if outcome in _ALL_SIGNALS:
                    return outcome
                if outcome == "found":
                    _slog(dlog, device, "setup_vpn", phase,
                          "onboarding complete — RoutingActivity reached, "
                          "retrying Connect")
                    continue

            if ob_sig in _TERMINAL_SIGNALS:
                return ob_sig

            # Anything else: restart the VPN stage cleanly. Deliberately NOT the
            # 15s Connect race — there is no Connect button on this screen — and
            # deliberately no force-stop from inside this branch. The outer
            # setup_vpn cycle loop and its caps still own recovery.
            _slog(dlog, device, "setup_vpn", phase,
                  "onboarding did not reach RoutingActivity — restarting the VPN "
                  "stage (no Connect race, no force-stop here)",
                  signal=SIG_RESTART_SETUP_VPN)
            return SIG_RESTART_SETUP_VPN

        # ── Connect coordinate straight out of the SAME dump ──────────────
        elif fast_state in VPN_CONNECT_SCREEN_STATES or fast_ui.get("unprotected"):
            coord  = fast_ui.get("connect_bounds")
            source = "exact"
            if coord is None:
                coord  = fast_ui.get("connect_bounds_loose")
                source = "loose"
            if coord is None:
                # Same tree, looser reader — still no second dump.
                mined, _t2, _u2 = _svpn_connect_from_dump(device, dlog, root=fast_root)
                if mined:
                    coord, source = mined, "dump"
            if coord is None:
                coord  = _svpn_connect_fallback_coord(device, dlog)
                source = "fallback"
                _slog(dlog, device, "setup_vpn", phase,
                      "unprotected VPN screen visible — using immediate fallback "
                      "Connect coordinate", state=fast_state,
                      source=source, coord=f"({coord[0]},{coord[1]})",
                      elapsed_since_dump=time.time() - _t_dump)
            else:
                _slog(dlog, device, "setup_vpn", phase,
                      f"Connect coordinate resolved from the single dump "
                      f"({source}) — clicking immediately",
                      state=fast_state, source=source,
                      coord=f"({coord[0]},{coord[1]})",
                      elapsed_since_dump=time.time() - _t_dump)

            fcx, fcy = coord
            res = _connect_click_now(fcx, fcy, source)
            if res in _ALL_SIGNALS:
                return res
            if res == "registered":
                if _svpn_permission_dialog_visible(device):
                    _svpn_handle_permission_dialog(device, dlog, guard, phase)
                sig = _svpn_wait_for_tun0(device, dlog, guard, phase)
                if sig == "retry_connect":
                    continue
                return sig
            continue      # not registered — loop; the cap gate above stops us

        # ── SLOW PATH ────────────────────────────────────────────────────
        # Reached only when the classifier could confirm none of: a Connect
        # coordinate, the unprotected screen, or the onboarding screen.
        _slog(dlog, device, "setup_vpn", phase,
              "classifier could not confirm a Connect screen — "
              "falling back to the full detection race", state=fast_state)

        # V2 diagnostic only — does NOT change the decision below. Captured just
        # for the state the 4 Aug run could not explain: unknown, on
        # RoutingActivity, tunnel down. Reuses fast_root, so no extra dump.
        if fast_state == "unknown":
            try:
                _cur_act = _svpn_activity(device)
                if "RoutingActivity" in _cur_act and not vpn_activity(device):
                    _vpn_capture_unknown_ui(device, dlog, fast_root, fast_ui,
                                            activity=_cur_act)
            except Exception:
                pass

        result = _svpn_guarded_click(
            device, dlog, guard, phase=phase, label="Connect",
            expect_activity="RoutingActivity",
            find_fn=_find_connect, registered_fn=_connect_registered,
            max_attempts=CAP_CONNECT_ATTEMPTS,
            reg_timeout=_VPN_CONNECT_REG_WINDOW,
            counter_store=_connect_attempts,
            # Connect ONLY. This screen is where the reconfirm search was
            # measured missing a button that was still there; no other VPN
            # button opts in.
            use_initial_on_reconfirm_miss=True,
        )
        if result in _ALL_SIGNALS:
            return result

        if result == "not_found":
            # "not_found" now also covers "the page moved and nothing
            # registered", so establish WHERE we are before doing anything
            # drastic. One activity read serves the whole branch.
            _nf_activity = _svpn_activity(device)

            # Real registration evidence outranks any routing decision.
            try:
                _nf_tun0 = bool(vpn_activity(device))
            except Exception:
                _nf_tun0 = False
            if _nf_tun0:
                _slog(dlog, device, "setup_vpn", phase,
                      "Connect not found but tun0 is already up — nothing to click",
                      activity=_nf_activity, tun0="true")
                return _svpn_wait_for_tun0(device, dlog, guard, phase)

            # The screen is no longer the Connect screen. Escalating or clicking
            # a fallback coordinate here would act on whatever replaced it —
            # AddAccount, UpgradeOnboarding, the welcome screen, Home. Hand the
            # page back to stage 1, which knows how to route each of them.
            if "RoutingActivity" not in _nf_activity:
                _slog(dlog, device, "setup_vpn", phase,
                      "Connect not found and RoutingActivity is gone — "
                      "restarting setup_vpn so stage 1 can route this page",
                      activity=_nf_activity, tun0="false",
                      action="restart_setup_vpn", signal=SIG_RESTART_SETUP_VPN)
                return SIG_RESTART_SETUP_VPN

            # Still on RoutingActivity: the existing classification below is the
            # right thing to do — including the stale-coordinate case, which can
            # legitimately find a fresh Connect coordinate.
            ui = {}
            try:
                ui = _classify_protonvpn_ui(device, dlog)
            except Exception:
                pass
            state = ui.get("state", "unknown")
            _slog(dlog, device, "setup_vpn", phase,
                  "Connect not found — classifying VPN UI", state=state,
                  activity=_nf_activity)

            # Already protected / mid-connect: nothing to click, just wait.
            if ui.get("protected") or state.startswith("protected"):
                return _svpn_wait_for_tun0(device, dlog, guard, phase)
            if state == "connecting_or_changing":
                return _svpn_wait_for_tun0(device, dlog, guard, phase)

            # ── Fallback: the screen IS the disconnected Connect screen ──────
            # Some ProtonVPN builds never expose "Connect" as a text node — the
            # dump shows only "You are unprotected", the country row, and the
            # nav items. That is a DETECTION miss, not a broken app, and the old
            # behaviour (force-stop, then reinstall) was badly disproportionate.
            mined, mined_texts, mined_unprot = _svpn_connect_from_dump(device, dlog)
            if mined or mined_unprot or _svpn_unprotected_screen(device, dlog):
                state = "disconnected_connect_fallback"
                if mined:
                    cx, cy = mined
                    source = "dump"
                    _slog(dlog, device, "setup_vpn", phase,
                          "Connect mined from the UIA dump after the race missed",
                          state=state, coord=f"({cx},{cy})")
                else:
                    cx, cy = _svpn_connect_fallback_coord(device, dlog)
                    source = "fallback"
                    _slog(dlog, device, "setup_vpn", phase,
                          "Connect text missing but unprotected VPN screen visible — "
                          "using fallback Connect coordinate",
                          state=state, coord=f"({cx},{cy})")

                res = _connect_click_now(cx, cy, source)
                if res in _ALL_SIGNALS:
                    return res

                if res == "registered":
                    if _svpn_permission_dialog_visible(device):
                        _svpn_handle_permission_dialog(device, dlog, guard, phase)
                    sig = _svpn_wait_for_tun0(device, dlog, guard, phase)
                    if sig == "retry_connect":
                        continue
                    return sig

                # Not registered. Retry while the attempt budget allows — still
                # no force-stop and still no reinstall for a detection problem.
                if _ctr_get(_connect_attempts, device) < CAP_CONNECT_ATTEMPTS:
                    _slog(dlog, device, "setup_vpn", phase,
                          "fallback click did not register — retrying Connect",
                          attempt=f"{_ctr_get(_connect_attempts, device)}"
                                  f"/{CAP_CONNECT_ATTEMPTS}")
                    continue

                # Fallback has now also failed — NOW the diagnostics are worth
                # collecting, off-thread so they still do not delay anything.
                _svpn_save_connect_debug(device, dlog, mined_texts,
                                         "fallback click never registered")
                append_issue(device, "vpn_connect_failed",
                             "fallback Connect coordinate clicked but never "
                             "registered", fn="setup_vpn", phase=phase)
                return _vpn_escalate(device, dlog, guard, phase=phase,
                                     reason="fallback_connect_never_registered")

            # Genuinely unrecognised: not protected, not connecting, and not the
            # unprotected screen either. Escalation is appropriate here — and this
            # is the other point where diagnostics actually help.
            _svpn_save_connect_debug(device, dlog, mined_texts,
                                     f"no Connect screen recognised (state={state})")
            append_issue(device, "vpn_connect_failed",
                         f"Connect not found and screen is not the unprotected "
                         f"VPN screen, ui_state={state}",
                         fn="setup_vpn", phase=phase)
            return _vpn_escalate(device, dlog, guard, phase=phase,
                                 reason="connect_button_not_found")

        if result == "exhausted":
            append_issue(device, "vpn_connect_failed",
                         "Connect clicked but never registered",
                         fn="setup_vpn", phase=phase)
            return _vpn_escalate(device, dlog, guard, phase=phase,
                                 reason="connect_never_registered")

        # Registered. Clear the permission dialog if Android raised one.
        if _svpn_permission_dialog_visible(device):
            if not _svpn_handle_permission_dialog(device, dlog, guard, phase):
                if _stop_requested():
                    return SIG_MANUAL_STOP

        sig = _svpn_wait_for_tun0(device, dlog, guard, phase)
        if sig == "retry_connect":
            continue
        return sig


def _svpn_wait_for_tun0(device: str, dlog, guard: "VpnGuard", phase: str) -> str:
    """
    After a registered Connect, wait up to 30s for tun0, then reclassify.

    Returns SIG_* or the sentinel "retry_connect" when the caller should make
    another Connect attempt (budget permitting).
    """
    t0 = time.time()
    while time.time() - t0 < _VPN_TUN0_WAIT:
        chk = vpn_guard_checkpoint(device, dlog, guard, phase=phase)
        if chk != "ok":
            return chk

        try:
            if vpn_activity(device):
                _slog(dlog, device, "setup_vpn", phase, "tun0 UP — VPN connected",
                      elapsed=time.time() - t0, signal=SIG_SUCCESS)
                return SIG_SUCCESS
        except Exception:
            pass

        if _svpn_permission_dialog_visible(device):
            _svpn_handle_permission_dialog(device, dlog, guard, phase)

        time.sleep(1.0)

    # 30s elapsed with no tunnel — reclassify and route accordingly.
    ui = {}
    try:
        ui = _classify_protonvpn_ui(device, dlog)
    except Exception as exc:
        dlog.warning(f"[SETUP] {device} | _classify_protonvpn_ui raised: {exc!r}")
    state          = ui.get("state", "unknown")
    connect_seen   = ui.get("connect_bounds") is not None
    change_seen    = ui.get("change_server_bounds") is not None

    _slog(dlog, device, "setup_vpn", phase, "tun0 wait expired — reclassifying",
          elapsed=time.time() - t0, state=state,
          connect_visible=connect_seen, change_visible=change_seen)

    try:
        if vpn_activity(device):
            return SIG_SUCCESS
    except Exception:
        pass

    if ui.get("protected") or state.startswith("protected"):
        if change_seen and not connect_seen:
            return setup_vpn_change_server(device, dlog, guard)
        _slog(dlog, device, "setup_vpn", phase,
              "UI says protected but tun0 is down — trying a server change")
        return setup_vpn_change_server(device, dlog, guard)

    if connect_seen and change_seen:
        # Ambiguous UI: refresh the dump once before acting on stale bounds.
        _slog(dlog, device, "setup_vpn", phase,
              "both Connect and Change Server visible — refreshing UI first")
        time.sleep(2.0)
        return "retry_connect"

    if connect_seen:
        if _ctr_get(_connect_attempts, device) < CAP_CONNECT_ATTEMPTS:
            return "retry_connect"
        append_issue(device, "vpn_connect_failed",
                     "Connect still visible after all attempts",
                     fn="setup_vpn", phase=phase)
        return _vpn_escalate(device, dlog, guard, phase=phase,
                             reason="connect_still_visible")

    if change_seen:
        return setup_vpn_change_server(device, dlog, guard)

    if state == "connecting_or_changing":
        _slog(dlog, device, "setup_vpn", phase,
              "stuck in connecting/changing for 30s — escalating")
        append_issue(device, "vpn_connect_failed", "stuck connecting 30s",
                     fn="setup_vpn", phase=phase)
        return _vpn_escalate(device, dlog, guard, phase=phase,
                             reason="stuck_connecting")

    # Same reasoning as the Connect-not-found path: an unprotected screen with an
    # unreadable label is a detection miss, so retry the click rather than
    # escalating into force-stop/reinstall.
    if _svpn_unprotected_screen(device, dlog):
        _slog(dlog, device, "setup_vpn", phase,
              "UI state unreadable but unprotected VPN screen visible — "
              "retrying Connect instead of escalating",
              state="disconnected_connect_fallback")
        if _ctr_get(_connect_attempts, device) < CAP_CONNECT_ATTEMPTS:
            return "retry_connect"

    append_issue(device, "vpn_connect_failed", f"unknown VPN UI state={state}",
                 fn="setup_vpn", phase=phase)
    return _vpn_escalate(device, dlog, guard, phase=phase, reason="unknown_vpn_ui")


# ── setup-time Change Server ─────────────────────────────────────────────────

def setup_vpn_change_server(device: str, dlog, guard: "VpnGuard") -> str:
    """
    Change Server during SETUP only, before TargetApp is ever opened.

    Distinct from the runtime _vpn_change_server(): TargetAppGuard does not exist yet,
    VpnGuard stays active throughout, and there is no TargetApp to reopen afterwards.
    """
    phase = "stage2_change_server"
    _slog(dlog, device, "setup_vpn", phase, "setup-time Change Server flow")

    def _find_change(stage: str = "initial"):
        budget = 12.0 if stage == "initial" else 8.0
        pos = _svpn_find_button_race(device, dlog, "Change server",
                                     timeout=budget, stage=stage)
        if pos is None:
            pos = _svpn_find_button_race(device, dlog, "Change Server",
                                         timeout=6.0, stage=stage)
        return pos

    def _change_registered():
        try:
            if vpn_activity(device):
                return True
        except Exception:
            pass
        try:
            ui = _classify_protonvpn_ui(device, dlog)
            if ui.get("state") == "connecting_or_changing":
                return True
            if ui.get("change_server_bounds") is None:
                return True          # button disappeared / changed state
        except Exception:
            pass
        return False

    while True:
        if _stop_requested():
            return SIG_MANUAL_STOP

        used = _ctr_get(_change_server_attempts, device)
        if used >= CAP_CHANGE_SERVER_ATTEMPTS:
            _slog(dlog, device, "setup_vpn", phase, "Change Server cap reached",
                  attempt=f"{used}/{CAP_CHANGE_SERVER_ATTEMPTS}")
            append_issue(device, "vpn_change_server_failed",
                         f"{used} setup-time attempts", fn="setup_vpn", phase=phase)
            return _vpn_escalate(device, dlog, guard, phase=phase,
                                 reason="change_server_exhausted")

        chk = vpn_guard_checkpoint(device, dlog, guard, phase=phase)
        if chk != "ok":
            return chk

        result = _svpn_guarded_click(
            device, dlog, guard, phase=phase, label="Change server",
            expect_activity="RoutingActivity",
            find_fn=_find_change, registered_fn=_change_registered,
            max_attempts=CAP_CHANGE_SERVER_ATTEMPTS, reg_timeout=5.0,
            counter_store=_change_server_attempts,
        )
        if result in _ALL_SIGNALS:
            return result

        if result in ("not_found", "exhausted"):
            append_issue(device, "vpn_change_server_failed", f"result={result}",
                         fn="setup_vpn", phase=phase)
            return _vpn_escalate(device, dlog, guard, phase=phase,
                                 reason=f"change_server_{result}")

        # Registered — wait for the tunnel to settle on the new server.
        t0 = time.time()
        while time.time() - t0 < _VPN_TUN0_WAIT:
            chk = vpn_guard_checkpoint(device, dlog, guard, phase=phase)
            if chk != "ok":
                return chk
            try:
                if vpn_activity(device):
                    _slog(dlog, device, "setup_vpn", phase,
                          "tun0 UP after server change",
                          elapsed=time.time() - t0, signal=SIG_SUCCESS)
                    return SIG_SUCCESS
            except Exception:
                pass
            if _svpn_permission_dialog_visible(device):
                _svpn_handle_permission_dialog(device, dlog, guard, phase)
            time.sleep(1.0)

        _slog(dlog, device, "setup_vpn", phase,
              "no tun0 after server change — retrying if budget allows",
              elapsed=time.time() - t0)


# ── VPN escalation ladder ────────────────────────────────────────────────────

def _vpn_escalate(device: str, dlog, guard, phase: str = "",
                  reason: str = "") -> str:
    """
    The single escalation ladder for every ProtonVPN failure.

        1. force-stop + reopen ProtonVPN      (CAP_VPN_KILL_REOPEN per run)
        2. reinstall ProtonVPN                (SHARED CAP_VPN_INSTALL per run)
        3. program-initiated device reopen     (CAP_PROGRAM_DEVICE_REOPEN)
        4. fail the device

    Each tier is strictly more disruptive than the last, and each has its own
    per-run cap, so a device that keeps failing walks down the ladder once
    rather than looping on the cheapest fix forever.
    """
    fn = "_vpn_escalate"
    _slog(dlog, device, fn, phase, "VPN escalation entered", reason=reason,
          counters=_counters_snapshot(device))

    # ── Tier 1: force-stop and reopen the app ─────────────────────────────
    kills = _ctr_get(_vpn_kill_reopen_count, device)
    if kills < CAP_VPN_KILL_REOPEN:
        new = _ctr_inc(_vpn_kill_reopen_count, device, dlog, "vpn_kill_reopen")
        _slog(dlog, device, fn, phase, "TIER 1 — force-stop + reopen ProtonVPN",
              attempt=f"{new}/{CAP_VPN_KILL_REOPEN}", reason=reason)
        try:
            _adb_shell(device, "am", "force-stop", "ch.protonvpn.android", timeout=5)
        except Exception:
            pass
        time.sleep(2.0)
        _ctr_reset_session(device)      # fresh app session, fresh click budgets
        return SIG_RESTART_SETUP_VPN

    # ── Tier 2: reinstall (shared cap with setup_device's first install) ──
    if vpn_install_allowed(device, dlog, reason=f"escalate:{reason}",
                           phase=phase, fn=fn):
        _slog(dlog, device, fn, phase, "TIER 2 — reinstalling ProtonVPN",
              reason=reason)
        if guard is not None:
            try:
                guard.stop()
            except Exception:
                pass
        try:
            _adb_shell(device, "am", "force-stop", "ch.protonvpn.android", timeout=5)
            uninstall_package(device, "ch.protonvpn.android")
            time.sleep(2.0)
            install_vpn(device)
        except Exception as exc:
            dlog.error(f"[SETUP] {device} | VPN reinstall raised: {exc!r}")

        t0 = time.time()
        while time.time() - t0 < 100.0:
            if _stop_requested():
                return SIG_MANUAL_STOP
            if find_vpn(device):
                _slog(dlog, device, fn, phase, "ProtonVPN reinstalled",
                      elapsed=time.time() - t0)
                _vpn_kill_reopen_count.pop(device, None)   # fresh app, fresh tier-1 budget
                _ctr_reset_session(device)
                if guard is not None:
                    _vpn_guard_rearm(guard, 1)
                return SIG_RESTART_SETUP_VPN
            time.sleep(2.0)

        _slog(dlog, device, fn, phase, "reinstall did not complete in 100s")
        append_issue(device, "vpn_reinstall_failed", f"reason={reason}",
                     fn=fn, phase=phase)

    # ── Tier 3: reopen the emulator ───────────────────────────────────────
    _slog(dlog, device, fn, phase, "TIER 3 — program device reopen", reason=reason)
    sig = program_reopen_device(device, dlog, reason=f"vpn_escalate:{reason}",
                                phase=phase, fn=fn)
    if sig == SIG_RESTART_BEFORE_TARGET_APP:
        return sig

    # ── Tier 4: out of options ────────────────────────────────────────────
    _slog(dlog, device, fn, phase, "TIER 4 — all VPN recovery exhausted",
          reason=reason, signal=SIG_FAIL_DEVICE)
    append_issue(device, "setup_vpn_failed",
                 f"all recovery tiers exhausted, reason={reason}",
                 fn=fn, phase=phase)
    return SIG_FAIL_DEVICE


# ── public entry point ───────────────────────────────────────────────────────

def setup_vpn(device: str) -> str:
    """
    Phase 2 of prepare_target_app: ProtonVPN open, onboarded, and tun0 up.

    Owns the VpnGuard lifecycle end to end — created here, stopped in a finally
    block on every exit path including exceptions, so a guard thread can never
    outlive the phase it was monitoring.

    Returns a SIG_* signal.
    """
    dlog  = _get_device_logger(device)
    t0    = time.time()
    guard = VpnGuard(device, dlog)

    dlog.info("=" * 70)
    _slog(dlog, device, "setup_vpn", "start", "PHASE 2 begin",
          counters=_counters_snapshot(device))
    print(f"[{device}] setup_vpn: starting")

    guard.start()
    try:
        for cycle in range(1, CAP_STAGE_CYCLES + 1):
            if _stop_requested():
                return SIG_MANUAL_STOP

            _slog(dlog, device, "setup_vpn", "cycle", "stage cycle begin",
                  attempt=f"{cycle}/{CAP_STAGE_CYCLES}")

            sig = _sig_or_stop(_setup_vpn_stage1_routing(device, dlog, guard))
            if sig == SIG_RESTART_SETUP_VPN:
                _vpn_guard_rearm(guard, 1)
                continue
            if sig != SIG_SUCCESS:
                _slog(dlog, device, "setup_vpn", "end", "stage 1 failed",
                      elapsed=time.time() - t0, signal=sig)
                return sig

            sig = _sig_or_stop(_setup_vpn_stage2_connect(device, dlog, guard))
            if sig == SIG_RESTART_SETUP_VPN:
                _vpn_guard_rearm(guard, 1)
                continue

            # Never report success on UI text alone — only a live tun0 counts.
            if sig == SIG_SUCCESS:
                _verify = require_vpn_up_or_fail(
                    device, dlog, fn="setup_vpn", phase="final_verify",
                    issue_code="setup_vpn_failed",
                    detail="stage 2 reported success but tun0 is not active",
                )
                if _verify != SIG_SUCCESS:
                    _slog(dlog, device, "setup_vpn", "final_verify",
                          "stage 2 claimed success but tun0 is down — overriding",
                          signal=_verify)
                    sig = _verify

            _slog(dlog, device, "setup_vpn", "end", "PHASE 2 finished",
                  elapsed=time.time() - t0, signal=sig,
                  counters=_counters_snapshot(device))
            if sig == SIG_SUCCESS:
                print(f"[{device}] setup_vpn: VPN connected ({time.time() - t0:.1f}s)")
            return sig

        # Cycles exhausted without a verdict — restart the whole setup cleanly.
        _slog(dlog, device, "setup_vpn", "end",
              "stage cycles exhausted", elapsed=time.time() - t0,
              signal=SIG_RESTART_BEFORE_TARGET_APP)
        append_issue(device, "setup_vpn_failed",
                     f"{CAP_STAGE_CYCLES} stage cycles without success",
                     fn="setup_vpn", phase="cycle")
        return SIG_RESTART_BEFORE_TARGET_APP

    except FatalAPKError:
        raise
    except Exception:
        dlog.exception("setup_vpn() unhandled exception")
        append_issue(device, "setup_vpn_failed", "unhandled exception",
                     fn="setup_vpn", phase="exception")
        return SIG_FAIL_DEVICE
    finally:
        try:
            guard.stop()
        except Exception:
            pass
        _slog(dlog, device, "setup_vpn", "cleanup", "VpnGuard stopped")


# ------------------------------------------------------------
# 11. WORKFLOW: TARGET APPLICATION (TargetApp)
# ------------------------------------------------------------

target_app_stage            = {}
target_app_install_attempts = {}
_target_app_guards: dict    = {}   # device → TargetAppGuard instance (lives through dailies)
_target_app_kill_reopen_count: dict = {}  # device → int, kill+reopen TargetApp attempts, max 3

# Tracks whether the loading-stuck full-restart (emulator reopen + prepare_target_app restart)
# has already been used for this device this run.  Capped at 1 so _reset_device_state()
# clearing regular counters cannot allow a second full restart.
# Cleared only by reset_device_finished_state() (final done/failed/stop).
_loading_full_restart_count: dict = {}   # device → int (0 or 1)

# Tracks whether the VPN-recovery-failure full restart (emulator reopen + full prepare_target_app)
# has already been used for this device this run.  Independent of loading restart counter.
# NOT cleared by _reset_device_state() — only by reset_device_finished_state().
_vpn_recovery_full_restart_count: dict = {}   # device → int (0 or 1)

# Per-device expiry timestamp for the post-loading MinuteMaid handling window.
# Set to time.time()+30 when loading is confirmed done; cleared after use.
_target_app_post_loading_minutemaid_until: dict = {}   # device → float


def _handle_minutemaid_if_in_window(device: str, dlog) -> bool:
    """
    If MinuteMaidActivity is in foreground AND we are still inside the 30-second
    post-loading MinuteMaid window, press Back once and wait 1s.

    Returns True if Back was pressed (caller should re-check activity).
    Returns False if outside the window or MinuteMaid not in foreground.

    Design: does NOT add a fixed 30s delay — it only acts within the window
    when MinuteMaid actually appears.
    """
    until = _target_app_post_loading_minutemaid_until.get(device, 0)
    now   = time.time()
    current = _get_current_activity(device).strip()
    if "MinuteMaidActivity" not in current:
        return False
    if now >= until:
        dlog.info("[MINUTEMAID] outside post-loading window — not special-handled")
        return False
    remaining = until - now
    dlog.info(
        f"[MINUTEMAID] MinuteMaidActivity seen inside post-loading window "
        f"(remaining={remaining:.1f}s) — pressing Back"
    )
    press_back(device)
    time.sleep(1.0)
    dlog.info("[MINUTEMAID] Back pressed, continuing")
    return True
_available_version: str = ""       # read once from F2 at startup; updated if newer version found on device

# ── Guard interrupt mechanism ─────────────────────────────────────────────────
# Set by TargetAppGuard to interrupt the main thread mid-wait (e.g. inside when_on_page).
# when_on_page and _back_to_main check this every iteration and exit early if set.
# Cleared by the main thread after reading the guard signal.
_GUARD_INTERRUPT: dict = {}   # device → threading.Event()

def _guard_interrupt_event(device: str) -> "_threading.Event":
    """Get (or create) the interrupt Event for a device."""
    if device not in _GUARD_INTERRUPT:
        _GUARD_INTERRUPT[device] = _threading.Event()
    return _GUARD_INTERRUPT[device]

def _guard_interrupt_set(device: str) -> None:
    """Guard calls this to interrupt the main thread immediately."""
    _guard_interrupt_event(device).set()

def _guard_interrupt_clear(device: str) -> None:
    """Main thread calls this after reading the guard signal."""
    _guard_interrupt_event(device).clear()


# ── TargetAppGuard class ────────────────────────────────────────────────────────

# Page-check lockout window.  While active, TargetAppGuard suppresses ONLY the
# unexpected_home / unexpected_page checks.  Device health, network and manual
# stop stay live.  Used by the Sign-up flow (Google auth legitimately takes
# over the foreground) and by runtime vpn_change_server (ProtonVPN is expected
# to be in the foreground and must not be reported as an unexpected page).
_target_app_page_checks_paused_until: dict = {}   # device -> float (epoch)
_target_app_page_checks_pause_reason: dict = {}   # device -> str


def target_app_guard_pause_page_checks(device: str, seconds: float, reason: str,
                                dlog=None) -> None:
    """Suppress TargetAppGuard's unexpected_home/unexpected_page checks temporarily."""
    until = time.time() + max(0.0, seconds)
    _target_app_page_checks_paused_until[device] = until
    _target_app_page_checks_pause_reason[device] = reason
    if dlog is not None:
        dlog.info(
            f"[TARGET_APP-GUARD] {device} | page checks PAUSED for {seconds:.0f}s "
            f"(reason={reason}) — device/network/stop checks stay active"
        )


def target_app_guard_resume_page_checks(device: str, dlog=None) -> None:
    """Re-enable TargetAppGuard's page checks before the lockout would expire."""
    had = _target_app_page_checks_paused_until.pop(device, None)
    reason = _target_app_page_checks_pause_reason.pop(device, "")
    if had is not None and dlog is not None:
        dlog.info(f"[TARGET_APP-GUARD] {device} | page checks RESUMED (was: {reason})")


def target_app_page_checks_paused(device: str) -> bool:
    return time.time() < _target_app_page_checks_paused_until.get(device, 0.0)


class TargetAppGuard:
    """
    Passive background monitor for TargetApp.  DETECTS ONLY.

    Like VpnGuard, this thread performs no repair of any kind.  It records the
    first issue it sees, sets the guard-interrupt event so the main thread
    breaks out of any long wait, and stops.  Recovery belongs to
    target_app_guard_checkpoint() during setup and to guard_check_and_recover()
    during task runtime.

    Lifecycle
    ─────────
        setup_target_app() arms it before the first open_target_app attempt
        only shared device checks run until TargetApp actually opens
        set_target_app_opened() enables the TargetApp-specific checks
        it stays alive after setup succeeds so runtime tasks are covered

    Detects
    ───────
        device_closed_by_itself        emulator vanished, we did not close it
        device_not_responding          port alive, ADB dead >10s
        screenshot_failed_repeatedly   reported by the main thread
        network_issue                  connection-issue page seen, or tun0 down
        unexpected_home                Home/launcher >3s after TargetApp opened
        unexpected_page                TargetApp not foreground >3s after TargetApp opened

    The public method set is frozen: controller_ui_v7.py constructs this class
    directly and calls start / set_stage / set_target_app_opened / set_main_page_seen
    when it attaches to an already-running TargetApp session.
    """

    CHECK_INTERVAL = 1.0
    VPN_DOWN_GRACE = 3.0    # tun0 may blip during a legitimate server change
    # How often the guard takes its OWN screenshot for the connection-issue page.
    # Every tick was one extra screencap per second per device; while recording
    # that is the single biggest contributor to screencap contention.
    CONNECTION_PROBE_INTERVAL           = 3.0
    CONNECTION_PROBE_INTERVAL_RECORDING = 10.0

    def __init__(self, device: str, dlog):
        self.device = device
        self.dlog   = dlog

        self._stop_event  = _threading.Event()
        self._result      = None
        self._result_lock = _threading.Lock()

        self._stage      = 1
        self._stage_lock = _threading.Lock()

        self._target_app_opened      = False
        self._target_app_opened_lock = _threading.Lock()
        self._main_page_seen_time = None

        self._screenshot_none = False
        self._screenshot_lock = _threading.Lock()

        self._health     = HealthState()
        self._started_at = time.time()
        self._last_conn_probe = 0.0

        self._thread = _threading.Thread(
            target=self._run, daemon=True, name=f"target_app_guard_{device}"
        )

    # ── public API (frozen — controller depends on this) ─────────────────

    def start(self):
        """Start the monitor thread, replacing any existing TargetAppGuard first."""
        device   = self.device
        existing = _target_app_guards.get(device)
        if existing is not None and existing is not self:
            if existing._thread.is_alive():
                self.dlog.warning(
                    f"[TARGET_APP-GUARD] {device} | existing TargetAppGuard alive — stopping it "
                    f"before starting the replacement"
                )
                existing._stop_event.set()
                try:
                    existing._thread.join(timeout=3.0)
                except Exception:
                    pass
            else:
                self.dlog.debug(f"[TARGET_APP-GUARD] {device} | replacing stopped TargetAppGuard")
        _target_app_guards[device] = self
        self.dlog.info(f"[TARGET_APP-GUARD] {device} | started stage={self._stage}")
        if not self._thread.is_alive():
            self._thread.start()
        return self

    def stop(self):
        self._stop_event.set()
        try:
            self._thread.join(timeout=3.0)
        except Exception:
            pass
        self.dlog.info(f"[TARGET_APP-GUARD] {self.device} | stopped")

    def set_stage(self, stage: int):
        with self._stage_lock:
            self._stage = stage
        self.dlog.debug(f"[TARGET_APP-GUARD] {self.device} | stage -> {stage}")

    def set_target_app_opened(self):
        """Main thread calls this once TargetApp is confirmed in the foreground."""
        with self._target_app_opened_lock:
            self._target_app_opened = True
        self.dlog.debug(f"[TARGET_APP-GUARD] {self.device} | target_app_opened — TargetApp checks enabled")

    def set_main_page_seen(self):
        """Called when the TargetApp main page is first confirmed."""
        if self._main_page_seen_time is None:
            self._main_page_seen_time = time.time()
            self.dlog.debug(f"[TARGET_APP-GUARD] {self.device} | main_page_seen clock started")

    def report_screenshot(self, img_is_none: bool):
        """Main thread reports screenshot outcomes for the shared >10s check."""
        with self._screenshot_lock:
            self._screenshot_none = bool(img_is_none)

    def check(self) -> tuple:
        with self._result_lock:
            if self._result is not None:
                return self._result
        return ("ok",)

    def clear_result(self):
        with self._result_lock:
            self._result = None
        self._stop_event.clear()
        self._health.reset()

    def is_alive(self) -> bool:
        return self._thread.is_alive()

    # ── internal ─────────────────────────────────────────────────────────

    def _set_result(self, issue: str, stage: int, detail: str = ""):
        with self._result_lock:
            if self._result is None:
                self._result = (issue, stage, detail)
                self.dlog.warning(
                    f"[TARGET_APP-GUARD] {self.device} | DETECTED {issue} "
                    f"(stage={stage}) {detail}"
                )
        # Break the main thread out of when_on_page / _back_to_main / sleeps.
        _guard_interrupt_set(self.device)
        self._stop_event.set()

    def _run(self):
        device         = self.device
        dlog           = self.dlog
        home_since     = None
        unknown_since  = None
        vpn_down_since = None

        dlog.info(f"[TARGET_APP-GUARD] {device} | monitor loop running (detect-only)")

        while not self._stop_event.is_set():
            with self._stage_lock:
                stage = self._stage
            with self._target_app_opened_lock:
                target_app_opened = self._target_app_opened
            with self._screenshot_lock:
                shot_none = self._screenshot_none

            # ── 1. Shared device health — always active ───────────────────
            issue = shared_device_health(device, self._health, dlog,
                                         img_was_none=shot_none)
            if issue:
                self._set_result(issue, stage, "shared_device_health")
                return

            # Nothing TargetApp-specific matters until TargetApp is actually up.
            if not target_app_opened:
                self._stop_event.wait(timeout=self.CHECK_INTERVAL)
                continue

            # ── 2. Network: tun0 down past the grace window ───────────────
            try:
                tun_up = vpn_activity(device)
            except Exception:
                tun_up = True          # fail-open, do not invent an outage
            if not tun_up:
                now = time.time()
                if vpn_down_since is None:
                    vpn_down_since = now
                    dlog.warning(
                        f"[TARGET_APP-GUARD] {device} | tun0 DOWN — "
                        f"{self.VPN_DOWN_GRACE:.0f}s grace"
                    )
                elif now - vpn_down_since >= self.VPN_DOWN_GRACE:
                    self._set_result(
                        "network_issue", stage,
                        f"tun0 down {now - vpn_down_since:.1f}s"
                    )
                    return
            else:
                if vpn_down_since is not None:
                    dlog.info(f"[TARGET_APP-GUARD] {device} | tun0 recovered within grace")
                vpn_down_since = None

            # ── 3. Network: in-game connection-issue popup ────────────────
            # This is an EXTRA capture on top of whatever the main thread is
            # already taking. While screenrecord is running it is a major source
            # of screencap contention, so it is throttled hard — tun0 (check 2
            # above) already catches genuine network loss within 3s, and the
            # main thread screenshots the connection-issue page anyway.
            _ci_gap = (self.CONNECTION_PROBE_INTERVAL_RECORDING
                       if recording_enabled_or_active(device)
                       else self.CONNECTION_PROBE_INTERVAL)
            if (time.time() - self._last_conn_probe) >= _ci_gap:
                self._last_conn_probe = time.time()
                try:
                    img = get_screenshot(device, retries=0)
                    self.report_screenshot(img is None)
                    if img is not None and is_on_page(device, "connection issue", image=img):
                        self._set_result("network_issue", stage,
                                         "connection issue page visible")
                        return
                except Exception:
                    pass

            # ── 4. Page checks — suppressed inside a lockout window ───────
            if target_app_page_checks_paused(device):
                home_since    = None
                unknown_since = None
                self._stop_event.wait(timeout=self.CHECK_INTERVAL)
                continue

            current = (_get_current_activity(device) or "").strip()
            if not current or "null" in current.lower():
                home_since    = None
                unknown_since = None
                self._stop_event.wait(timeout=self.CHECK_INTERVAL)
                continue

            is_home = ("HomeActivity" in current) or ("launcher" in current.lower())
            is_target_app  = TARGET_APP_PACKAGE in current

            # 4a. Home/launcher after TargetApp opened — TargetApp dropped out
            if is_home:
                unknown_since = None
                now = time.time()
                if home_since is None:
                    home_since = now
                    dlog.info(
                        f"[TARGET_APP-GUARD] {device} | Home seen after TargetApp opened — "
                        f"{TARGET_APP_HOME_TOLERANCE:.0f}s tolerance started"
                    )
                elif now - home_since >= TARGET_APP_HOME_TOLERANCE:
                    self._set_result(
                        "unexpected_home", stage,
                        f"Home held {now - home_since:.1f}s activity={current!r}"
                    )
                    return
                self._stop_event.wait(timeout=self.CHECK_INTERVAL)
                continue

            home_since = None

            # 4b. TargetApp in the foreground — all good
            if is_target_app:
                if unknown_since is not None:
                    dlog.info(f"[TARGET_APP-GUARD] {device} | TargetApp foreground again — timer reset")
                unknown_since = None
                self._stop_event.wait(timeout=self.CHECK_INTERVAL)
                continue

            # 4c. Anything else, MinuteMaid/Google auth included, counts as an
            #     unexpected page unless a deliberate lockout is open (4 above).
            now = time.time()
            if unknown_since is None:
                unknown_since = now
                dlog.info(
                    f"[TARGET_APP-GUARD] {device} | TargetApp not foreground: {current!r} — "
                    f"{TARGET_APP_PAGE_TOLERANCE:.0f}s tolerance started"
                )
            elif now - unknown_since >= TARGET_APP_PAGE_TOLERANCE:
                self._set_result(
                    "unexpected_page", stage,
                    f"held {now - unknown_since:.1f}s activity={current!r}"
                )
                return

            self._stop_event.wait(timeout=self.CHECK_INTERVAL)

        dlog.info(f"[TARGET_APP-GUARD] {device} | monitor loop exited")


# ── TargetAppGuard main-thread checkpoint + recovery ───────────────────────────────

def _target_app_guard_rearm(guard: "TargetAppGuard", new_stage: int) -> "TargetAppGuard":
    """
    Re-arm an TargetAppGuard after main-thread recovery.  Reuses the object so
    existing references (including the controller's) stay valid.
    """
    if guard is None:
        return None
    device = guard.device
    dlog   = guard.dlog
    dlog.info(f"[TARGET_APP-GUARD] {device} | re-arming at stage {new_stage}")
    try:
        guard.stop()
    except Exception:
        pass
    guard.clear_result()
    guard.set_stage(new_stage)
    _guard_interrupt_clear(device)
    guard._stop_event.clear()
    guard._thread = _threading.Thread(
        target=guard._run, daemon=True, name=f"target_app_guard_{device}"
    )
    _target_app_guards[device] = guard
    guard._thread.start()
    dlog.info(f"[TARGET_APP-GUARD] {device} | re-armed at stage {new_stage}")
    return guard


def _restart_target_app_guard(guard: "TargetAppGuard", new_stage: int):
    """
    Backwards-compatible alias kept for the runtime task loop in device_worker,
    which calls _restart_target_app_guard(guard, 3) after a VPN server change.
    """
    return _target_app_guard_rearm(guard, new_stage)


def _target_app_guard_handle(device: str, dlog, result: tuple, guard: "TargetAppGuard",
                      phase: str = "", in_loading: bool = False) -> str:
    """
    Act on one TargetAppGuard detection.  Runs on the MAIN thread only.

    `in_loading` changes the network-issue outcome: during Loading() we must
    click OK and carry on loading rather than navigating back to main screen,
    because the game is still booting and there is no main screen to return to.

    Returns a SIG_* signal, or "ok" when nothing further is required.
    """
    issue  = result[0]
    stage  = result[1] if len(result) > 1 else None
    detail = result[2] if len(result) > 2 else ""
    fn     = "target_app_guard_checkpoint"

    if issue == "ok":
        return "ok"

    _slog(dlog, device, fn, phase or f"stage{stage}",
          f"handling guard issue: {issue}", detail=detail, in_loading=in_loading)

    # ── Emulator closed on its own ────────────────────────────────────────
    if issue == "device_closed_by_itself":
        return recover_self_closed_device(device, dlog, phase=phase, fn=fn)

    # ── Emulator frozen ───────────────────────────────────────────────────
    if issue == "device_not_responding":
        return program_reopen_device(device, dlog, reason="device_not_responding",
                                     phase=phase, fn=fn)

    # ── Screenshots dead ──────────────────────────────────────────────────
    if issue == "screenshot_failed_repeatedly":
        return handle_screenshot_failure(device, dlog, phase=phase, fn=fn)

    # ── Network: connection-issue page or tun0 down ───────────────────────
    if issue == "network_issue":
        return _target_app_handle_network_issue(device, dlog, guard,
                                         phase=phase, in_loading=in_loading)

    # ── TargetApp dropped back to Home ──────────────────────────────────────────
    if issue == "unexpected_home":
        now = time.time()
        stamps = [t for t in _unexpected_home_timestamps.get(device, [])
                  if now - t < UNEXPECTED_HOME_WINDOW]
        stamps.append(now)
        _unexpected_home_timestamps[device] = stamps
        _slog(dlog, device, fn, phase or "setup_target_app", "unexpected_home after TargetApp opened",
              events=f"{len(stamps)}/{CAP_UNEXPECTED_HOME_EVENTS}"
                     f" in {UNEXPECTED_HOME_WINDOW:.0f}s")

        if len(stamps) >= CAP_UNEXPECTED_HOME_EVENTS:
            _unexpected_home_timestamps[device] = []
            append_issue(device, "target_app_home_bounce_repeated",
                         f"{len(stamps)} home bounces within "
                         f"{UNEXPECTED_HOME_WINDOW:.0f}s", fn=fn, phase=phase)
            return program_reopen_device(device, dlog, reason="repeated_unexpected_home",
                                         phase=phase, fn=fn)

        # Open TargetApp directly — deliberately NOT a force-stop, the game process
        # is usually still alive and relaunching is far cheaper than a restart.
        _slog(dlog, device, fn, phase or "setup_target_app",
              "opening TargetApp directly after home bounce (no force-stop)")
        try:
            open_target_app(device, context="target_app_guard unexpected_home")
        except Exception as exc:
            dlog.warning(f"[TARGET_APP-GUARD] {device} | open_target_app raised: {exc!r}")
        if _wait_for_target_app_foreground(device, dlog, timeout=20.0):
            _target_app_guard_rearm(guard, stage or 3)
            guard.set_target_app_opened()
            return "ok"
        return program_reopen_device(device, dlog, reason="unexpected_home_recovery_failed",
                                     phase=phase, fn=fn)

    # ── Some other page took the foreground ───────────────────────────────
    if issue == "unexpected_page":
        for attempt in range(1, 4):
            if _stop_requested():
                return SIG_MANUAL_STOP
            try:
                press_back(device)
            except Exception as exc:
                dlog.warning(f"[TARGET_APP-GUARD] {device} | press_back raised: {exc!r}")
            time.sleep(1.0)
            current = (_get_current_activity(device) or "").strip()
            back_on_target_app = TARGET_APP_PACKAGE in current
            _slog(dlog, device, fn, phase or "setup_target_app",
                  "Back pressed to clear unexpected page",
                  attempt=f"{attempt}/3", page=current, recovered=back_on_target_app)
            if back_on_target_app:
                _target_app_guard_rearm(guard, stage or 3)
                guard.set_target_app_opened()
                return "ok"

        # Back x3 failed — try relaunching TargetApp before touching the emulator.
        _slog(dlog, device, fn, phase or "setup_target_app",
              "Back x3 failed — opening TargetApp directly")
        try:
            open_target_app(device, context="target_app_guard unexpected_page")
        except Exception as exc:
            dlog.warning(f"[TARGET_APP-GUARD] {device} | open_target_app raised: {exc!r}")
        if _wait_for_target_app_foreground(device, dlog, timeout=25.0):
            _target_app_guard_rearm(guard, stage or 3)
            guard.set_target_app_opened()
            return "ok"

        current = (_get_current_activity(device) or "").strip()
        append_issue(device, "target_app_unexpected_page",
                     f"activity={current!r} after Back x3 and open_target_app",
                     fn=fn, phase=phase)
        try:
            # `current` was already read for the Back-x3 decision.
            record_unexpected_page(
                device, dlog, current_activity=current,
                source_fn="_target_app_guard_handle", context=phase or "setup_target_app",
                page_guess=f"target_app_unknown_{stage}", issue_code="target_app_unexpected_page")
        except Exception:
            pass
        return program_reopen_device(device, dlog, reason="unexpected_page_recovery_failed",
                                     phase=phase, fn=fn)

    dlog.warning(f"[TARGET_APP-GUARD] {device} | unhandled guard issue {issue!r} — ignoring")
    return "ok"


def target_app_guard_checkpoint(device: str, dlog, guard: "TargetAppGuard",
                         phase: str = "", in_loading: bool = False) -> str:
    """
    The mandatory TargetAppGuard checkpoint.

    Call at least once per second inside every wait loop and immediately before
    every click during setup_target_app / Loading.

    Returns "ok" or a SIG_* signal.
    """
    if _stop_requested():
        return SIG_MANUAL_STOP

    # Pause gate FIRST, before reading the guard — see vpn_guard_checkpoint.
    gate = wait_while_paused(
        device, dlog, phase=phase, fn="target_app_guard_checkpoint",
        context="loading" if in_loading else "setup",
    )
    if gate == SIG_MANUAL_STOP:
        return SIG_MANUAL_STOP
    if gate == "resumed":
        if guard is not None:
            try:
                guard.clear_result()   # discard detections from the outage window
                _guard_interrupt_clear(device)
            except Exception:
                pass
        if in_loading:
            # Requirement: resume Loading rather than restarting setup.  The
            # only cleanup needed is the connection-issue popup, which the game
            # will have raised while the network was down.
            _slog(dlog, device, "target_app_guard_checkpoint", "loading",
                  "resumed during Loading — dismissing connection popup if present, "
                  "then continuing Loading")
            _loading_click_ok_if_popup(device, dlog, guard)
            return "ok"
        return SIG_RESTART_BEFORE_TARGET_APP

    if guard is None:
        return "ok"

    result = guard.check()
    if result[0] == "ok":
        return "ok"

    outcome = _target_app_guard_handle(device, dlog, result, guard,
                                phase=phase, in_loading=in_loading)
    try:
        guard.clear_result()
        _guard_interrupt_clear(device)
    except Exception:
        pass
    return outcome


def _wait_for_target_app_foreground(device: str, dlog, timeout: float = 25.0) -> bool:
    """
    Poll until the TargetApp activity is in the foreground.

    Returns True as soon as TargetApp is confirmed, False on timeout or manual stop.
    """
    t0 = time.time()
    while time.time() - t0 < timeout:
        if _stop_requested():
            return False
        current = (_get_current_activity(device) or "").strip()
        if TARGET_APP_PACKAGE in current:
            dlog.info(
                f"[TARGET_APP-GUARD] {device} | TargetApp foreground confirmed in "
                f"{time.time() - t0:.1f}s"
            )
            return True
        time.sleep(1.0)
    dlog.warning(
        f"[TARGET_APP-GUARD] {device} | TargetApp never reached foreground in {timeout:.0f}s "
        f"(last activity={(_get_current_activity(device) or '').strip()!r})"
    )
    return False


def _target_app_handle_network_issue(device: str, dlog, guard: "TargetAppGuard",
                              phase: str = "", in_loading: bool = False) -> str:
    """
    Network recovery for TargetApp: connection-issue popup and/or tun0 down.

    Order is deliberate — the host check comes first because clicking OK or
    changing VPN servers is pointless and counter-burning while the PC itself
    has no internet.
    """
    fn = "_target_app_handle_network_issue"
    _slog(dlog, device, fn, phase or "runtime",
          "network issue detected — checking device then host internet",
          in_loading=in_loading)

    net = check_network_and_maybe_pause(device, dlog, phase=phase, fn=fn)
    if net == SIG_MANUAL_STOP:
        return SIG_MANUAL_STOP
    if net == SIG_RESTART_BEFORE_TARGET_APP:
        # We paused for a host outage and it is back.  During Loading we stay
        # in Loading; everywhere else the caller restarts cleanly.
        if in_loading:
            _slog(dlog, device, fn, "loading",
                  "host internet restored during Loading — continuing Loading")
            _loading_click_ok_if_popup(device, dlog, guard)
            return "ok"
        return SIG_RESTART_BEFORE_TARGET_APP

    # Host is fine.  Give tun0 a short window to come back on its own.
    t0 = time.time()
    tun_up = False
    while time.time() - t0 < 5.0:
        if _stop_requested():
            return SIG_MANUAL_STOP
        try:
            if vpn_activity(device):
                tun_up = True
                break
        except Exception:
            pass
        time.sleep(1.0)

    _slog(dlog, device, fn, phase or "runtime", "tun0 recheck complete",
          elapsed=time.time() - t0, tun0="up" if tun_up else "down")

    if tun_up:
        _loading_click_ok_if_popup(device, dlog, guard)
        if guard is not None:
            _target_app_guard_rearm(guard, 3)
            guard.set_target_app_opened()
        return "ok"

    # tun0 is genuinely down — hand over to the runtime change-server flow.
    _slog(dlog, device, fn, phase or "runtime",
          "tun0 still down — running runtime vpn_change_server")
    try:
        ok = _vpn_change_server(device, dlog, guard, force_change=True)
    except Exception as exc:
        dlog.error(f"[TARGET_APP-GUARD] {device} | _vpn_change_server raised: {exc!r}")
        ok = False

    _slog(dlog, device, fn, phase or "runtime",
          "vpn_change_server finished", result="ok" if ok else "failed",
          reason=_last_vpn_change_failure_reason.get(device, ""))

    if ok:
        # Confirm the tunnel really came back — a True return is not enough.
        gate = require_vpn_up_or_fail(device, dlog, fn=fn,
                                      phase=phase or "runtime",
                                      issue_code="vpn_change_server_failed",
                                      detail="vpn_change_server reported success "
                                             "but tun0 is still down")
        if gate != SIG_SUCCESS:
            return gate
        if guard is not None:
            _target_app_guard_rearm(guard, 3)
            guard.set_target_app_opened()
        if in_loading:
            _loading_click_ok_if_popup(device, dlog, guard)
        _slog(dlog, device, fn, phase or "runtime",
              "vpn_change_server recovered the tunnel", signal="ok")
        return "ok"

    # Unrecoverable VPN loss with the device alive and host internet up.
    #
    # Deliberately NOT program_reopen_device and NOT restart_prepare_target_app: reopening
    # the emulator does not fix a VPN that will not connect, and restarting setup
    # would loop. Playing on without the tunnel is the one outcome that must never
    # happen, so the device fails here.
    if not host_internet_ok():
        sig = pause_controller_until_host_internet_back(
            device, dlog, phase=phase or "runtime", fn=fn)
        _slog(dlog, device, fn, phase or "runtime",
              "host outage, not a VPN failure — resuming after pause", signal=sig)
        return sig

    reason = _last_vpn_change_failure_reason.get(device, "unknown")
    _slog(dlog, device, fn, phase or "runtime",
          "VPN unrecoverable — refusing to continue TargetApp without VPN",
          reason=reason, tun0="down", host_internet="up",
          issue="vpn_change_server_failed", signal=SIG_FAIL_DEVICE)
    append_issue(device, "vpn_change_server_failed",
                 f"runtime recovery failed; refusing to continue TargetApp without VPN "
                 f"(reason={reason})", fn=fn, phase=phase)
    return SIG_FAIL_DEVICE


# ── _restart_target_app_guard ────────────────────────────────────────────────



# ── setup_target_app ─────────────────────────────────────────────────────────────

# =============================================================================
# PHASE 3 of prepare_target_app:  setup_target_app()  +  Loading()
# -----------------------------------------------------------------------------
# setup_target_app is deliberately thin: install, version, APK and XAPK checks all
# moved to setup_device, so all this phase does is arm TargetAppGuard, get the game
# process into the foreground, and hand over to Loading().
#
# Loading() owns everything between "TargetApp is in the foreground" and "we are
# standing on target app main", including the three interstitials that used to
# have no handling at all:
#
#     loading_warning   -> button "switch"    (Switch account)
#     loading_warning1  -> button "switch"    (Switch account)
#     google_signin     -> button "sign up"
#
# All three come from pages.json, which stays the source of truth for both the
# page fingerprints and the button rectangles.
# =============================================================================

_LOADING_PCT_REGION = (819, 899, 1170, 951)   # percent/"Now loading" OCR window
_LOADING_TOTAL_BUDGET = 1800.0                # absolute ceiling for one Loading()

# Pages that legitimately mean "the game is doing something", checked in this
# order.  The two warnings and the Google prompt are drawn OVER the loading
# screen, so they must be tested before "loading" or they are never seen.
_LOADING_PAGE_ORDER = (
    "loading_warning",
    "loading_warning1",
    "google_signin",
    "connection issue",
    "loading after update",
    "loading",
)


def detect_target_app_main_or_popup_context(device: str, dlog, img=None) -> str:
    """
    Classify a post-loading screen.

    Returns one of: "main_ark", "popup_over_main", "loading", "unknown".

    Wraps the existing _target_app_is_on_main_or_popup() so Loading() has a single
    vocabulary, and adds the loading check so the caller can tell "still
    loading" apart from "genuinely unrecognised".
    """
    if img is None:
        img = get_screenshot(device)
    if img is None:
        return "unknown"

    try:
        if is_on_page(device, "loading", image=img):
            return "loading"
    except Exception:
        pass

    try:
        kind = _target_app_is_on_main_or_popup(device, dlog, img)
    except Exception as exc:
        dlog.debug(f"[LOADING] {device} | _target_app_is_on_main_or_popup raised: {exc!r}")
        kind = "unknown"

    if kind == "main":
        return "main_ark"
    if kind == "popup":
        return "popup_over_main"

    # The old helper only knew about "new server reward", so Daily Rewards /
    # Login Reward fell through as unknown. Check the rest of the post-loading
    # popup set, then the title text, then the bottom bar.
    for pg in POST_LOADING_POPUPS:
        try:
            if is_on_page(device, pg, image=img):
                dlog.info(f"[LOADING] {device} | popup over main matched: {pg!r}")
                return "popup_over_main"
        except Exception:
            continue

    try:
        if _loading_reward_title_visible(device, dlog, img):
            return "popup_over_main"
        if _loading_main_bar_visible(device, dlog, img):
            return "popup_over_main"
    except Exception:
        pass

    return "unknown"


# How often the interstitial pages are re-checked while the loading screen is
# steadily matching. Every is_on_page costs an OCR pass (~9s on these devices),
# and the 03/08 run spent 3,039 evaluations on 528 percent ticks — 5.8 page
# checks per tick — almost all of them answering "no" about screens that had not
# appeared. The interstitials do not vanish on their own, so re-checking them on
# an interval costs latency, never a missed screen.
#
# REAL SECONDS, not iterations: an iteration can take anywhere from 1s to 20s
# depending on OCR, so an iteration count gave a wildly variable real interval.
LOADING_INTERSTITIAL_SECONDS = 10.0

_LOADING_INTERSTITIALS = ("loading_warning", "loading_warning1",
                          "google_signin", "connection issue")
_LOADING_PAGES_ONLY    = ("loading after update", "loading")


def _loading_detect_page(device: str, dlog, guard, fast_first: bool = False,
                         check_interstitials: bool = True,
                         last_loading_page: str = "") -> tuple:
    """
    Take one screenshot and classify it against the pages Loading cares about.

    Returns (page_name, img, full_sweep_ran).  page_name is a pages.json name,
    or one of "main_ark" / "popup_over_main" / "unknown" / "no_screenshot".

    `full_sweep_ran` reports what THIS call actually did, so the caller never
    has to infer it from what it asked for. The two differ in both directions:

      * asked for a sweep but the screenshot failed  -> nothing was classified,
        so False. The caller must not log a sweep or restart its timer.
      * did not ask for a sweep, but the remembered loading page stopped
        matching -> this function promotes itself to a complete sweep below,
        so True. The caller must restart its timer, or it would run a second
        redundant sweep moments later.

    It is True only when the COMPLETE _LOADING_PAGE_ORDER was walked. The
    one-check fast path and the reduced (interstitial-free) order both report
    False, because neither one looked for the overlay pages.

    `fast_first`  — the loading screen matched last iteration, so test it FIRST
                    and return the moment it matches again. While a download is
                    running this is true ~95% of the time and skips five OCR
                    passes per tick.
    `last_loading_page` — the EXACT page that matched last time ("loading" or
                    "loading after update"). Only that one is retried on the
                    fast path; testing both still cost an extra OCR pass every
                    tick for a page we already knew was not showing.
    `check_interstitials` — when False, skip the warning/sign-in/connection
                    checks entirely for this pass. The caller re-enables them
                    every LOADING_INTERSTITIAL_SECONDS of REAL time, and always
                    the moment the loading page stops matching.

    The screenshot outcome is reported to TargetAppGuard so the shared screenshot
    health check works without taking extra captures.
    """
    img = get_screenshot(device)
    if guard is not None:
        try:
            guard.report_screenshot(img is None)
        except Exception:
            pass
    if img is None:
        # No frame, so no page was evaluated. Reporting a completed sweep here
        # would let a run of failed captures silently suppress the interstitial
        # checks: each one would restart the caller's timer without a single
        # page having been looked at.
        return ("no_screenshot", None, False)

    # ── Fast path: is the SAME loading page still showing? ────────────────
    # Exactly one is_on_page call in the common case.
    #
    # ONLY taken when check_interstitials is False. When a full sweep is due we
    # must NOT return early here: the loading screen keeps matching underneath a
    # warning/sign-in overlay, so an early return would let those overlays go
    # undetected indefinitely — the sweep would be "due" every tick and never
    # actually run.
    if fast_first and not check_interstitials and last_loading_page in _LOADING_PAGES_ONLY:
        try:
            if is_on_page(device, last_loading_page, image=img):
                # One check, and it was not an interstitial — not a sweep.
                return (last_loading_page, img, False)
        except Exception as exc:
            dlog.debug(f"[LOADING] {device} | is_on_page({last_loading_page!r}) "
                       f"raised: {exc!r}")
        # It stopped matching — something changed, so run the COMPLETE sweep
        # immediately regardless of where the interstitial timer stands.
        check_interstitials = True

    # True from here on only if the order below is the complete one. Every
    # remaining return path runs AFTER that walk, so they all share this value.
    full_sweep_ran = bool(check_interstitials)

    # _LOADING_PAGE_ORDER puts the interstitials FIRST on purpose: the warning
    # and sign-in screens are drawn OVER the loading screen, so testing loading
    # first would mask them.
    order = (_LOADING_PAGE_ORDER if check_interstitials
             else tuple(p for p in _LOADING_PAGE_ORDER
                        if p not in _LOADING_INTERSTITIALS))
    for page in order:
        try:
            if is_on_page(device, page, image=img):
                return (page, img, full_sweep_ran)
        except Exception as exc:
            dlog.debug(f"[LOADING] {device} | is_on_page({page!r}) raised: {exc!r}")

    # Known post-loading popups, before the generic main/popup classifier.
    for pg in POST_LOADING_POPUPS:
        try:
            if is_on_page(device, pg, image=img):
                return ("popup_over_main", img, full_sweep_ran)
        except Exception:
            continue

    ctx = detect_target_app_main_or_popup_context(device, dlog, img)
    if ctx in ("main_ark", "popup_over_main"):
        return (ctx, img, full_sweep_ran)
    return ("unknown", img, full_sweep_ran)


def _loading_click_page_button(device: str, dlog, guard, page_name: str,
                               button_name: str, phase: str,
                               attempt_label: str) -> "tuple[int, int] | None":
    """
    Click a pages.json button using the setup checkpoint pattern:

        checkpoint -> reconfirm page -> resolve rect -> click -> log

    Returns the clicked coordinate, or None when the page moved on before the
    click (which is a success from the caller's point of view, not a failure).
    """
    # The checkpoint runs the pause gate; during Loading a resume returns "ok"
    # after dismissing the connection popup, so we simply re-verify the page
    # below and click only if it is genuinely still there.
    chk = target_app_guard_checkpoint(device, dlog, guard, phase=phase, in_loading=True)
    if chk != "ok":
        return None

    # Final pause check in the last moment before the tap.
    if _pause_requested():
        gate = wait_while_paused(device, dlog, phase=phase,
                                 fn="_loading_click_page_button", context="loading")
        if gate == SIG_MANUAL_STOP:
            return None
        _slog(dlog, device, "Loading", phase,
              "paused just before the tap — re-checking the page after resume",
              page=page_name, button=button_name)

    img = get_screenshot(device)
    if guard is not None:
        try:
            guard.report_screenshot(img is None)
        except Exception:
            pass
    if img is None or not is_on_page(device, page_name, image=img):
        _slog(dlog, device, "Loading", phase,
              f"{page_name} no longer visible before click — skipping",
              button=button_name, attempt=attempt_label)
        return None

    try:
        x1, y1, x2, y2 = _get_page_button_rect(page_name, button_name)
    except Exception as exc:
        dlog.error(f"[LOADING] {device} | button rect lookup failed: {exc!r}")
        return None

    cx, cy = (x1 + x2) // 2, (y1 + y2) // 2
    _slog(dlog, device, "Loading", phase, "clicking button",
          page=page_name, button=button_name, coord=f"({cx},{cy})",
          rect=f"({x1},{y1},{x2},{y2})", attempt=attempt_label)
    try:
        _raw_tap(device, cx, cy)
    except Exception as exc:
        dlog.error(f"[LOADING] {device} | tap raised: {exc!r}")
        record_event(device, "click", fn="_loading_click_page_button", phase=phase,
                     page=page_name, button=button_name, coord=f"({cx},{cy})",
                     attempt=attempt_label, result="tap_failed", error=str(exc))
        return None
    record_event(device, "click", fn="_loading_click_page_button", phase=phase,
                 page=page_name, button=button_name, coord=f"({cx},{cy})",
                 rect=f"({x1},{y1},{x2},{y2})", attempt=attempt_label,
                 result="tap_sent")
    return (cx, cy)


def _loading_click_ok_if_popup(device: str, dlog, guard) -> bool:
    """
    Dismiss the in-game "connection issue" popup if it is on screen.

    Up to CAP_CONNECTION_ISSUE_OK clicks.  Used both by Loading() and by the
    TargetAppGuard network handler, which is why it lives at module level.
    """
    for attempt in range(1, CAP_CONNECTION_ISSUE_OK + 1):
        # No target_app_guard_checkpoint here on purpose — this function is called FROM
        # the checkpoint's own resume path, so calling back into it would
        # recurse.  The pause gate is checked directly instead.
        if _pause_requested():
            if wait_while_paused(device, dlog, phase="connection_issue",
                                 fn="_loading_click_ok_if_popup",
                                 context="loading") == SIG_MANUAL_STOP:
                return False

        img = get_screenshot(device)
        if guard is not None:
            try:
                guard.report_screenshot(img is None)
            except Exception:
                pass
        if img is None:
            time.sleep(1.0)
            continue

        try:
            visible = is_on_page(device, "connection issue", image=img)
        except Exception:
            visible = False

        if not visible:
            if attempt > 1:
                _slog(dlog, device, "Loading", "connection_issue",
                      "connection issue popup gone", attempt=f"{attempt-1}")
            return True

        try:
            x1, y1, x2, y2 = _get_page_button_rect("connection issue", "ok")
            cx, cy = (x1 + x2) // 2, (y1 + y2) // 2
            _slog(dlog, device, "Loading", "connection_issue", "clicking OK",
                  page="connection issue", button="ok", coord=f"({cx},{cy})",
                  attempt=f"{attempt}/{CAP_CONNECTION_ISSUE_OK}")
            _raw_tap(device, cx, cy)
            record_event(device, "click", fn="_loading_click_ok_if_popup",
                         phase="connection_issue", page="connection issue",
                         button="ok", coord=f"({cx},{cy})",
                         attempt=f"{attempt}/{CAP_CONNECTION_ISSUE_OK}",
                         result="tap_sent")
        except Exception as exc:
            dlog.error(f"[LOADING] {device} | OK click failed: {exc!r}")
        time.sleep(1.5)

    _slog(dlog, device, "Loading", "connection_issue",
          "popup still visible after all OK attempts",
          attempt=f"{CAP_CONNECTION_ISSUE_OK}/{CAP_CONNECTION_ISSUE_OK}")
    return False


# ── loading_warning / loading_warning1 ───────────────────────────────────────

def _loading_handle_warning(device: str, dlog, guard, page_name: str) -> str:
    """
    Handle loading_warning / loading_warning1 by clicking the "switch" button
    (labelled "Switch account" on screen).

    Registration is generous on purpose: any move away from the warning page
    counts, because the game jumps to several different next screens depending
    on account state.
    """
    phase = page_name
    used  = _ctr_inc(_loading_warning_switch_attempts, device, dlog,
                     "loading_warning_switch")
    label = f"{used}/{CAP_SWITCH_ATTEMPTS}"

    if used > CAP_SWITCH_ATTEMPTS:
        _slog(dlog, device, "Loading", phase,
              "Switch attempts exhausted — failing device",
              page=page_name, button="switch", attempt=label,
              signal=SIG_FAIL_DEVICE)
        append_issue(device, "loading_warning_switch_failed",
                     f"page={page_name} after {CAP_SWITCH_ATTEMPTS} Switch attempts",
                     fn="Loading", phase=phase)
        return SIG_FAIL_DEVICE

    t_seen = time.time()
    _slog(dlog, device, "Loading", phase, "warning page detected",
          page=page_name, attempt=label)

    coord = _loading_click_page_button(device, dlog, guard, page_name,
                                       "switch", phase, label)
    if coord is None:
        # Page vanished on its own — re-dispatch and see where we landed.
        return "continue"

    # Wait up to 5s for the click to register.
    t_click = time.time()
    while time.time() - t_click < 5.0:
        chk = target_app_guard_checkpoint(device, dlog, guard, phase=phase, in_loading=True)
        if chk != "ok":
            return chk

        page, _img, _full = _loading_detect_page(device, dlog, guard)
        if page not in (page_name, "no_screenshot"):
            _slog(dlog, device, "Loading", phase, "Switch click REGISTERED",
                  page=page_name, button="switch", coord=f"{coord}",
                  attempt=label, elapsed=time.time() - t_click,
                  next_page=page, seen_after=time.time() - t_seen)
            record_event(device, "click", fn="_loading_handle_warning", phase=phase,
                         page=page_name, button="switch", coord=f"{coord}",
                         attempt=label, registered=True, result="registered",
                         next_page=page,
                         elapsed_since_click=round(time.time() - t_click, 2))
            return "continue"
        time.sleep(0.5)

    _slog(dlog, device, "Loading", phase, "Switch click did NOT register",
          page=page_name, button="switch", coord=f"{coord}", attempt=label,
          elapsed=time.time() - t_click)
    record_event(device, "click", fn="_loading_handle_warning", phase=phase,
                 page=page_name, button="switch", coord=f"{coord}", attempt=label,
                 registered=False, result="not_registered",
                 elapsed_since_click=round(time.time() - t_click, 2))
    return "continue"


# ── google_signin ────────────────────────────────────────────────────────────

def _loading_handle_google_signin(device: str, dlog, guard) -> str:
    """
    Handle the Google Play sign-in prompt by clicking "sign up".

    Google's own auth screens legitimately take over the foreground for several
    seconds afterwards, which TargetAppGuard would otherwise report as
    unexpected_page.  So immediately after the click we open a 15-second page-
    check lockout.  Device health, network and manual stop all stay live during
    it — only the two page checks are suppressed.
    """
    phase = "google_signin"
    used  = _ctr_inc(_google_signin_signup_attempts, device, dlog,
                     "google_signin_signup")
    label = f"{used}/{CAP_SIGNUP_ATTEMPTS}"

    if used > CAP_SIGNUP_ATTEMPTS:
        _slog(dlog, device, "Loading", phase,
              "Sign up attempts exhausted — failing device",
              page=phase, button="sign up", attempt=label, signal=SIG_FAIL_DEVICE)
        append_issue(device, "google_signin_signup_failed",
                     f"still on google_signin after {CAP_SIGNUP_ATTEMPTS} attempts",
                     fn="Loading", phase=phase)
        return SIG_FAIL_DEVICE

    t_seen = time.time()
    _slog(dlog, device, "Loading", phase, "google_signin detected", attempt=label)

    coord = _loading_click_page_button(device, dlog, guard, "google_signin",
                                       "sign up", phase, label)
    if coord is None:
        return "continue"

    target_app_guard_pause_page_checks(device, SIGNUP_PAGE_GUARD_LOCKOUT,
                                reason="google_signin_signup", dlog=dlog)
    _slog(dlog, device, "Loading", phase,
          "page checks paused after Sign up click",
          coord=f"{coord}", attempt=label,
          lockout=f"{SIGNUP_PAGE_GUARD_LOCKOUT:.0f}s")

    try:
        t_click = time.time()
        while time.time() - t_click < SIGNUP_PAGE_GUARD_LOCKOUT:
            # Device / network / stop checks stay active via the checkpoint;
            # only unexpected_home and unexpected_page are suppressed.
            chk = target_app_guard_checkpoint(device, dlog, guard, phase=phase, in_loading=True)
            if chk != "ok":
                return chk

            page, _img, _full = _loading_detect_page(device, dlog, guard)
            if page in ("loading", "loading after update", "main_ark",
                        "popup_over_main", "connection issue"):
                _slog(dlog, device, "Loading", phase,
                      "sign-in accepted — resuming page checks",
                      next_page=page, attempt=label,
                      elapsed=time.time() - t_click,
                      seen_after=time.time() - t_seen)
                record_event(device, "click", fn="_loading_handle_google_signin",
                             phase=phase, page="google_signin", button="sign up",
                             coord=f"{coord}", attempt=label, registered=True,
                             result="registered", next_page=page,
                             elapsed_since_click=round(time.time() - t_click, 2))
                return "continue"
            time.sleep(1.0)

        _slog(dlog, device, "Loading", phase,
              "lockout expired with no progress page", attempt=label,
              elapsed=time.time() - t_click)
        return "continue"
    finally:
        target_app_guard_resume_page_checks(device, dlog)


# ── connection issue during Loading ──────────────────────────────────────────

def _loading_handle_connection_issue(device: str, dlog, guard) -> str:
    """
    Connection issue while the game is still loading.

    Deliberately different from the runtime handler: we do NOT navigate back to
    main screen and we do NOT restart a task, because the game has not finished
    booting and there is no main screen to go back to.  Fix the network, dismiss
    the popup, and carry on loading.
    """
    phase = "connection_issue"
    _slog(dlog, device, "Loading", phase, "connection issue during Loading")

    net = check_network_and_maybe_pause(device, dlog, phase=phase, fn="Loading")
    if net == SIG_MANUAL_STOP:
        return SIG_MANUAL_STOP
    if net == SIG_RESTART_BEFORE_TARGET_APP:
        # Host outage resolved.  Stay in Loading per spec.
        _slog(dlog, device, "Loading", phase,
              "host internet restored — dismissing popup and continuing Loading")
        _loading_click_ok_if_popup(device, dlog, guard)
        return "continue"

    # Host is fine — give tun0 a moment, then change server if still down.
    tun_up = False
    t0 = time.time()
    while time.time() - t0 < 5.0:
        if _stop_requested():
            return SIG_MANUAL_STOP
        try:
            if vpn_activity(device):
                tun_up = True
                break
        except Exception:
            pass
        time.sleep(1.0)

    if not tun_up:
        _slog(dlog, device, "Loading", phase,
              "tun0 still down — runtime vpn_change_server", tun0="down")
        target_app_guard_pause_page_checks(device, 120.0,
                                    reason="vpn_change_server_during_loading",
                                    dlog=dlog)
        try:
            ok = _vpn_change_server(device, dlog, guard, force_change=True)
        except Exception as exc:
            dlog.error(f"[LOADING] {device} | _vpn_change_server raised: {exc!r}")
            ok = False
        finally:
            target_app_guard_resume_page_checks(device, dlog)

        reason = _last_vpn_change_failure_reason.get(device, "unknown")
        _slog(dlog, device, "Loading", phase, "vpn_change_server finished",
              result="ok" if ok else "failed", reason=reason)

        if not ok:
            # Never keep loading without a tunnel. Not a reopen, not a restart —
            # the device fails, because continuing would put the game online with
            # the real IP exposed.
            if not host_internet_ok():
                sig = pause_controller_until_host_internet_back(
                    device, dlog, phase=phase, fn="Loading")
                _slog(dlog, device, "Loading", phase,
                      "host outage during Loading, not a VPN failure", signal=sig)
                return sig
            _slog(dlog, device, "Loading", phase,
                  "VPN unrecoverable during Loading — refusing to continue",
                  tun0="down", host_internet="up",
                  issue="vpn_change_server_failed", signal=SIG_FAIL_DEVICE)
            append_issue(device, "vpn_change_server_failed",
                         f"recovery failed during Loading; refusing to continue "
                         f"without VPN (reason={reason})",
                         fn="Loading", phase=phase)
            return SIG_FAIL_DEVICE

        if guard is not None:
            _target_app_guard_rearm(guard, 3)
            guard.set_target_app_opened()

    # Confirm the tunnel before resuming — this is the gate that decides whether
    # Loading may continue at all.
    gate = require_vpn_up_or_fail(device, dlog, fn="Loading", phase=phase,
                                  issue_code="vpn_down_during_loading",
                                  detail="connection issue resolved but tun0 is "
                                         "still down; refusing to continue Loading")
    if gate != SIG_SUCCESS:
        return gate

    _loading_click_ok_if_popup(device, dlog, guard)
    _slog(dlog, device, "Loading", phase,
          "network recovered and tun0 confirmed — continuing Loading "
          "(no back_to_main, no task restart)", tun0="up")
    return "continue"


# ── loading percent watch ────────────────────────────────────────────────────

def _loading_watch_percent(device: str, dlog, guard) -> str:
    """
    Watch the loading percentage until it finishes or stalls.

    Two things end this loop successfully:
      * the loading page disappears and STAYS gone for 5 continuous seconds
      * a different known page appears (warning / sign-in / connection issue),
        which the caller then dispatches

    One thing ends it unsuccessfully: no readable percent increase for 60s.
    An unreadable percent is not a stall — OCR misses happen constantly during
    scene transitions, and only a genuinely frozen number matters.
    """
    phase       = "loading_percent"
    t0          = time.time()
    last_pct    = None
    last_change = time.time()
    gone_since  = None
    mode        = "launch"

    _slog(dlog, device, "Loading", phase, "watching loading percent",
          region=f"{_LOADING_PCT_REGION}",
          stuck_threshold=f"{LOADING_STUCK_THRESHOLD:.0f}s",
          gone_confirm=f"{LOADING_GONE_CONFIRM:.0f}s")

    last_loading_page = ""    # the EXACT loading page that matched last pass
    last_full_sweep   = 0.0   # monotonic timestamp of the last interstitial sweep

    while time.time() - t0 < _LOADING_TOTAL_BUDGET:
        chk = target_app_guard_checkpoint(device, dlog, guard, phase=phase, in_loading=True)
        if chk != "ok":
            return chk

        # Cadence measured in REAL SECONDS. An iteration can take 1s or 20s
        # depending on OCR, so counting iterations gave an unpredictable actual
        # interval — the interstitials could go unchecked for a minute.
        now_m    = time.monotonic()
        due_full = (last_full_sweep == 0.0
                    or (now_m - last_full_sweep) >= LOADING_INTERSTITIAL_SECONDS)
        # A complete sweep also happens whenever we have no known loading page
        # to retry, and _loading_detect_page escalates to one on its own if the
        # remembered page stops matching.
        want_full = due_full or not last_loading_page
        prev_page = last_loading_page

        # full_sweep_ran is what the detector ACTUALLY did, which is not always
        # what want_full asked for: a failed screenshot means no sweep despite
        # want_full, and a remembered page that stopped matching means a sweep
        # despite want_full being False. Driving the log and the timer off the
        # request instead of the result gave a sweep entry for ticks that never
        # classified anything, and skipped the entry for sweeps that did.
        page, img, full_sweep_ran = _loading_detect_page(
            device, dlog, guard,
            fast_first=bool(last_loading_page),
            check_interstitials=want_full,
            last_loading_page=last_loading_page,
        )

        if full_sweep_ran and page != "no_screenshot":
            # Stamped AFTER the sweep finished, from a fresh reading. Using the
            # pre-sweep timestamp made the next sweep fall due sooner than
            # LOADING_INTERSTITIAL_SECONDS by however long the sweep itself took
            # — which on these devices is several OCR passes.
            _swept_at = time.monotonic()
            if not want_full:
                _reason = "remembered_page_changed"
            elif not prev_page:
                _reason = "no_previous_loading_page"
            else:
                _reason = "periodic"
            _slog(dlog, device, "Loading", phase,
                  "periodic full interstitial sweep",
                  reason=_reason,
                  since_last=(0.0 if last_full_sweep == 0.0
                              else _swept_at - last_full_sweep),
                  took=_swept_at - now_m, page=page)
            last_full_sweep = _swept_at

        last_loading_page = page if page in ("loading", "loading after update") else ""

        if page == "no_screenshot":
            last_loading_page = ""
            time.sleep(1.0)
            continue

        # A different known page took over — let the dispatcher handle it.
        if page in ("loading_warning", "loading_warning1", "google_signin",
                    "connection issue"):
            _slog(dlog, device, "Loading", phase,
                  "another known page appeared during loading",
                  next_page=page, elapsed=time.time() - t0)
            return "continue"

        if page in ("main_ark", "popup_over_main"):
            # Distinct result, NOT "continue".
            # Returning "continue" here sent Loading() back to its dispatch loop,
            # which then classified the Daily Rewards popup as "unknown" and spun
            # for minutes. The game is loaded at this point — go straight to
            # post-loading resolution.
            _slog(dlog, device, "Loading", phase,
                  "game reached main/popup while watching percent — "
                  "handing over to post-loading resolution",
                  next_page=page, elapsed=time.time() - t0)
            return "post_loading_ready"

        if page not in ("loading", "loading after update"):
            # Loading page is not visible. Require it to stay gone.
            now = time.time()
            if gone_since is None:
                gone_since = now
                _slog(dlog, device, "Loading", phase,
                      "loading page gone — starting confirmation timer",
                      confirm=f"{LOADING_GONE_POSTCHECK:.0f}s",
                      elapsed=now - t0)
            elif now - gone_since >= LOADING_GONE_POSTCHECK:
                # 3 continuous seconds without the loading screen: stop watching
                # percent and run the ordered post-loading checks. Waiting the
                # full 5s only delayed noticing the reward popup.
                _slog(dlog, device, "Loading", phase,
                      "loading gone for the post-check window — "
                      "stopping percent watch",
                      gone_for=now - gone_since, elapsed=now - t0)
                _mark_page_seen(device, "target app main")
                _target_app_post_loading_minutemaid_until[device] = time.time() + 30.0
                return "loading_done"
            time.sleep(1.0)
            continue

        # Loading page IS visible.
        gone_since = None
        _mark_page_seen(device, "loading")

        raw = ""
        try:
            raw = check_text(device, *_LOADING_PCT_REGION, image=img) or ""
            if not raw:
                raw = check_text1(device, *_LOADING_PCT_REGION, image=img) or ""
        except Exception as exc:
            dlog.debug(f"[LOADING] {device} | percent OCR raised: {exc!r}")

        chk = target_app_guard_checkpoint(device, dlog, guard, phase=phase, in_loading=True)
        if chk != "ok":
            return chk

        now = time.time()

        # "Now loading" means a full asset download, which is legitimately slow.
        if mode == "launch" and raw and "now loading" in raw.lower():
            mode        = "download"
            last_change = now
            _slog(dlog, device, "Loading", phase,
                  "'Now loading' seen — switching to download mode",
                  elapsed=now - t0)

        m   = re.search(r"(\d+)\s*%", raw)
        pct = int(m.group(1)) if m else None

        if pct is not None:
            if last_pct is None or pct > last_pct:
                _slog(dlog, device, "Loading", phase, "progress",
                      percent=f"{last_pct}->{pct}%", mode=mode, elapsed=now - t0)
                last_pct    = pct
                last_change = now
            elif pct < last_pct and mode == "download" and "now loading" not in raw.lower():
                # Download finished and the boot loader restarted the bar.
                _slog(dlog, device, "Loading", phase,
                      "percent reset — download done, switching to launch mode",
                      percent=f"{last_pct}->{pct}%", elapsed=now - t0)
                mode        = "launch"
                last_pct    = pct
                last_change = now
        else:
            dlog.debug(f"[LOADING] {device} | percent unreadable (raw={raw!r})")

        stall = now - last_change
        if stall >= LOADING_STUCK_THRESHOLD:
            _slog(dlog, device, "Loading", phase, "LOADING STUCK",
                  percent=f"{last_pct}%", stalled_for=stall, mode=mode,
                  elapsed=now - t0)
            return "loading_stuck"

        time.sleep(2.0)

    _slog(dlog, device, "Loading", phase, "overall loading budget exceeded",
          elapsed=time.time() - t0, percent=f"{last_pct}%")
    return "loading_stuck"


def _loading_stuck_escalate(device: str, dlog, guard) -> str:
    """
    Escalate a stuck loading screen, one rung per call:

        1. relaunch TargetApp normally
        2. force-stop TargetApp, then relaunch
        3. reinstall TargetApp, then relaunch
        4. give up

    The rung is stored per device so escalation does not restart from the top
    every time Loading() is re-entered.
    """
    phase = "loading_stuck"
    rung  = _loading_attempt_state.get(device, 0)
    _loading_attempt_state[device] = rung + 1

    _slog(dlog, device, "Loading", phase, "escalating stuck loading",
          attempt=f"{rung + 1}/3")

    if rung == 0:
        _slog(dlog, device, "Loading", phase, "rung 1 — plain TargetApp relaunch")
        return SIG_RESTART_SETUP_TARGET_APP

    if rung == 1:
        _slog(dlog, device, "Loading", phase, "rung 2 — force-stop then relaunch")
        try:
            _adb_shell(device, "am", "force-stop",
                       TARGET_APP_PACKAGE, timeout=5)
        except Exception:
            pass
        time.sleep(2.0)
        return SIG_RESTART_SETUP_TARGET_APP

    if rung == 2:
        _slog(dlog, device, "Loading", phase, "rung 3 — reinstall TargetApp then relaunch")
        try:
            _adb_shell(device, "am", "force-stop",
                       TARGET_APP_PACKAGE, timeout=5)
            uninstall_package(device, TARGET_APP_PACKAGE)
            time.sleep(2.0)
            install_target_app(device)
        except FatalAPKError:
            raise
        except Exception as exc:
            dlog.error(f"[LOADING] {device} | TargetApp reinstall raised: {exc!r}")
        target_app_install_attempts[device] = True

        t0 = time.time()
        while time.time() - t0 < 120.0:
            if _stop_requested():
                return SIG_MANUAL_STOP
            if find_target_app(device):
                _slog(dlog, device, "Loading", phase, "TargetApp reinstalled",
                      elapsed=time.time() - t0)
                return SIG_RESTART_SETUP_TARGET_APP
            time.sleep(2.0)
        _slog(dlog, device, "Loading", phase, "TargetApp reinstall did not complete")

    _slog(dlog, device, "Loading", phase,
          "still stuck after reinstall — failing device", signal=SIG_FAIL_DEVICE)
    append_issue(device, "loading_stuck_failed",
                 "stuck after plain relaunch, force-stop and reinstall",
                 fn="Loading", phase=phase)
    return SIG_FAIL_DEVICE


# ── Loading() ────────────────────────────────────────────────────────────────

# Popups that legitimately appear the moment the game finishes loading, in the
# order they should be checked.  "login reward" / "monthly reward" are the Daily
# Rewards / Login Reward dialogs that previously left Loading spinning on
# "unknown" for minutes because nothing recognised them.
POST_LOADING_POPUPS = (
    "login reward",
    "monthly reward",
    "new server reward",
    "signup reward not collected",
    "daily free pack",
)

# Title strings that identify the reward dialogs even when the pixel fingerprint
# drifts (event skins change the artwork but not the heading).
_REWARD_TITLE_TEXTS = ("daily rewards", "login reward", "monthly login")

# Bottom-bar labels. If these are on screen, the game IS loaded and on the main
# app — anything else covering it is a popup, not an unknown page.
_MAIN_BAR_TEXTS = ("quests", "explore", "items", "mail", "more", "map")

LOADING_GONE_POSTCHECK = 3.0   # loading absent this long -> run post-loading checks


def _loading_popup_close(device: str, dlog, guard, page_name: str) -> bool:
    """
    Close a known post-loading popup via its `close` button.

    Falls back to a single Back press when the page has no close rect — some
    dialogs in pages.json only define day-cells and a title.
    """
    try:
        x1, y1, x2, y2 = _get_page_button_rect(page_name, "close")
        cx, cy = (x1 + x2) // 2, (y1 + y2) // 2
        _slog(dlog, device, "Loading", "post_loading", "closing popup",
              page=page_name, button="close", coord=f"({cx},{cy})")
        _raw_tap(device, cx, cy)
        record_event(device, "click", fn="_loading_popup_close", phase="post_loading",
                     page=page_name, button="close", coord=f"({cx},{cy})",
                     result="tap_sent")
        time.sleep(1.2)
        return True
    except Exception as exc:
        dlog.debug(f"[LOADING] {device} | no close rect for {page_name!r}: {exc!r}")

    _slog(dlog, device, "Loading", "post_loading",
          "popup has no close button — pressing Back once", page=page_name)
    try:
        press_back(device)
        time.sleep(1.2)
        return True
    except Exception as exc:
        dlog.warning(f"[LOADING] {device} | Back after popup raised: {exc!r}")
    return False


def _loading_reward_title_visible(device: str, dlog, img) -> bool:
    """
    True when a reward dialog's heading is on screen.

    Text-based backstop for the pixel fingerprints: seasonal reskins change the
    artwork constantly but the heading stays "Daily Rewards" / "Login Reward".
    """
    if img is None:
        return False
    try:
        raw = (check_text(device, 600, 40, 1350, 210, image=img) or "").lower()
        if not raw:
            raw = (check_text1(device, 600, 40, 1350, 210, image=img) or "").lower()
    except Exception:
        return False
    hit = any(t in raw for t in _REWARD_TITLE_TEXTS)
    if hit:
        dlog.info(f"[LOADING] {device} | reward dialog title detected: {raw.strip()[:60]!r}")
    return hit


def _loading_main_bar_visible(device: str, dlog, img) -> bool:
    """
    True when the main-app bottom bar is readable.

    This is the signal that separates "a popup is covering the app" from "we have
    no idea what this screen is". The bar stays visible under most dialogs, so
    seeing it means the game is loaded and only needs the popup dismissed.
    """
    if img is None:
        return False
    try:
        raw = (check_text(device, 820, 1030, 1910, 1080, image=img) or "").lower()
        if not raw:
            raw = (check_text1(device, 820, 1030, 1910, 1080, image=img) or "").lower()
    except Exception:
        return False
    hits = [t for t in _MAIN_BAR_TEXTS if t in raw]
    if len(hits) >= 2:
        dlog.info(f"[LOADING] {device} | main bottom bar visible ({hits}) — "
                  f"game is loaded, screen is a popup over main")
        return True
    return False


def _loading_post_loading_resolve(device: str, dlog, guard) -> str:
    """
    Resolve whatever is on screen once loading has finished.

    Runs the full ordered check — the interstitials first (they can still appear
    late), then the reward popups, then main/map, then the generic
    popup-over-main fallback. Returns SIG_SUCCESS once target app main is
    confirmed, a SIG_* signal, or "unresolved".
    """
    phase = "post_loading"
    _slog(dlog, device, "Loading", phase,
          "loading finished — running ordered post-loading checks")

    for attempt in range(1, 9):
        if _stop_requested():
            return SIG_MANUAL_STOP
        chk = target_app_guard_checkpoint(device, dlog, guard, phase=phase, in_loading=True)
        if chk != "ok":
            return chk

        img = get_screenshot(device)
        if guard is not None:
            try:
                guard.report_screenshot(img is None)
            except Exception:
                pass
        if img is None:
            time.sleep(1.0)
            continue

        # 1. Interstitials can still show up after loading ends.
        for pg in ("loading_warning", "loading_warning1", "google_signin",
                   "connection issue"):
            try:
                if is_on_page(device, pg, image=img):
                    _slog(dlog, device, "Loading", phase,
                          "interstitial appeared after loading", page=pg,
                          attempt=f"{attempt}/8")
                    return f"dispatch:{pg}"
            except Exception:
                continue

        # 2. Known reward popups.
        closed = False
        for pg in POST_LOADING_POPUPS:
            try:
                if is_on_page(device, pg, image=img):
                    _slog(dlog, device, "Loading", phase, "post-loading popup detected",
                          page=pg, attempt=f"{attempt}/8")
                    _loading_popup_close(device, dlog, guard, pg)
                    closed = True
                    break
            except Exception:
                continue
        if closed:
            continue

        # 3. Reward dialog by title, for reskins the fingerprints miss.
        if _loading_reward_title_visible(device, dlog, img):
            _slog(dlog, device, "Loading", phase,
                  "reward dialog matched by title text — closing",
                  attempt=f"{attempt}/8")
            if not _loading_popup_close(device, dlog, guard, "login reward"):
                try:
                    press_back(device)
                    time.sleep(1.0)
                except Exception:
                    pass
            continue

        # 4. Already home?
        for pg in ("target app main", "game main map"):
            try:
                if is_on_page(device, pg, image=img):
                    _slog(dlog, device, "Loading", phase, "main page confirmed",
                          page=pg, attempt=f"{attempt}/8")
                    if pg == "target app main":
                        _mark_page_seen(device, "target app main")
                        if guard is not None:
                            guard.set_main_page_seen()
                        return SIG_SUCCESS
                    if _back_to_main(device, dlog, guard):
                        _mark_page_seen(device, "target app main")
                        if guard is not None:
                            guard.set_main_page_seen()
                        return SIG_SUCCESS
            except Exception:
                continue

        # 5. Generic popup over main — bottom bar readable but app didn't match.
        if _loading_main_bar_visible(device, dlog, img):
            _slog(dlog, device, "Loading", phase,
                  "popup over main (bottom bar visible) — navigating back",
                  attempt=f"{attempt}/8")
            if _back_to_main(device, dlog, guard):
                _mark_page_seen(device, "target app main")
                if guard is not None:
                    guard.set_main_page_seen()
                return SIG_SUCCESS
            continue

        # 6. Nothing recognised this pass — let back_to_main try.
        _slog(dlog, device, "Loading", phase,
              "screen not recognised — trying back_to_main", attempt=f"{attempt}/8")
        if _back_to_main(device, dlog, guard):
            _mark_page_seen(device, "target app main")
            if guard is not None:
                guard.set_main_page_seen()
            return SIG_SUCCESS
        time.sleep(1.5)

    _slog(dlog, device, "Loading", phase,
          "post-loading checks exhausted without reaching main screen")
    try:
        # `img` is the last frame we already captured — no extra screenshot.
        record_unexpected_page(
            device, dlog, image=img, source_fn="_loading_post_loading_resolve",
            context="post_loading", page_guess="post_loading_unresolved",
            issue_code="post_loading_unresolved", capture_if_missing=False)
    except Exception:
        pass
    return "unresolved"


def _loading_initial_window(device: str, dlog, guard) -> tuple:
    """
    Wait up to 30s for ANY valid page after open_target_app, exiting the moment one
    appears rather than burning the whole window.

    Returns (page_name_or_signal, elapsed).
    """
    phase = "initial_window"
    t0    = time.time()
    _slog(dlog, device, "Loading", phase,
          "waiting for a valid page after open_target_app",
          window=f"{LOADING_INITIAL_WINDOW:.0f}s")

    while time.time() - t0 < LOADING_INITIAL_WINDOW:
        chk = target_app_guard_checkpoint(device, dlog, guard, phase=phase, in_loading=True)
        if chk != "ok":
            return (chk, time.time() - t0)

        page, _img, _full = _loading_detect_page(device, dlog, guard)
        if page not in ("unknown", "no_screenshot"):
            _slog(dlog, device, "Loading", phase, "valid page appeared — exiting early",
                  page=page, elapsed=time.time() - t0)
            return (page, time.time() - t0)
        time.sleep(1.0)

    _slog(dlog, device, "Loading", phase,
          "no valid page within window — trying back_to_main",
          elapsed=time.time() - t0)
    return ("timeout", time.time() - t0)


def Loading(device: str, dlog=None, guard=None) -> str:
    """
    Own the entire TargetApp loading flow, from "TargetApp just opened" to "standing on
    target app main".

    Dispatch loop over the pages that can legitimately appear:

        loading / loading after update -> watch percent
        loading_warning  / loading_warning1 -> click "switch"  (max 3)
        google_signin                       -> click "sign up" (max 3, 15s lockout)
        connection issue                    -> fix network, click OK, keep loading
        main_ark / popup_over_main          -> back_to_main, done

    Returns a SIG_* signal.
    """
    if dlog is None:
        dlog = _get_device_logger(device)
    if guard is None:
        guard = _target_app_guards.get(device)

    t_start = time.time()
    dlog.info("=" * 70)
    _slog(dlog, device, "Loading", "start", "loading flow begin",
          counters=_counters_snapshot(device))
    print(f"[{device}] Loading: watching for game load")

    page, elapsed = _loading_initial_window(device, dlog, guard)
    if page in _ALL_SIGNALS:
        return page

    if page == "timeout":
        # Nothing recognisable in 30s. The game may already be up behind an
        # unmapped screen — run the post-loading resolver first, since it knows
        # about the reward popups; fall back to back_to_main.
        out = _loading_post_loading_resolve(device, dlog, guard)
        if out in _ALL_SIGNALS:
            return out
        if _back_to_main(device, dlog, guard):
            _slog(dlog, device, "Loading", "initial_window",
                  "back_to_main reached main screen after silent window",
                  elapsed=time.time() - t_start, signal=SIG_SUCCESS)
            _mark_page_seen(device, "target app main")
            if guard is not None:
                guard.set_main_page_seen()
            return SIG_SUCCESS
        _slog(dlog, device, "Loading", "initial_window",
              "back_to_main failed — treating as stuck loading")
        return _loading_stuck_escalate(device, dlog, guard)

    # _loading_initial_window has just classified this exact screen and returned
    # a valid page. Re-classifying it immediately meant a second complete sweep
    # of the same frame — six is_on_page evaluations, each with OCR — for an
    # answer we already had, and a staler one at that. Carry it into the first
    # dispatch pass instead.
    #
    # `img` is not carried across: initial_window never returns "unknown", and
    # img is only read on the unknown branch (both helpers there return False on
    # None anyway). Every handler re-confirms its page before it taps.
    pending_page = page

    # ── main dispatch loop ────────────────────────────────────────────────
    while time.time() - t_start < _LOADING_TOTAL_BUDGET:
        if _stop_requested():
            return SIG_MANUAL_STOP

        chk = target_app_guard_checkpoint(device, dlog, guard, phase="dispatch", in_loading=True)
        if chk != "ok":
            return chk

        if pending_page:
            page, img = pending_page, None
            pending_page = ""
            _slog(dlog, device, "Loading", "dispatch", "page classified",
                  page=page, elapsed=time.time() - t_start,
                  source="initial_window (reused, no re-classification)")
        else:
            page, img, _full = _loading_detect_page(device, dlog, guard)
            _slog(dlog, device, "Loading", "dispatch", "page classified",
                  page=page, elapsed=time.time() - t_start, source="sweep")

        if page == "no_screenshot":
            time.sleep(1.0)
            continue

        # ── the two account warnings ──────────────────────────────────────
        if page in ("loading_warning", "loading_warning1"):
            res = _loading_handle_warning(device, dlog, guard, page)
            if res in _ALL_SIGNALS:
                return res
            continue

        # ── Google Play sign-in ───────────────────────────────────────────
        if page == "google_signin":
            res = _loading_handle_google_signin(device, dlog, guard)
            if res in _ALL_SIGNALS:
                return res
            continue

        # ── in-game network popup ─────────────────────────────────────────
        if page == "connection issue":
            res = _loading_handle_connection_issue(device, dlog, guard)
            if res in _ALL_SIGNALS:
                return res
            continue

        # ── actual loading screen ─────────────────────────────────────────
        if page in ("loading", "loading after update"):
            res = _loading_watch_percent(device, dlog, guard)
            if res in _ALL_SIGNALS:
                return res
            if res == "loading_stuck":
                return _loading_stuck_escalate(device, dlog, guard)

            if res in ("loading_done", "post_loading_ready"):
                # Loading is over. Resolve whatever is on screen — reward popups
                # included — rather than assuming back_to_main can cope alone.
                out = _loading_post_loading_resolve(device, dlog, guard)
                if out in _ALL_SIGNALS:
                    return out
                if isinstance(out, str) and out.startswith("dispatch:"):
                    # A late interstitial: let the main loop handle it.
                    continue
                _slog(dlog, device, "Loading", "finish",
                      "post-loading resolution could not reach main screen",
                      result=out)
                return _loading_stuck_escalate(device, dlog, guard)
            continue

        # ── already on the app, or a popup over it ────────────────────────
        if page in ("main_ark", "popup_over_main"):
            _slog(dlog, device, "Loading", "finish",
                  "main/popup detected — resolving post-loading state", page=page)
            out = _loading_post_loading_resolve(device, dlog, guard)
            if out in _ALL_SIGNALS:
                return out
            if isinstance(out, str) and out.startswith("dispatch:"):
                continue
            _slog(dlog, device, "Loading", "finish",
                  "post-loading resolution failed", result=out)
            return _loading_stuck_escalate(device, dlog, guard)

        # ── unrecognised ──────────────────────────────────────────────────
        # Before treating an unknown screen as a loop, check whether the game is
        # simply loaded with something on top of it. This is what kept the Daily
        # Rewards popup spinning as "unknown" for minutes.
        if _loading_main_bar_visible(device, dlog, img) or \
                _loading_reward_title_visible(device, dlog, img):
            _slog(dlog, device, "Loading", "dispatch",
                  "unknown screen but game is loaded underneath — "
                  "running post-loading resolution")
            out = _loading_post_loading_resolve(device, dlog, guard)
            if out in _ALL_SIGNALS:
                return out
            if isinstance(out, str) and out.startswith("dispatch:"):
                continue
        time.sleep(1.5)

    _slog(dlog, device, "Loading", "end", "Loading budget exceeded",
          elapsed=time.time() - t_start)
    append_issue(device, "loading_stuck_failed",
                 f"no resolution within {_LOADING_TOTAL_BUDGET:.0f}s",
                 fn="Loading", phase="end")
    return SIG_FAIL_DEVICE


# ── setup_target_app ────────────────────────────────────────────────────────────────

def setup_target_app(device: str) -> str:
    """
    Phase 3 of prepare_target_app: get Target Application running and loaded.

    Thin by design — install, version and APK checks all live in setup_device
    now, so the only responsibilities here are arming TargetAppGuard, launching the
    game, and handing over to Loading().

    On success the guard is deliberately LEFT RUNNING: runtime tasks rely on
    _target_app_guards[device] being live once setup completes.

    Returns a SIG_* signal.
    """
    dlog = _get_device_logger(device)
    t0   = time.time()

    dlog.info("=" * 70)
    _slog(dlog, device, "setup_target_app", "start", "PHASE 3 begin",
          counters=_counters_snapshot(device))
    print(f"[{device}] setup_target_app: starting")

    guard = _target_app_guards.get(device)
    if guard is None or not guard.is_alive():
        guard = TargetAppGuard(device, dlog)
        guard.start()
    else:
        _target_app_guard_rearm(guard, 1)
    guard.set_stage(1)

    try:
        for cycle in range(1, 4):
            if _stop_requested():
                return SIG_MANUAL_STOP

            _slog(dlog, device, "setup_target_app", "cycle", "launch cycle begin",
                  attempt=f"{cycle}/3")

            # ── open_target_app, up to CAP_OPEN_TARGET_APP_ATTEMPTS across the phase ────
            foreground = False
            while _ctr_get(_open_target_app_attempts, device) < CAP_OPEN_TARGET_APP_ATTEMPTS:
                chk = target_app_guard_checkpoint(device, dlog, guard, phase="open_target_app")
                if chk != "ok":
                    if chk in _ALL_SIGNALS and chk != "ok":
                        return chk

                used = _ctr_inc(_open_target_app_attempts, device, dlog, "open_target_app")
                t_open = time.time()
                try:
                    launched = bool(open_target_app(device, context="setup_target_app"))
                except Exception as exc:
                    dlog.error(f"[SETUP] {device} | open_target_app raised: {exc!r}")
                    launched = False

                _slog(dlog, device, "setup_target_app", "open_target_app", "launch attempt",
                      attempt=f"{used}/{CAP_OPEN_TARGET_APP_ATTEMPTS}",
                      result="sent" if launched else "failed",
                      elapsed=time.time() - t_open)

                if launched and _wait_for_target_app_foreground(device, dlog, timeout=30.0):
                    foreground = True
                    break
                random_delay(1.5, 2.5)

            if not foreground:
                _slog(dlog, device, "setup_target_app", "open_target_app",
                      "TargetApp never reached the foreground — program reopen",
                      attempt=f"{_ctr_get(_open_target_app_attempts, device)}"
                              f"/{CAP_OPEN_TARGET_APP_ATTEMPTS}")
                append_issue(device, "setup_target_app_failed",
                             f"open_target_app failed {CAP_OPEN_TARGET_APP_ATTEMPTS} times",
                             fn="setup_target_app", phase="open_target_app")
                sig = program_reopen_device(device, dlog, reason="open_target_app_failed",
                                            phase="open_target_app", fn="setup_target_app")
                _slog(dlog, device, "setup_target_app", "end", "PHASE 3 aborted",
                      elapsed=time.time() - t0, signal=sig)
                return sig

            # TargetApp is up — enable the TargetApp-specific guard checks and load.
            guard.set_target_app_opened()
            guard.set_stage(3)
            _slog(dlog, device, "setup_target_app", "open_target_app",
                  "TargetApp foreground confirmed — handing over to Loading()")

            sig = _sig_or_stop(Loading(device, dlog, guard))

            if sig == SIG_RESTART_SETUP_TARGET_APP:
                # Loading escalation already did the app-level work (nothing,
                # force-stop, or reinstall).  Re-arm and relaunch.
                _slog(dlog, device, "setup_target_app", "cycle",
                      "Loading asked for a relaunch", attempt=f"{cycle}/3")
                _open_target_app_attempts.pop(device, None)   # fresh launch budget
                _target_app_guard_rearm(guard, 1)
                continue

            if sig == SIG_SUCCESS:
                update_status(device, "TargetApp", "Setup Complete")
                _slog(dlog, device, "setup_target_app", "end", "PHASE 3 complete",
                      elapsed=time.time() - t0, signal=sig,
                      counters=_counters_snapshot(device))
                print(f"[{device}] setup_target_app: done ({time.time() - t0:.1f}s)")
                return sig

            _slog(dlog, device, "setup_target_app", "end", "PHASE 3 failed",
                  elapsed=time.time() - t0, signal=sig)
            return sig

        _slog(dlog, device, "setup_target_app", "end", "launch cycles exhausted",
              elapsed=time.time() - t0, signal=SIG_RESTART_BEFORE_TARGET_APP)
        append_issue(device, "setup_target_app_failed", "3 launch cycles without success",
                     fn="setup_target_app", phase="cycle")
        return SIG_RESTART_BEFORE_TARGET_APP

    except FatalAPKError:
        raise
    except Exception:
        dlog.exception("setup_target_app() unhandled exception")
        append_issue(device, "setup_target_app_failed", "unhandled exception",
                     fn="setup_target_app", phase="exception")
        try:
            if _target_app_guards.get(device) is guard:
                _target_app_guards.pop(device, None)
            guard.stop()
        except Exception:
            pass
        return SIG_FAIL_DEVICE
    # NOTE: on success the guard is intentionally left running for runtime tasks.
    # NOTE: guard is NOT stopped on success — stays alive for dailies


# ── task status ───────────────────────────────────────────────────────────────
# One entry per live task. VIP Collect is idempotent — an interrupted run simply
# re-reads the button and sees "Sold Out" — so it needs no substatus bookkeeping.
_vip_collect_status: dict = {}   # device_id -> "done" or ""

# Tutorial has no sheet column yet (TASK_DEFS["tutorial"]["header"] is None), so
# this dict only tracks "already done this process lifetime" in memory — it is
# not persisted to/loaded from the sheet the way _vip_collect_status is. Once a
# sheet column exists, mirror the vip_collect load/save wiring below for it too.
_tutorial_status: dict = {}      # device_id -> "done" or ""

# Not task state: setup and the controller both use these.
_device_type_map:  dict = {}   # device_id   -> device_type
_device_friendly:  dict = {}   # device_id   -> friendly name

EVENT_LIST_RECT = (355, 123, 730, 980)   # shared event panel list scroll area


def _get_page_button_rect(page_name: str, button_name: str):
    """
    Look up a button's bounding rect from pages.json.
    Returns (x1, y1, x2, y2) as a tuple.
    Raises RuntimeError if page or button not found — check pages.json spelling.
    """
    pages = load_pages_config()
    page  = pages.get(page_name)
    if not page:
        raise RuntimeError(
            f"_get_page_button_rect: page '{page_name}' not in pages.json — check pages.json"
        )
    for btn in page.get("buttons", []):
        if btn.get("name", "").lower() == button_name.lower():
            rect = btn.get("rect")
            if rect and len(rect) == 4:
                return tuple(rect)
            x, y, w, h = btn.get("x"), btn.get("y"), btn.get("w"), btn.get("h")
            if all(v is not None for v in (x, y, w, h)):
                return (x, y, x + w, y + h)
    raise RuntimeError(
        f"_get_page_button_rect: button '{button_name}' not found in page '{page_name}' — check pages.json"
    )

def _get_page_text_rect(page_name: str, text_name: str):
    """
    Look up a text region's bounding rect from pages.json.
    Returns (x1, y1, x2, y2). Raises RuntimeError if not found.
    """
    pages = load_pages_config()
    page  = pages.get(page_name)
    if not page:
        raise RuntimeError(f"_get_page_text_rect: page '{page_name}' not found")
    for t in page.get("texts", []):
        if t.get("name", "").lower() == text_name.lower():
            rect = t.get("rect")
            if rect and len(rect) == 4:
                return tuple(rect)
            x, y, w, h = t.get("x"), t.get("y"), t.get("w"), t.get("h")
            if all(v is not None for v in (x, y, w, h)):
                return (x, y, x + w, y + h)
    raise RuntimeError(f"_get_page_text_rect: text '{text_name}' not found in page '{page_name}'")


SPEEDUP_CACHE_FILE = "speedup_cache.json"

def _gc(device, dlog, guard) -> "str | None":
    """
    Synchronous guard check.  Detects problems and repairs them inline.

    Returns None      — device is stable / was repaired; task continues.
    Returns "restart" — recovery fully failed; task should restart from top.

    All existing callers continue to work unchanged:
        g = _gc(device, dlog, guard)
        if g is not None:
            return g
    """
    if dlog is None:
        dlog = _get_device_logger(device)
    ok = guard_check_and_recover(device, dlog, guard, context="_gc")
    if ok:
        return None
    return "restart"


# ==============================================================================
# GUARD SYNC — SYNCHRONOUS DETECT + FIX SYSTEM
# ==============================================================================

class GuardRecoveryFailed(Exception):
    """
    Raised by click_in_bounding_box when guard_check_and_recover() determines
    the device cannot be recovered.  The controller's except-block catches this
    and handles it like any ADB-level exception (wait → prepare_target_app → retry).
    """


# ── Per-device recovery lock (RLock — reentrant so prepare_target_app can click) ──────

_GUARD_RECOVERY_LOCKS: dict = {}
_GRL_MUTEX = _threading.Lock()

def _guard_recovery_lock(device: str) -> _threading.RLock:
    """Return (creating if needed) the per-device reentrant recovery lock."""
    with _GRL_MUTEX:
        if device not in _GUARD_RECOVERY_LOCKS:
            _GUARD_RECOVERY_LOCKS[device] = _threading.RLock()
        return _GUARD_RECOVERY_LOCKS[device]


# ── Per-thread re-entry depth tracker ─────────────────────────────────────────
# Tracks how deeply guard_check_and_recover is nested for the current thread.
# Prevents redundant full-recovery cycles when guard_check_and_recover is
# re-entered from within prepare_target_app / setup_vpn / setup_target_app.

_guard_tls = _threading.local()

# Per-thread stop-event storage: set in device_worker so that long unbounded
# wait loops inside guard helpers can exit cleanly when stop is requested.
_thread_local = _threading.local()

def _stop_requested() -> bool:
    """
    Safe helper that returns True if the per-thread stop event has been set.
    Used inside unbounded wait loops (_guard_verify_offline, Scenario C,
    _vpn_change_health_check) so they exit cleanly on controller stop.
    """
    try:
        ev = getattr(_thread_local, "stop_event", None)
        return bool(ev and ev.is_set())
    except Exception:
        return False


def _guard_get_depth(device: str) -> int:
    depths = getattr(_guard_tls, "depths", {})
    return depths.get(device, 0)

def _guard_inc_depth(device: str) -> int:
    if not hasattr(_guard_tls, "depths"):
        _guard_tls.depths = {}
    _guard_tls.depths[device] = _guard_tls.depths.get(device, 0) + 1
    return _guard_tls.depths[device]

def _guard_dec_depth(device: str) -> None:
    if hasattr(_guard_tls, "depths"):
        d = _guard_tls.depths.get(device, 1) - 1
        _guard_tls.depths[device] = max(0, d)


# ── Structured recovery logger ─────────────────────────────────────────────────

def _log_guard_result(
    device:      str,
    dlog,
    ctx:         str,
    issue:       str,
    t_detect:    float,
    t_fix_start: float,
    success:     bool,
    extra_note:  str = "",
) -> None:
    """Emit one richly-structured [GUARD-RECOVERY] log line."""
    t_now         = time.time()
    detection_lat = t_fix_start - t_detect
    recovery_dur  = t_now - t_fix_start
    adb_state     = "online" if _adb_ping(device) else "OFFLINE"
    vpn_state     = "up"     if vpn_activity(device) else "DOWN"
    activity      = _get_current_activity(device).strip()
    dlog.info(
        f"[GUARD-RECOVERY] device={device!r} "
        f"ctx={ctx!r} "
        f"issue={issue!r} "
        f"detection_latency={detection_lat:.3f}s "
        f"recovery_duration={recovery_dur:.3f}s "
        f"final_adb={adb_state} "
        f"final_vpn={vpn_state} "
        f"final_activity={activity!r} "
        f"success={success} "
        + (f"note={extra_note!r}" if extra_note else "")
    )
    print(
        f"[GUARD-RECOVERY] {device} | {issue} | "
        f"{'OK' if success else 'FAILED'} | "
        f"detect={detection_lat:.2f}s recover={recovery_dur:.2f}s | "
        f"adb={adb_state} vpn={vpn_state}"
    )


# ── guard_check_and_recover ────────────────────────────────────────────────────

def guard_check_and_recover(
    device:      str,
    dlog=None,
    guard=None,
    context:     str  = "",
    require_target_app: bool = True,
) -> bool:
    """
    Central synchronous guard: detect problems AND fix them in the calling
    (main / task) thread before returning.

    Architecture
    ────────────
    • Uses a per-device RLock so concurrent calls on the SAME device queue up.
      RLock is reentrant so prepare_target_app → setup_target_app → click_in_bounding_box
      → guard_check_and_recover can re-enter without deadlock.
    • A thread-local depth counter short-circuits nested calls that happen
      inside prepare_target_app / setup_target_app to avoid infinite recovery loops.
    • Always reads the live guard from _target_app_guards[device], ignoring stale
      guard references (handles the case where prepare_target_app created a fresh one).

    Checks (in order)
    ─────────────────
    1. Consume pending TargetAppGuard result (clears interrupt event).
    2. ADB online — reconnect / relaunch emulator if needed.
    3. VPN tunnel  — setup_vpn() + open_target_app() if needed.
    4. TargetApp foreground — open_target_app() if needed.
    5. Connection issue popup — _handle_connection_issue() inline.
    6. Unexpected non-TargetApp activity — press Back or reopen TargetApp.
    7. Restart TargetAppGuard thread if it stopped after signalling.

    Returns True  — device is stable, task may continue.
    Returns False — unrecoverable; caller should raise GuardRecoveryFailed
                    or return "restart".
    """
    t_call = time.time()

    if dlog is None:
        dlog = _get_device_logger(device)
    # Always prefer the live guard from the global registry
    live_guard = _target_app_guards.get(device) or guard

    depth = _guard_inc_depth(device)
    try:
        if depth > 1:
            # Nested call from within prepare_target_app / setup_target_app / setup_vpn.
            # Do minimal ADB check only; outer call handles full recovery.
            if not _adb_ping(device):
                dlog.warning(
                    f"[GUARD-SYNC] [{device}] [{context}] "
                    f"ADB offline (nested depth={depth}) — outer recovery will handle"
                )
                return False
            return True

        lock     = _guard_recovery_lock(device)
        acquired = lock.acquire(blocking=True, timeout=120.0)
        if not acquired:
            dlog.warning(
                f"[GUARD-SYNC] [{device}] [{context}] "
                f"Lock acquire timed out (120s) — optimistic continue"
            )
            return True

        try:
            return _guard_check_and_recover_locked(
                device, dlog, live_guard, context, require_target_app, t_call
            )
        finally:
            lock.release()
    finally:
        _guard_dec_depth(device)


def _guard_check_and_recover_locked(
    device:      str,
    dlog,
    live_guard,
    context:     str,
    require_target_app: bool,
    t_call:      float,
) -> bool:
    """
    Synchronous guard recovery — runs inside the per-device lock.
    Implements the exact scenario rules:

      Scenario A  — TargetApp not foreground / TargetApp closed
      Scenario B  — VPN down / internet down / connection issue page
      Scenario C  — ADB disconnect (emulator still alive)
      Scenario D  — Emulator confirmed closed
    """
    ctx = f"[GUARD-SYNC] [{device}] [{context or 'check'}]"

    # ── Step 0: Consume pending TargetAppGuard result ───────────────────────────────
    pending_issue = None
    if live_guard is not None:
        result = live_guard.check()
        if result[0] != "ok":
            pending_issue = result[0]
            dlog.info(f"{ctx} Pending guard result: {result}")
            live_guard.clear_result()
            _guard_interrupt_clear(device)

    # ─────────────────────────────────────────────────────────────────────────
    # SCENARIO C / D — ADB offline
    # ─────────────────────────────────────────────────────────────────────────
    if not _adb_ping(device):
        dlog.warning(f"{ctx} ADB offline — checking emulator process")
        t_fix = time.time()

        # Emulator alive + ADB lost: KEEP reconnecting until ADB returns or
        # netstat confirms the emulator closed. No fixed timeout — a VPN
        # tunnel change can drop ADB for longer than any short cap, and
        # failing on the cap caused false device-offline outcomes.
        emulator_dead = not is_emulator_process_alive(device)
        if not emulator_dead:
            dlog.info(f"{ctx} [Scenario C] ADB lost but emulator alive — waiting")
            print(f"[GUARD-RECOVERY][{device}] Scenario C: ADB lost but emulator alive — waiting")

        t_confirm = time.time()
        last_log  = t_confirm
        while not emulator_dead:
            if _stop_requested():
                dlog.info(
                    f"{ctx} [Scenario C] stop requested while waiting for ADB — exiting"
                )
                print(f"[GUARD-RECOVERY][{device}] Scenario C: stop requested — exiting")
                _log_guard_result(device, dlog, context, "adb_wait_stopped", t_call, t_fix, False)
                return False

            _adb_connect_quiet(device)
            time.sleep(1.0)
            if _adb_ping(device):
                elapsed = time.time() - t_confirm
                dlog.info(
                    f"{ctx} [Scenario C] ADB reconnected after {elapsed:.1f}s "
                    f"(emulator alive) ✓"
                )
                _log_guard_result(device, dlog, context, "adb_reconnect_ok", t_call, t_fix, True)
                break

            if not is_emulator_process_alive(device):
                emulator_dead = True
                break

            now = time.time()
            if now - last_log >= 10.0:
                dlog.info(
                    f"{ctx} [Scenario C] still waiting for ADB, "
                    f"elapsed={now - t_confirm:.0f}s"
                )
                last_log = now

        if not _adb_ping(device):
            if emulator_dead:
                # ── Scenario D: Emulator confirmed closed ─────────────────────
                reopen_count = _device_reopen_count.get(device, 0) + 1
                _device_reopen_count[device] = reopen_count
                dlog.warning(
                    f"{ctx} [Scenario D] Emulator confirmed dead "
                    f"(reopen #{reopen_count}/5)"
                )
                print(f"[GUARD-RECOVERY][{device}] Scenario D: emulator dead reopen #{reopen_count}")

                if reopen_count > 5:
                    dlog.error(f"{ctx} [Scenario D] Emulator closed >5 times — FAILING device")
                    _log_guard_result(device, dlog, context, "emulator_closed_too_many", t_call, t_fix, False)
                    return False

                _launch_device_for_worker(device)

                reconnected = False
                t_launch = time.time()
                while time.time() - t_launch < 90.0:
                    _adb_connect_quiet(device)
                    time.sleep(2.0)
                    if _adb_ping(device):
                        reconnected = True
                        break
                    dlog.debug(f"{ctx} [{time.time()-t_launch:.0f}s] waiting for ADB after relaunch")

                if not reconnected:
                    dlog.error(f"{ctx} [Scenario D] ADB still offline 90s after relaunch")
                    _log_guard_result(device, dlog, context, "emulator_relaunch_adb_timeout", t_call, t_fix, False)
                    return False

                dlog.info(f"{ctx} [Scenario D] ADB restored ✓ — handing setup back to the top level")

                # prepare_target_app() is deliberately NOT called here.
                #
                # This function can be reached from deep inside a task (tap ->
                # guard_fix_if_signalled -> guard_check_and_recover), so calling
                # prepare_target_app() from this point would nest a full setup inside a
                # half-finished task and, on repeated recoveries, stack setups on
                # top of each other.  prepare_target_app() must stay a top-level call.
                #
                # Returning False propagates as GuardRecoveryFailed / "full_restart",
                # and BOTH top-level handlers already re-run setup properly:
                #   * device_worker's task loop  -> prepare_target_app(force_stop_first=True)
                #   * controller _run_one        -> prepare_target_app(force_stop_first=True)
                if require_target_app:
                    reset_transient_recovery_state(device)
                    dlog.info(
                        f"{ctx} [Scenario D] transient state cleared — top-level "
                        f"caller will run prepare_target_app(force_stop_first=True)"
                    )

                _last_guard_recovery_reason[device] = "device_closed_recovered"
                dlog.warning(
                    f"{ctx} [Scenario D] Emulator relaunched — returning False to "
                    f"trigger a top-level setup restart (not continuing mid-step)"
                )
                _log_guard_result(device, dlog, context, "emulator_relaunched_restart", t_call, t_fix, False)
                return False

            # NOTE: there is no "Scenario C UNRECOVERABLE" or "transient" fallback.
            # The while loop above only exits via:
            #   a) ADB restored (break) → _adb_ping is True → outer if skipped
            #   b) emulator_dead=True   → Scenario D path above
            #   c) stop requested       → return False already executed
            # Reaching here means ADB was broken but emulator is alive and
            # stop was not requested — this is a logic error; fail safely.
            dlog.warning(
                f"{ctx} [Scenario C] reached end-of-block without ADB and "
                f"without confirmed close — returning False (unexpected exit)"
            )
            _log_guard_result(device, dlog, context, "adb_unexpected_exit", t_call, t_fix, False)
            return False

    # ─────────────────────────────────────────────────────────────────────────
    # SCENARIO B — VPN / internet / connection issue
    # ─────────────────────────────────────────────────────────────────────────
    if require_target_app and not vpn_activity(device):
        t_fix = time.time()
        now   = time.time()

        # Track VPN down events (rolling 60s window)
        vpn_ts = _vpn_down_timestamps.setdefault(device, [])
        vpn_ts.append(now)
        _vpn_down_timestamps[device] = [t for t in vpn_ts if now - t <= 60.0]
        vpn_down_count = len(_vpn_down_timestamps[device])

        dlog.warning(
            f"{ctx} [Scenario B] VPN tunnel DOWN "
            f"(#{vpn_down_count} in last 60s)"
        )
        print(f"[GUARD-RECOVERY][{device}] Scenario B: VPN down #{vpn_down_count}")

        # B1: 3-second grace — check internet during grace
        t_grace = time.time()
        recovered_in_grace = False
        internet_ok = True
        while time.time() - t_grace < 3.0:
            time.sleep(0.5)
            if vpn_activity(device):
                dlog.info(f"{ctx} [B1] VPN recovered within grace ✓")
                recovered_in_grace = True
                break
            internet_ok = internet(device)

        # B1: Frequency check — if VPN went down >3 times in 60s, change server
        # even if it recovered during grace
        if vpn_down_count > 3 and recovered_in_grace:
            dlog.warning(
                f"{ctx} [B1] VPN recovered in grace but down {vpn_down_count}x in 60s "
                f"— changing VPN server proactively (force_change=True)"
            )
            _vpn_down_timestamps[device] = []   # reset counter
            if not _vpn_change_server(device, dlog, force_change=True):
                reason = _last_vpn_change_failure_reason.get(device, "unknown")
                dlog.error(f"{ctx} [B1] Proactive server change failed (reason={reason!r})")
                if reason == "device_closed":
                    dlog.error(f"{ctx} [B1] device_closed during change — Scenario D escalation")
                _log_guard_result(device, dlog, context, "vpn_freq_server_change_failed", t_call, t_fix, False)
                return False
            # Server changed — reopen TargetApp and continue
            if not _ensure_vpn_prepare_target_app(device, dlog, context="B1 freq server change"):
                _log_guard_result(device, dlog, context, "b1_vpn_gate_failed", t_call, t_fix, False)
                return False
            if not open_target_app(device):
                dlog.error(f"{ctx} [B1] open_target_app failed after freq server change")
                _log_guard_result(device, dlog, context, "b1_target_app_open_failed", t_call, t_fix, False)
                return False
            _b1_reached = _wait_for_activity(
                device, TARGET_APP_PACKAGE, timeout=20.0, interval=1.0, dlog=dlog
            )
            if not _b1_reached:
                dlog.error(f"{ctx} [B1] TargetApp activity not confirmed after freq server change")
                _log_guard_result(device, dlog, context, "b1_target_app_activity_timeout", t_call, t_fix, False)
                return False
            _log_guard_result(device, dlog, context, "vpn_server_changed_freq", t_call, t_fix, True)
            return True

        if recovered_in_grace:
            return True

        # B2: Internet check during grace showed internet is down
        if not internet_ok:
            dlog.warning(f"{ctx} [B2] Internet down — entering 40s wait")
            print(f"[GUARD-RECOVERY][{device}] Scenario B2: internet down — 40s wait")
            t_inet = time.time()
            inet_returned = False
            while time.time() - t_inet < 40.0:
                time.sleep(1.0)
                if internet(device):
                    inet_returned = True
                    dlog.info(f"{ctx} [B2] Internet returned after {time.time()-t_inet:.1f}s ✓")
                    break

            if not inet_returned:
                dlog.error(
                    f"{ctx} [B2] Internet still down after 40s — "
                    f"signalling GLOBAL INTERNET DOWN emergency"
                )
                _log_guard_result(device, dlog, context, "internet_down_40s", t_call, t_fix, False)
                # Notify controller via queue (multiprocessing-safe)
                _notify_internet_down(device)
                return False

        # B3: VPN still down after grace — force actual server change
        # force_change=True because VPN was verified down after the 3s grace;
        # we must not accept an already-protected state without clicking Change Server.
        if not vpn_activity(device):
            dlog.warning(f"{ctx} [B3] VPN still down after grace — changing server (force_change=True)")
            print(f"[GUARD-RECOVERY][{device}] Scenario B3: changing VPN server")

            # _vpn_change_server already performs 3 full internal attempts — call once
            if not _vpn_change_server(device, dlog, force_change=True):
                reason = _last_vpn_change_failure_reason.get(device, "unknown")
                dlog.error(f"{ctx} [B3] VPN server change failed (reason={reason!r})")
                if reason == "device_closed":
                    dlog.error(f"{ctx} [B3] device_closed during change — Scenario D escalation")
                    # Scenario D will be handled on next guard cycle (ADB is gone)
                    _log_guard_result(device, dlog, context, "vpn_server_change_exhausted", t_call, t_fix, False)
                    return False
                _log_guard_result(device, dlog, context, "vpn_server_change_exhausted", t_call, t_fix, False)
                return _handle_vpn_recovery_failed_full_restart(
                    device, dlog,
                    reason=f"B3 guard VPN server change failed ({reason})"
                )

            dlog.info(f"{ctx} [B3] VPN server change OK ✓")
            _vpn_down_timestamps[device] = []   # reset counter after server change

        # VPN is back — reopen TargetApp
        if not _ensure_vpn_prepare_target_app(device, dlog, context="Scenario B VPN restored"):
            _log_guard_result(device, dlog, context, "vpn_gate_failed_after_fix", t_call, t_fix, False)
            return False
        if not open_target_app(device):
            dlog.error(f"{ctx} [Scenario B] open_target_app() failed after VPN recovery")
            _log_guard_result(device, dlog, context, "vpn_fixed_target_app_open_failed", t_call, t_fix, False)
            return False

        reached = _wait_for_activity(device, TARGET_APP_PACKAGE, timeout=20.0, interval=1.0, dlog=dlog)
        if not reached:
            dlog.error(f"{ctx} [Scenario B] TargetApp activity not reached after VPN fix")
            _log_guard_result(device, dlog, context, "vpn_fixed_target_app_activity_timeout", t_call, t_fix, False)
            return False

        dlog.info(f"{ctx} [Scenario B] VPN + TargetApp restored ✓")
        _log_guard_result(device, dlog, context, "vpn_fixed", t_call, t_fix, True)

    # ─────────────────────────────────────────────────────────────────────────
    # SCENARIO A — TargetApp not foreground / closed
    # ─────────────────────────────────────────────────────────────────────────
    if require_target_app:
        current = _get_current_activity(device).strip()
        target_app_fg  = TARGET_APP_PACKAGE in current

        if not target_app_fg:
            t_fix = time.time()
            now   = time.time()
            dlog.warning(f"{ctx} [Scenario A] TargetApp not foreground: {current!r}")
            print(f"[GUARD-RECOVERY][{device}] Scenario A: TargetApp not foreground")

            # Track not-foreground events (rolling 60s)
            fg_ts = _target_app_not_fg_timestamps.setdefault(device, [])
            fg_ts.append(now)
            _target_app_not_fg_timestamps[device] = [t for t in fg_ts if now - t <= 60.0]
            fg_count = len(_target_app_not_fg_timestamps[device])
            dlog.info(f"{ctx} [Scenario A] not-fg count: {fg_count} in last 60s")

            # A: Escalation — >5 times in 60s → reinstall TargetApp
            if fg_count > 5:
                target_app_reinstall_n = _target_app_reinstall_count.get(device, 0)
                if target_app_reinstall_n >= 1:
                    dlog.error(
                        f"{ctx} [Scenario A] TargetApp not-fg {fg_count}x in 60s "
                        f"and reinstall already done — FAILING device"
                    )
                    _log_guard_result(device, dlog, context, "target_app_not_fg_reinstall_exhausted", t_call, t_fix, False)
                    return False

                dlog.warning(
                    f"{ctx} [Scenario A] TargetApp not-fg {fg_count}x in 60s "
                    f"— reinstalling TargetApp (no VPN reinstall)"
                )
                dlog.info(f"{ctx} [FORCE-STOP] TargetApp force-stop before reinstall (escalation path)")
                _target_app_reinstall_count[device] = 1
                _target_app_not_fg_timestamps[device] = []
                uninstall_ark(device)
                install_target_app(device)
                # Fall through to Scenario A open_target_app below

            # Step 1: direct open_target_app (NO force-stop first — Scenario A rule)
            dlog.info(f"{ctx} [Scenario A Step 1] open_target_app() direct — no force-stop")
            if not _ensure_vpn_prepare_target_app(device, dlog, context="Scenario A Step 1"):
                _log_guard_result(device, dlog, context, "vpn_gate_failed_scenario_a", t_call, t_fix, False)
                return False
            if not open_target_app(device):
                dlog.warning(f"{ctx} [Scenario A] open_target_app() returned False — waiting anyway")

            reached = _wait_for_activity(
                device, TARGET_APP_PACKAGE, timeout=20.0, interval=1.0, dlog=dlog
            )

            if not reached:
                # Step 2: force-close TargetApp + open again
                dlog.warning(
                    f"{ctx} [Scenario A Step 2] TargetApp not appeared in 20s "
                    f"— force-close + reopen"
                )
                dlog.info(f"{ctx} [FORCE-STOP] TargetApp force-stopped (Scenario A Step 2: direct open failed)")
                _adb_shell(device, "am", "force-stop", TARGET_APP_PACKAGE, timeout=5)
                time.sleep(1.0)
                open_ok = False
                if _ensure_vpn_prepare_target_app(device, dlog, context="Scenario A Step 2"):
                    open_ok = open_target_app(device)
                    if not open_ok:
                        dlog.warning(
                            f"{ctx} [Scenario A Step 2] open_target_app returned False — "
                            f"verifying activity before failing/continuing"
                        )
                else:
                    dlog.error(f"{ctx} [Scenario A Step 2] VPN gate failed — skipping open_target_app")
                reached = _wait_for_activity(
                    device, TARGET_APP_PACKAGE, timeout=20.0, interval=1.0, dlog=dlog
                )
                if reached:
                    dlog.info(f"{ctx} [Scenario A Step 2] TargetApp activity confirmed after force-stop/open")
                else:
                    dlog.error(
                        f"{ctx} [Scenario A Step 2] TargetApp activity not confirmed after force-stop/open "
                        f"(open_ok={open_ok}) — proceeding to Step 3"
                    )

            if not reached:
                # Step 3: uninstall + reinstall (once)
                target_app_reinstall_n = _target_app_reinstall_count.get(device, 0)
                if target_app_reinstall_n >= 1:
                    dlog.error(
                        f"{ctx} [Scenario A Step 3] TargetApp still not running "
                        f"and reinstall already done — FAILING device"
                    )
                    _log_guard_result(device, dlog, context, "target_app_closed_reinstall_exhausted", t_call, t_fix, False)
                    return False

                dlog.warning(f"{ctx} [Scenario A Step 3] force-close + open failed — reinstalling TargetApp")
                dlog.info(f"{ctx} [FORCE-STOP] TargetApp force-stopped before reinstall (Scenario A Step 3)")
                _target_app_reinstall_count[device] = 1
                _adb_shell(device, "am", "force-stop", TARGET_APP_PACKAGE, timeout=5)
                uninstall_ark(device)
                install_target_app(device)
                if not _ensure_vpn_prepare_target_app(device, dlog, context="Scenario A Step 3 reinstall"):
                    _log_guard_result(device, dlog, context, "vpn_gate_failed_scenario_a_reinstall", t_call, t_fix, False)
                    return False
                if not open_target_app(device):
                    dlog.error(f"{ctx} [Scenario A Step 3] open_target_app failed after reinstall")
                    _log_guard_result(device, dlog, context, "target_app_reinstall_open_failed", t_call, t_fix, False)
                    return False
                reached = _wait_for_activity(
                    device, TARGET_APP_PACKAGE, timeout=30.0, interval=1.0, dlog=dlog
                )
                if not reached:
                    dlog.error(f"{ctx} [Scenario A] TargetApp still not running after reinstall — FAILING")
                    _log_guard_result(device, dlog, context, "target_app_reinstall_failed", t_call, t_fix, False)
                    return False

            dlog.info(f"{ctx} [Scenario A] TargetApp foreground confirmed ✓")
            _log_guard_result(device, dlog, context, "target_app_reopened", t_call, t_fix, True)

    # ─────────────────────────────────────────────────────────────────────────
    # SCENARIO B4 — Connection issue popup
    # ─────────────────────────────────────────────────────────────────────────
    if require_target_app:
        try:
            _img_ci = get_screenshot(device, retries=0)
            if _img_ci is not None and is_on_page(device, "connection issue", image=_img_ci):
                t_fix = time.time()
                now   = time.time()
                dlog.warning(f"{ctx} [B4] Connection issue popup detected")
                print(f"[GUARD-RECOVERY][{device}] Scenario B4: connection issue popup")

                # Track frequency
                # ci_vpn_count is recalculated AFTER v2 appends the current event
                # B4: Determine if loading phase — use tracked state + context text
                in_loading = (
                    "loading" in context.lower()
                    or "setup_target_app" in context.lower()
                    or _loading_phase_active.get(device, False)
                    or _last_seen_page.get(device) == "loading"
                )

                # B4: VPN/internet sub-check and OK click
                outcome = _handle_connection_issue_v2(device, dlog, in_loading)

                if outcome["status"] == "failed":
                    dlog.error(f"{ctx} [B4] connection issue handling failed")
                    _log_guard_result(device, dlog, context, "connection_issue_failed", t_call, t_fix, False)
                    return False

                # Recalculate after v2 has appended the current event
                now2 = time.time()
                ci_ts_raw2   = _connection_issue_timestamps.get(device, [])
                ci_ts_typed2 = [(t, ic) for (t, ic) in ci_ts_raw2 if isinstance(t, float) and now2 - t <= 60.0]
                ci_vpn_count = sum(1 for (_, ic) in ci_ts_typed2 if not ic)

                # B4: >5 non-internet CI in 60s → force server change
                if ci_vpn_count > 5:
                    dlog.warning(f"{ctx} [B4] {ci_vpn_count} non-internet connection issues in 60s — changing VPN server (force_change=True)")
                    _connection_issue_timestamps[device] = []
                    if not _vpn_change_server(device, dlog, force_change=True):
                        dlog.error(f"{ctx} [B4] Forced server change failed")
                        _log_guard_result(device, dlog, context, "connection_issue_server_change_failed", t_call, t_fix, False)
                        return False

                    dlog.info(f"{ctx} [B4] Forced server change OK — reopening TargetApp")
                    if not _ensure_vpn_prepare_target_app(device, dlog, context="B4 forced server change"):
                        _log_guard_result(device, dlog, context, "b4_vpn_gate_failed", t_call, t_fix, False)
                        return False
                    if not open_target_app(device):
                        dlog.error(f"{ctx} [B4] open_target_app() failed after forced server change")
                        _log_guard_result(device, dlog, context, "b4_forced_cs_target_app_open_failed", t_call, t_fix, False)
                        return False

                    reached = _wait_for_activity(
                        device, TARGET_APP_PACKAGE,
                        timeout=20.0, interval=1.0, dlog=dlog,
                    )
                    if not reached:
                        dlog.error(f"{ctx} [B4] TargetApp activity not reached after forced server change")
                        _log_guard_result(device, dlog, context, "b4_forced_cs_target_app_timeout", t_call, t_fix, False)
                        return False

                    if in_loading:
                        page = when_on_page(device, ["loading", "target app main"], timeout=30.0)
                    else:
                        page = when_on_page(device, ["target app main"], timeout=30.0)

                    if not page:
                        dlog.error(f"{ctx} [B4] Expected page not reached after forced server change (loading={in_loading})")
                        _log_guard_result(device, dlog, context, "b4_forced_cs_page_timeout", t_call, t_fix, False)
                        return False

                    dlog.info(f"{ctx} [B4] Forced server change + TargetApp restored ✓ (page={page!r})")

                # B4: Loading-only "8 times no reason" (VPN up, internet up, still failing)
                # Use the cause flags from v2 — do NOT re-check VPN/internet here because
                # by this point both will have already recovered. The sticky cause flags
                # reflect what actually caused the connection issue, not the current state.
                lci = _loading_connection_issue_count.get(device, 0)
                if in_loading and not outcome["internet_cause"] and not outcome["vpn_cause"]:
                    # True no-reason event: neither VPN nor internet was ever down
                    lci += 1
                    _loading_connection_issue_count[device] = lci
                    dlog.info(f"{ctx} [B4] No-reason loading connection issues: {lci}/8")

                if in_loading and lci >= 8:
                    target_app_reinstall_n = _target_app_reinstall_count.get(device, 0)
                    if target_app_reinstall_n >= 1:
                        dlog.error(f"{ctx} [B4] 8+ loading connection issues + reinstall done — FAILING")
                        _log_guard_result(device, dlog, context, "loading_ci_reinstall_exhausted", t_call, t_fix, False)
                        return False

                    # lci >= 8 only reached when no VPN/internet cause was recorded,
                    # so we know VPN+internet are healthy — safe to reinstall
                    dlog.warning(
                        f"{ctx} [B4] 8+ no-reason loading connection issues "
                        f"— reinstalling TargetApp"
                    )
                    _target_app_reinstall_count[device] = 1
                    _loading_connection_issue_count[device] = 0

                    ok_uninstall = uninstall_ark(device)
                    if not ok_uninstall:
                        dlog.warning(f"{ctx} [B4] uninstall_ark() returned False — app may already be absent, continuing")

                    ok_install = install_target_app(device)
                    if not ok_install:
                        dlog.error(f"{ctx} [B4] install_target_app() failed — cannot continue TargetApp reinstall")
                        _log_guard_result(device, dlog, context, "loading_ci_reinstall_install_failed", t_call, t_fix, False)
                        return False

                    if not _ensure_vpn_prepare_target_app(device, dlog, context="B4 TargetApp reinstall"):
                        _log_guard_result(device, dlog, context, "b4_reinstall_vpn_gate_failed", t_call, t_fix, False)
                        return False
                    ok_open = open_target_app(device)
                    if not ok_open:
                        dlog.error(f"{ctx} [B4] open_target_app() failed after TargetApp reinstall")
                        _log_guard_result(device, dlog, context, "loading_ci_reinstall_open_failed", t_call, t_fix, False)
                        return False

                    reached = _wait_for_activity(
                        device, TARGET_APP_PACKAGE,
                        timeout=30.0, interval=1.0, dlog=dlog
                    )
                    if not reached:
                        dlog.error(f"{ctx} [B4] TargetApp activity not reached after reinstall")
                        _log_guard_result(device, dlog, context, "loading_ci_reinstall_activity_timeout", t_call, t_fix, False)
                        return False

                    dlog.info(f"{ctx} [B4] TargetApp reinstall complete — TargetApp activity confirmed ✓")

                outcome_status = outcome["status"]
                dlog.info(f"{ctx} [B4] Connection issue resolved ({outcome_status}) ✓")
                _log_guard_result(device, dlog, context, f"connection_issue_{outcome_status}", t_call, t_fix, True)

        except Exception as _ci_ex:
            dlog.warning(f"{ctx} Exception in connection-issue check: {_ci_ex}")

    # ── Unexpected activity ───────────────────────────────────────────────────
    if require_target_app:
        current = _get_current_activity(device).strip()
        _is_known = (
            not current
            or "null" in current.lower()
            or TARGET_APP_PACKAGE in current
            or "HomeActivity" in current
            or "launcher" in current.lower()
            or "ch.protonvpn.android" in current
            or "vpndialogs" in current
            or "MinuteMaidActivity" in current
        )
        if not _is_known:
            t_fix = time.time()
            dlog.warning(f"{ctx} Unexpected activity: {current!r} — pressing Back once")
            _adb_shell(device, "input", "keyevent", "4")
            time.sleep(1.5)
            current2 = _get_current_activity(device).strip()
            if TARGET_APP_PACKAGE not in current2:
                dlog.warning(f"{ctx} Still not in TargetApp after Back ({current2!r}) — open_target_app")
                # VPN gate
                if not _ensure_vpn_prepare_target_app(device, dlog, context="unexpected activity after Back"):
                    dlog.error(f"{ctx} VPN gate failed on unexpected activity recovery")
                    _log_guard_result(device, dlog, context, "unexpected_activity_vpn_gate_failed", t_call, t_fix, False)
                    return False
                # open_target_app
                if not open_target_app(device):
                    dlog.error(f"{ctx} open_target_app returned False on unexpected activity recovery")
                    _log_guard_result(device, dlog, context, "unexpected_activity_target_app_open_failed", t_call, t_fix, False)
                    return False
                # activity confirmation
                _ua_reached = _wait_for_activity(
                    device, TARGET_APP_PACKAGE, timeout=15.0, interval=1.0, dlog=dlog
                )
                if not _ua_reached:
                    dlog.error(f"{ctx} Unexpected activity: TargetApp activity not confirmed after open_target_app")
                    _log_guard_result(device, dlog, context, "unexpected_activity_activity_timeout", t_call, t_fix, False)
                    return False
                dlog.info(f"{ctx} Unexpected activity handled ✓ (TargetApp activity confirmed)")
                _log_guard_result(device, dlog, context, "unexpected_activity", t_call, t_fix, True)
            else:
                dlog.info(f"{ctx} Unexpected activity resolved by Back ✓")
                _log_guard_result(device, dlog, context, "unexpected_activity", t_call, t_fix, True)

    # ── Restart TargetAppGuard if it stopped ───────────────────────────────────────
    _live_g = _target_app_guards.get(device)
    if require_target_app and _live_g is not None and not _live_g._thread.is_alive():
        dlog.info(f"{ctx} TargetAppGuard thread dead — restarting")
        _live_g.clear_result()
        _live_g._stop_event.clear()
        _live_g._thread = _threading.Thread(
            target=_live_g._run, daemon=True, name=f"target_app_guard_{device}"
        )
        _live_g._thread.start()
        dlog.info(f"{ctx} TargetAppGuard restarted ✓")

    elapsed = time.time() - t_call
    if elapsed > 0.05 or pending_issue:
        dlog.debug(f"{ctx} check complete in {elapsed:.3f}s | pending_issue={pending_issue!r}")

    return True


# Global internet-down event — set by guard when internet_down 40s limit hit
# Controller watches this and triggers emergency stop
_GLOBAL_INTERNET_DOWN_EVENT = _threading.Event()

# Per-process queue reference set by device_worker so guard can notify controller
_WORKER_STATUS_Q = None

def _notify_internet_down(device: str) -> None:
    """
    Report a suspected host-internet outage to the controller.

    Now emits "host_internet_pause" rather than the old
    "internet_down_emergency".  The controller responds by holding every device
    in place instead of killing subprocesses and closing emulators — see
    _enter_internet_pause() in controller_ui_v7.py.  The old emergency handler
    still exists there but is reserved for manual Stop, shutdown and hard reset.

    _GLOBAL_INTERNET_DOWN_EVENT is still set for any legacy reader.
    """
    _GLOBAL_INTERNET_DOWN_EVENT.set()
    _notify_host_internet_pause(device, "internet_down_over_40s")


def _host_internet_ok_bot() -> bool:
    """
    Bot-side host/global internet check.
    Uses the PC/host network, NOT the emulator's VPN tunnel.
    Tries Windows ping (TTL=) then Linux/cross-platform ping then HTTPS.

    Call this when internet(device) fails for a single emulator to decide
    whether the failure is:
      - emulator-only / VPN-route failure  → _host_internet_ok_bot() returns True
      - global host internet down          → _host_internet_ok_bot() returns False
    """
    import subprocess as _sub
    # 1. Windows host ping to 8.8.8.8
    try:
        r = _sub.run(
            ["ping", "-n", "1", "-w", "2000", "8.8.8.8"],
            capture_output=True, text=True, timeout=5
        )
        if "TTL=" in (r.stdout or "") or "bytes from" in (r.stdout or ""):
            return True
    except Exception:
        pass
    # 2. Windows host ping to 1.1.1.1 (second independent target)
    try:
        r = _sub.run(
            ["ping", "-n", "1", "-w", "2000", "1.1.1.1"],
            capture_output=True, text=True, timeout=5
        )
        if "TTL=" in (r.stdout or "") or "bytes from" in (r.stdout or ""):
            return True
    except Exception:
        pass
    # 3. HTTPS generate_204 fallback
    try:
        import urllib.request as _ureq
        resp = _ureq.urlopen("https://www.google.com/generate_204", timeout=4)
        if resp.status == 204:
            return True
    except Exception:
        pass
    return False


def _force_reset_vpn_only(device: str, dlog, reason: str = "") -> bool:
    """
    VPN-only reset with real reconnect/recovery flow.

    Used ONLY when:
      - VPN has already been opened/connected (not first-startup)
      - host/global internet is confirmed OK
      - emulator/ADB is alive

    Does NOT force-stop TargetApp.
    Does NOT reopen the emulator.
    Does NOT call setup_vpn() recursively.

    Recovery flow:
      1. Force-stop ch.protonvpn.android only
      2. open_vpn() → wait for RoutingActivity
      3. If tun0/vpn_activity already up → check internet → return
      4. Find and click Connect button
      5. Handle VPN permission dialog
      6. Wait for tun0 (up to 20s)
      7. If still not connected, Change Server once (force_change=True)
         with recursion guard to prevent _vpn_change_server→_force_reset loop
      8. Wait for tun0 again
      9. Recheck internet(device)

    Returns True only when vpn_activity(device) and internet(device) are both True.

    Logs: [VPN-RESET] ...
    """
    dlog.info(f"[VPN-RESET] reason={reason!r}")
    print(f"[VPN-RESET][{device}] reason={reason!r}")

    # Recursion guard: set while active so _vpn_change_server won't call back here
    if _vpn_only_reset_active.get(device):
        dlog.warning("[VPN-RESET] already active for this device — skipping re-entry")
        return False
    _vpn_only_reset_active[device] = True

    try:
        return _force_reset_vpn_only_inner(device, dlog)
    finally:
        _vpn_only_reset_active.pop(device, None)


def _force_reset_vpn_only_inner(device: str, dlog) -> bool:
    """Inner implementation of _force_reset_vpn_only (separated for recursion guard)."""

    # 1. Force-stop ProtonVPN only — do NOT touch TargetApp
    dlog.info("[VPN-RESET] force-stopping ProtonVPN only")
    try:
        subprocess.run(
            ["adb", "-s", device, "shell", "am", "force-stop", "ch.protonvpn.android"],
            capture_output=True, timeout=8
        )
    except Exception as e:
        dlog.warning(f"[VPN-RESET] force-stop error: {e}")

    time.sleep(2.0)

    # 2. Open ProtonVPN
    dlog.info("[VPN-RESET] opening ProtonVPN")
    try:
        open_vpn(device)
    except Exception as e:
        dlog.warning(f"[VPN-RESET] open_vpn error: {e}")
        dlog.info("[VPN-RESET] RoutingActivity reached=False")
        dlog.info("[VPN-RESET] final vpn_activity=False internet=False")
        dlog.info("[VPN-RESET] recovered=False")
        return False

    # 3. Wait for RoutingActivity (up to 10s)
    t_ra = time.time()
    routing_ok = False
    while time.time() - t_ra < 10.0:
        cur = _get_current_activity(device).strip()
        if "RoutingActivity" in cur or "ch.protonvpn.android" in cur:
            routing_ok = True
            break
        time.sleep(1.0)
    dlog.info(f"[VPN-RESET] RoutingActivity reached={routing_ok}")

    # 4. Quick check: did VPN auto-connect?
    if vpn_activity(device):
        dlog.info("[VPN-RESET] current vpn_activity=True")
        inet_ok = internet(device)
        dlog.info(f"[VPN-RESET] final vpn_activity=True internet={inet_ok}")
        dlog.info(f"[VPN-RESET] recovered={inet_ok}")
        return inet_ok
    dlog.info("[VPN-RESET] current vpn_activity=False")

    # 5. Find and click Connect button via UIAutomator
    connect_pos = None
    try:
        connect_pos = _find_vpn_button(device, "Connect")
    except Exception:
        pass

    if connect_pos is not None:
        cx, cy = connect_pos
        dlog.info(f"[VPN-RESET] Connect button found/clicked at ({cx},{cy})")
        try:
            _adb_shell(device, "input", "tap", str(cx), str(cy))
        except Exception as e:
            dlog.warning(f"[VPN-RESET] Connect tap error: {e}")
    else:
        dlog.info("[VPN-RESET] Connect button not found — checking for dialog")

    # 6. Handle VPN permission dialog
    time.sleep(1.5)
    perm_handled = False
    try:
        cur = _get_current_activity(device).strip()
        if "vpndialogs" in cur:
            perm_handled = _vpn_tap_ok_allow(device, dlog)
            dlog.info(f"[VPN-RESET] VPN permission dialog handled={perm_handled}")
        else:
            dlog.info("[VPN-RESET] VPN permission dialog handled=False (not shown)")
    except Exception as e:
        dlog.warning(f"[VPN-RESET] permission dialog check error: {e}")
        dlog.info("[VPN-RESET] VPN permission dialog handled=False")

    # 7. Wait for tun0 (up to 20s)
    t_tun = time.time()
    vpn_ok = False
    while time.time() - t_tun < 20.0:
        if vpn_activity(device):
            vpn_ok = True
            break
        time.sleep(1.5)

    if vpn_ok:
        inet_ok = internet(device)
        dlog.info(f"[VPN-RESET] final vpn_activity=True internet={inet_ok}")
        dlog.info(f"[VPN-RESET] recovered={inet_ok}")
        return inet_ok

    # 8. Change Server fallback (once, with recursion guard already set)
    dlog.info("[VPN-RESET] Change Server fallback start")
    cs_ok = False
    try:
        cs_ok = _vpn_change_server(device, dlog, force_change=True)
    except Exception as e:
        dlog.warning(f"[VPN-RESET] Change Server fallback error: {e}")
    dlog.info(f"[VPN-RESET] Change Server fallback result={cs_ok}")

    # 9. Final check
    vpn_final = vpn_activity(device)
    inet_final = vpn_final and internet(device)
    dlog.info(f"[VPN-RESET] final vpn_activity={vpn_final} internet={inet_final}")
    dlog.info(f"[VPN-RESET] recovered={inet_final}")
    return inet_final


def _ensure_vpn_prepare_target_app(device: str, dlog, context: str) -> bool:
    """
    VPN gate — must be called before every open_target_app() call.

    Hard rule: TargetApp must never be launched unless VPN/tun0 is confirmed connected.
    If VPN is down, attempts recovery via _force_reset_vpn_only.
    If recovery fails, returns False and open_target_app must NOT be called.

    Logs [VPN-GATE] ... on every path.
    """
    if vpn_activity(device):
        dlog.info(f"[VPN-GATE] {context}: VPN confirmed before TargetApp open")
        return True

    dlog.warning(f"[VPN-GATE] {context}: VPN not connected before TargetApp open — recovering")
    try:
        recovered = _force_reset_vpn_only(
            device, dlog, reason=f"VPN gate before TargetApp: {context}"
        )
    except Exception as _e:
        dlog.error(f"[VPN-GATE] {context}: _force_reset_vpn_only raised: {_e}")
        recovered = False

    if recovered and vpn_activity(device):
        dlog.info(f"[VPN-GATE] {context}: VPN restored — TargetApp open allowed")
        return True

    dlog.error(f"[VPN-GATE] {context}: VPN could not be restored — TargetApp open blocked")
    return False


def _handle_vpn_recovery_failed_full_restart(
    device: str,
    dlog,
    reason: str,
) -> bool:
    """
    Called when VPN recovery has genuinely failed (no tun0, no UI connected, all
    internal retries exhausted).

    Rule:
      - This full device restart is allowed exactly ONCE per device per run.
      - If already used, log clearly and return False (device fails).

    Behaviour when restart is allowed:
      1. Log the failure reason.
      2. Increment _vpn_recovery_full_restart_count.
      3. Call _reopen_device_capped() to close and reopen the emulator.
      4. Call _reset_device_state() so the next prepare_target_app starts completely clean.
      5. Return False — the caller must propagate this False up through setup_vpn /
         prepare_target_app so the device_worker BA-RETRY loop restarts prepare_target_app from
         the beginning.  Do NOT continue the current stage.

    Returns False always.  Logs indicate whether the device was reopened or failed.
    """
    dlog.error(f"[VPN-FAIL-RESTART] VPN recovery failed reason={reason!r}")

    _fr = _vpn_recovery_full_restart_count.get(device, 0)
    if _fr >= 1:
        dlog.error(
            f"[VPN-FAIL-RESTART] restart already used — marking device failed "
            f"(count={_fr})"
        )
        append_issue(device, "vpn_recovery_full_restart_failed", str(reason),
                     fn="_handle_vpn_recovery_failed_full_restart",
                     phase="full_restart")
        return False

    _vpn_recovery_full_restart_count[device] = _fr + 1
    dlog.error(
        f"[VPN-FAIL-RESTART] closing/reopening emulator for full prepare_target_app restart "
        f"attempt 1/1 (reason={reason!r})"
    )
    _reopen_device_capped(device, dlog)
    dlog.error("[VPN-FAIL-RESTART] device reopened — restarting full prepare_target_app from beginning")
    _reset_device_state(device)
    # Return False — device_worker BA-RETRY loop will restart prepare_target_app cleanly.
    return False


def _handle_connection_issue_v2(
    device: str, dlog, in_loading: bool = False
) -> dict:
    """
    B4 connection issue handler — checks VPN/internet, clicks OK.
    loading phase is determined by in_loading param OR _loading_phase_active[device].

    Returns a dict:
        {
            "status":         "ok" | "failed",
            "internet_cause": bool,   # True if internet was down at any point
            "vpn_cause":      bool,   # True if VPN was down at any point
        }

    Callers that previously checked `== "ok"` / `== "failed"` should use
    result["status"] instead.
    """
    _FAILED = lambda inet, vpn: {"status": "failed", "internet_cause": inet, "vpn_cause": vpn}
    _OK     = lambda inet, vpn: {"status": "ok",     "internet_cause": inet, "vpn_cause": vpn}

    # Use per-device loading phase state if available (more reliable than context string)
    effective_loading = in_loading or _loading_phase_active.get(device, False)

    # Verify still on connection issue page
    img = get_screenshot(device)
    if img is None or not is_on_page(device, "connection issue", image=img):
        dlog.info("── [B4] Not on connection issue page — ignoring")
        return _OK(False, False)

    dlog.info("[B4][INET] connection issue detected")

    vpn_up   = vpn_activity(device)
    inet_ok  = internet(device)   # always check internet, even if VPN/tun0 is up

    dlog.info(f"[B4][INET] emulator internet status={'UP' if inet_ok else 'DOWN'}")

    # Check host internet immediately — needed for classification even when
    # emulator internet looks OK, because a live connection issue page means
    # the game connection is bad regardless of tun0/ping state.
    host_ok_initial = _host_internet_ok_bot()
    dlog.info(f"[B4][INET] host internet status={'UP' if host_ok_initial else 'DOWN'}")

    if not host_ok_initial:
        dlog.error("[B4][INET] host down — global internet emergency")
        _notify_internet_down(device)
        return _FAILED(False, False)

    # Sticky cause flags — set to True when the cause is observed; never reset to
    # False just because the condition recovered. This ensures an internet-caused
    # connection issue stays classified as internet_cause=True even if internet
    # returns within the 40-second wait.
    internet_was_down = False
    vpn_was_down      = False

    # If internet is down, that's the root cause regardless of VPN state
    if not inet_ok:
        internet_was_down = True
        dlog.warning("[B4][INET] emulator internet failed")
        dlog.warning("[B4][INET] waiting up to 40s for emulator internet")
        t_inet = time.time()
        while time.time() - t_inet < 40.0:
            time.sleep(1.0)
            if internet(device):
                elapsed = time.time() - t_inet
                dlog.info(f"── [B4] Internet returned ({elapsed:.1f}s) ✓")
                inet_ok = True
                vpn_up  = vpn_activity(device)
                break

        if not inet_ok:
            # 40s elapsed — emulator internet still down.
            # Check host/global internet BEFORE notifying controller emergency.
            dlog.warning("[B4][INET] still down after 40s")
            host_ok = _host_internet_ok_bot()
            dlog.info(f"[B4][INET] host internet status={'UP' if host_ok else 'DOWN'}")

            if not host_ok:
                # Real global internet down — escalate to controller
                dlog.error("[B4][INET] host down — notifying controller global internet emergency")
                _notify_internet_down(device)
                return _FAILED(internet_was_down, vpn_was_down)
            else:
                # Host internet is fine — emulator-only VPN-route failure
                dlog.warning("[B4][INET] host up — emulator-only VPN-route issue")
                dlog.info("[B4][INET] attempting VPN-only reset (not global close-all)")
                vpn_reset_ok = _force_reset_vpn_only(
                    device, dlog, reason="B4 emulator-only internet down"
                )
                if vpn_reset_ok:
                    dlog.info("[B4][INET] internet restored after VPN-only reset")
                    dlog.info("[B4][INET] reopening TargetApp after VPN-only reset")
                    if not _ensure_vpn_prepare_target_app(device, dlog, context="B4 VPN-only reset"):
                        dlog.error("[B4][INET] VPN gate failed after VPN-only reset")
                        return _FAILED(internet_was_down, vpn_was_down)
                    if not open_target_app(device):
                        dlog.error("[B4][INET] open_target_app failed after VPN-only reset")
                        return _FAILED(internet_was_down, vpn_was_down)
                    reached = _wait_for_activity(
                        device,
                        TARGET_APP_PACKAGE,
                        timeout=20.0,
                        dlog=dlog,
                        context="B4 after VPN-only reset",
                    )
                    if not reached:
                        dlog.error("[B4][INET] TargetApp activity not confirmed after VPN-only reset")
                        return _FAILED(internet_was_down, vpn_was_down)
                    dlog.info("[B4][INET] TargetApp activity confirmed after VPN-only reset")
                    # Check what page we are on before trying to click OK
                    _img_post_reset = get_screenshot(device)
                    if _img_post_reset is not None and is_on_page(
                            device, "connection issue", image=_img_post_reset):
                        _post_reset_page = "connection issue"
                    elif _img_post_reset is not None and is_on_page(
                            device, "loading", image=_img_post_reset):
                        _post_reset_page = "loading"
                    elif _img_post_reset is not None and is_on_page(
                            device, "target app main", image=_img_post_reset):
                        _post_reset_page = "target app main"
                    else:
                        _post_reset_page = "unknown"
                    dlog.info(f"[B4][INET] page after VPN reset={_post_reset_page}")
                    if _post_reset_page in ("loading", "target app main"):
                        dlog.info("[B4][INET] already on loading/main — no OK click needed")
                        return _OK(internet_was_down, vpn_was_down)
                    elif _post_reset_page == "unknown":
                        dlog.error("[B4][INET] page unknown after VPN reset — device-level failure")
                        return _FAILED(internet_was_down, vpn_was_down)
                    # _post_reset_page == "connection issue": fall through to OK click below
                    dlog.info("[B4][INET] connection issue still visible — clicking OK")
                    inet_ok = True
                    vpn_up  = vpn_activity(device)
                    internet_was_down = True  # retain cause flag
                else:
                    dlog.error("[B4][INET] VPN-only reset failed — device-level failure")
                    _handle_vpn_recovery_failed_full_restart(
                        device, dlog, reason="B4 emulator-only VPN-only reset failed"
                    )
                    return _FAILED(internet_was_down, vpn_was_down)
        # internet_was_down remains True — the cause is recorded even after recovery

    if not vpn_up:
        vpn_was_down = True
        # B1/B2/B3 VPN logic inline (no force-stop, no setup_vpn)
        dlog.warning("── [B4] VPN down — 3s grace")
        t_grace = time.time()
        while time.time() - t_grace < 3.0:
            time.sleep(0.5)
            if vpn_activity(device):
                dlog.info("── [B4] VPN recovered in grace ✓")
                vpn_up = True
                break

        if not vpn_up:
            # Change VPN server — VPN was verified down after grace; force actual change.
            # force_change=True ensures we click Change Server even if VPN recovered
            # between the grace check and the _vpn_change_server call.
            dlog.info("[B4][INET] host up — running VPN recovery/change-server")
            dlog.info("── [B4] Changing VPN server (force_change=True, 3 attempts inside)")
            if not _vpn_change_server(device, dlog, force_change=True):
                dlog.error("── [B4] VPN server change failed")
                dlog.warning(f"[B4][VPN] VPN recovery result=False")
                # Do not click OK on connection issue when VPN recovery failed.
                # Trigger one full device restart; if already used, fail device.
                return _FAILED(
                    internet_was_down, vpn_was_down
                ) if _handle_vpn_recovery_failed_full_restart(
                    device, dlog, reason="B4 VPN down server change failed"
                ) else _FAILED(internet_was_down, vpn_was_down)
            vpn_up = True
            dlog.info(f"[B4][VPN] VPN recovery result=True")

            # Return to TargetApp — check each step before continuing
            dlog.info("[B4][VPN] VPN server change succeeded — reopening TargetApp")
            if not _ensure_vpn_prepare_target_app(device, dlog, context="B4 VPN server change"):
                dlog.error("[B4][VPN] VPN gate failed after server change")
                return _FAILED(internet_was_down, vpn_was_down)
            if not open_target_app(device):
                dlog.error("[B4][VPN] open_target_app failed after VPN server change")
                return _FAILED(internet_was_down, vpn_was_down)
            reached = _wait_for_activity(
                device,
                TARGET_APP_PACKAGE,
                timeout=20.0,
                dlog=dlog,
                context="B4 after VPN server change",
            )
            if not reached:
                dlog.error("[B4][VPN] TargetApp activity not confirmed after VPN server change")
                return _FAILED(internet_was_down, vpn_was_down)
            dlog.info("[B4][VPN] TargetApp activity confirmed after VPN server change")
        # vpn_was_down remains True — cause recorded even after recovery
    else:
        # VPN and internet both appear OK — but connection issue page is visible.
        # This means the game connection is bad for a non-obvious reason.
        # Run VPN recovery/change-server to force a clean reconnect.
        dlog.info("[B4][INET] host up — running VPN recovery/change-server (CI page present despite tun0 UP)")
        _b4_ui = _classify_protonvpn_ui(device, dlog)
        _b4_state = _b4_ui["state"]
        dlog.info(f"[B4][VPN] ProtonVPN UI state={_b4_state!r}")
        if _b4_state == "protected_change_timer_unavailable":
            dlog.info(f"[B4][VPN] Change Server unavailable/timer but VPN protected — returning to TargetApp")
            # VPN is already connected; just click OK and continue
        else:
            # Attempt VPN recovery via _vpn_change_server (force_change=True)
            _b4_vpn_ok = _vpn_change_server(device, dlog, force_change=True)
            dlog.info(f"[B4][VPN] VPN recovery result={_b4_vpn_ok}")
            if not _b4_vpn_ok:
                # VPN recovery failed — do not click OK, trigger full device restart once.
                dlog.error("── [B4] VPN recovery failed (vpn was UP) — triggering full device restart")
                _handle_vpn_recovery_failed_full_restart(
                    device, dlog, reason="B4 VPN recovery failed (tun0 was UP but CI page)"
                )
                return _FAILED(internet_was_down, vpn_was_down)
            else:
                # VPN recovery succeeded — reopen TargetApp with full checks
                dlog.info("[B4][VPN] VPN recovery succeeded — reopening TargetApp")
                if not _ensure_vpn_prepare_target_app(device, dlog, context="B4 VPN recovery (vpn was up)"):
                    dlog.error("[B4][VPN] VPN gate failed after VPN recovery")
                    return _FAILED(internet_was_down, vpn_was_down)
                if not open_target_app(device):
                    dlog.error("[B4][VPN] open_target_app failed after VPN recovery")
                    return _FAILED(internet_was_down, vpn_was_down)
                reached = _wait_for_activity(
                    device,
                    TARGET_APP_PACKAGE,
                    timeout=20.0,
                    dlog=dlog,
                    context="B4 recovery reopen",
                )
                if not reached:
                    dlog.error("[B4][VPN] TargetApp activity not confirmed after VPN recovery")
                    return _FAILED(internet_was_down, vpn_was_down)
                dlog.info("[B4][VPN] TargetApp activity confirmed after VPN recovery")

    # Track connection issue with accurate cause flags
    now = time.time()
    ci_ts = _connection_issue_timestamps.setdefault(device, [])
    ci_ts_typed = [(t, ic) for (t, ic) in ci_ts if now - t <= 60.0]
    ci_ts_typed.append((now, internet_was_down))   # inet_cause = internet_was_down (sticky)
    _connection_issue_timestamps[device] = ci_ts_typed

    dlog.info(
        f"── [B4] Cause flags: internet_was_down={internet_was_down} "
        f"vpn_was_down={vpn_was_down}"
    )

    # Click OK
    try:
        ok_rect = _get_page_button_rect("connection issue", "ok")
        click_in_bounding_box(device, *ok_rect)
        dlog.info(f"── [B4] Clicked OK ✓")
    except Exception as exc:
        dlog.error(f"── [B4] OK click failed: {exc}")
        return _FAILED(internet_was_down, vpn_was_down)

    time.sleep(0.8)

    # Wait for correct page after OK
    if effective_loading:
        page = when_on_page(device, ["loading", "target app main"], timeout=20.0)
    else:
        page = when_on_page(device, ["target app main"], timeout=20.0)

    if not page:
        dlog.error(f"── [B4] Expected page did not appear after OK (loading={effective_loading})")
        return _FAILED(internet_was_down, vpn_was_down)

    dlog.info(f"── [B4] Page confirmed after OK: {page!r} ✓")
    return _OK(internet_was_down, vpn_was_down)


# ── guarded_sleep ──────────────────────────────────────────────────────────────

def guarded_sleep(
    device:      str,
    seconds:     float,
    dlog=None,
    guard=None,
    context:     str   = "",
    require_target_app: bool  = True,
    chunk:       float = 1.0,
) -> bool:
    """
    Sleep for `seconds` total, split into chunks of at most `chunk` seconds.
    Uses guard_fix_if_signalled() each chunk — fast no-op when no signal is pending;
    falls through to full guard_check_and_recover() only when TargetAppGuard has fired.

    Returns True  — sleep completed normally.
    Returns False — guard recovery failed (device unrecoverable).

    Use instead of random_delay() for any wait >= 1 second inside task code.
    Short delays (< 1s) may still use random_delay() or time.sleep() directly.
    """
    if dlog is None:
        dlog = _get_device_logger(device)

    ctx      = f"guarded_sleep/{context}" if context else "guarded_sleep"
    end_time = time.time() + seconds

    while time.time() < end_time:
        # Explicit pause gate as well as the one inside guard_fix_if_signalled:
        # a long sleep is exactly where a pause is most likely to land, and this
        # keeps the wait from silently running out during an outage.
        if _pause_requested():
            gate = wait_while_paused(device, dlog, phase="runtime",
                                     fn="guarded_sleep", context="runtime")
            if gate == SIG_MANUAL_STOP:
                return False
            dlog.info(
                f"[GUARD-SYNC] [{device}] guarded_sleep: resumed from controller "
                f"pause — aborting remaining sleep so the task restarts"
            )
            return False
        if not guard_fix_if_signalled(device, dlog, guard, context=ctx):
            dlog.warning(
                f"[GUARD-SYNC] [{device}] guarded_sleep: recovery failed "
                f"— aborting remaining sleep of {end_time - time.time():.1f}s"
            )
            return False
        remaining = end_time - time.time()
        if remaining <= 0:
            break
        time.sleep(min(chunk, remaining))

    return True


# ── Shared helpers ────────────────────────────────────────────────────────────

def _wp2(device: str, page_name: str, dlog, guard=None) -> bool:
    """
    Wait for page, 5s max. Returns True if found, False if not.
    Passes guard + dlog through to when_on_page so guard polling is active
    during the wait. Guard is optional — existing callers pass nothing.
    """
    result = when_on_page(device, page_name, timeout=5.0, guard=guard, dlog=dlog)
    if not result:
        dlog.warning(f"── daily ── page '{page_name}' not found")
    return bool(result)

def _target_app_is_on_main_or_popup(device: str, dlog, img) -> str:
    """
    Inspect a fresh post-loading screenshot and classify it as one of:
      "main"    — target app main or game main map is visible.
      "popup"   — a known in-game popup is visible (connection issue,
                  new server reward, widget promo, server protect, …).
      "unknown" — neither matched; caller should fall back to _back_to_main.
    """
    if img is None:
        dlog.warning("── _target_app_is_on_main_or_popup ── img is None — returning unknown")
        return "unknown"

    try:
        if is_on_page(device, "target app main", image=img):
            dlog.debug("── _target_app_is_on_main_or_popup ── matched 'target app main'")
            return "main"
        if is_on_page(device, "game main map", image=img):
            dlog.debug("── _target_app_is_on_main_or_popup ── matched 'game main map'")
            return "main"
    except Exception as ex:
        dlog.debug(f"── _target_app_is_on_main_or_popup ── main check raised: {ex!r}")

    _POPUP_PAGES = (
        "new server reward",
        # connection issue is handled only by guard/B4 — not a post-loading popup
        # widget promo and server protect excluded until needed
    )
    for popup in _POPUP_PAGES:
        try:
            if is_on_page(device, popup, image=img):
                dlog.debug(f"── _target_app_is_on_main_or_popup ── matched popup {popup!r}")
                return "popup"
        except Exception as ex:
            dlog.debug(
                f"── _target_app_is_on_main_or_popup ── popup check {popup!r} raised: {ex!r}"
            )

    return "unknown"

def _target_app_post_loading_to_main(device: str, dlog, guard) -> bool:
    """
    Safe post-loading navigation to target app main.

    Flow (updated):
        1. Log "Loading confirmed done" + "TargetApp activity confirmed".
        2. Start 30-second MinuteMaid handling window.
        3. Take ONE fresh screenshot immediately (no fixed render wait).
        4. Classify via _target_app_is_on_main_or_popup().
        5. main    → mark page seen, success.
           popup   → call _back_to_main directly.
           unknown → save screenshot to unknown_pages/, then call _back_to_main.
    """
    dlog.info("── post_loading ── Loading confirmed done")
    dlog.info("── post_loading ── TargetApp activity confirmed")
    print(f"[{device}] post_loading: taking screenshot immediately after loading")
    # Note: MinuteMaid 30s window was already started in _target_app_watch_loading
    # when loading was confirmed done. No need to start it again here.

    img = get_screenshot(device)
    if img is None:
        dlog.warning("── post_loading ── Screenshot failed — trying once more")
        time.sleep(1)
        img = get_screenshot(device)
        if img is None:
            dlog.warning("── post_loading ── Screenshot failed twice — falling back to _back_to_main")
            return _back_to_main(device, dlog, guard)

    dlog.info("── post_loading ── Fresh screenshot taken immediately after loading")
    page_state = _target_app_is_on_main_or_popup(device, dlog, img)
    dlog.info(f"── post_loading ── page_state={page_state}")
    print(f"[{device}] post_loading: page_state={page_state}")

    if page_state == "main":
        _mark_page_seen(device, "target app main")
        dlog.info("── post_loading ── main confirmed on first check ✓")
        return True

    # 2C — popup detected: call _back_to_main directly (no separate Back loop)
    if page_state == "popup":
        dlog.info("── post_loading ── popup detected — calling _back_to_main directly")
        print(f"[{device}] post_loading: popup — calling _back_to_main")
        return _back_to_main(device, dlog, guard)

    # 2D — unknown: save screenshot first, then call _back_to_main
    dlog.warning("── post_loading ── page unknown — saving screenshot before _back_to_main")
    try:
        import os as _os
        _unk_dir = _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), "unknown_pages")
        _os.makedirs(_unk_dir, exist_ok=True)
        _safe_dev = device.replace(":", "_").replace(".", "_")
        _ts_str   = time.strftime("%Y%m%d_%H%M%S")
        _unk_path = _os.path.join(_unk_dir, f"{_safe_dev}_post_loading_unknown_{_ts_str}.png")
        if hasattr(img, "save"):
            img.save(_unk_path)
        dlog.info(f"[UNKNOWN-PAGE] post-loading page unknown — saved screenshot path={_unk_path}")
        print(f"[{device}] [UNKNOWN-PAGE] saved screenshot: {_unk_path}")
    except Exception as _ue:
        dlog.warning(f"[UNKNOWN-PAGE] screenshot save failed: {_ue!r}")
    dlog.warning("[UNKNOWN-PAGE] falling back to _back_to_main")
    print(f"[{device}] post_loading: page unknown — fallback to _back_to_main")
    return _back_to_main(device, dlog, guard)

def _back_to_main(device: str, dlog, guard) -> bool:
    """
    Navigate to 'target app main'. Handles game main map by clicking the app button.
    Both pages share visual elements — game main map takes priority if both match.

    Stale-interrupt handling:
      The guard interrupt Event can be left set from an earlier check that has
      already been consumed/resolved. _back_to_main MUST NOT exit just because
      the Event is set — it consults the live guard's result first. Only real
      restart/failure outcomes abort; "ok" outcomes clear the stale flag and
      continue.

    Returns True if main screen reached, False if couldn't recover after 10 attempts.
    """
    _REAL_STOP_OUTCOMES = {
        "offline", "connection_issue", "restart", "restart_stage3",
        "full_restart", "failure", "done",
    }

    for _ in range(10):
        if _guard_interrupt_event(device).is_set():
            dlog.info("── _back_to_main ── guard interrupt found")
            if guard is None:
                _guard_interrupt_clear(device)
                dlog.info("── _back_to_main ── stale guard interrupt cleared (no guard), continuing")
            else:
                try:
                    result = guard.check()
                except Exception as _ge:
                    result = ("ok",)
                    dlog.debug(f"── _back_to_main ── guard.check() raised: {_ge!r}")
                dlog.info(f"── _back_to_main ── guard outcome={result!r}")

                outcome = result[0] if result else "ok"
                if outcome in _REAL_STOP_OUTCOMES:
                    dlog.warning(
                        f"── _back_to_main ── real guard {outcome} — exiting"
                    )
                    return False

                try:
                    guard.clear_result()
                except Exception:
                    pass
                _guard_interrupt_clear(device)
                dlog.info("── _back_to_main ── stale guard interrupt cleared, continuing")

        current = _get_current_activity(device)

        # MinuteMaid: handle within the post-loading window only (no fixed wait).
        if current and "MinuteMaidActivity" in current:
            if _handle_minutemaid_if_in_window(device, dlog):
                continue  # Back was pressed — re-check activity next iteration
            # Outside window — treat as unexpected activity
            dlog.warning("── _back_to_main ── MinuteMaidActivity outside window — treating as unexpected")
            g = _gc(device, dlog, guard)
            if g is not None:
                return False
            continue

        if current and "targetapp" not in current:
            dlog.warning(f"── _back_to_main ── TargetApp not in foreground ({current!r}) — handing to guard")
            g = _gc(device, dlog, guard)
            if g is not None:
                return False

        img = get_screenshot(device)
        if img is None:
            dlog.warning("── _back_to_main ── screenshot None — calling guard_check_and_recover")
            ok = guard_check_and_recover(device, dlog, guard, context="_back_to_main/screenshot_none")
            if not ok:
                return False
            continue

        on_map = is_on_page(device, "game main map", image=img)
        on_ark = is_on_page(device, "target app main", image=img)

        if on_map:
            dlog.info("── _back_to_main ── game main map detected — clicking app button")
            _mark_page_seen(device, "game main map")
            click_in_bounding_box(device, *_get_page_button_rect("game main map", "app"))
            guarded_sleep(device, random.uniform(1, 1.5), dlog=dlog, guard=guard)
            g = _gc(device, dlog, guard)
            if g is not None:
                return False
            continue

        if on_ark:
            dlog.info("── _back_to_main ── target app main confirmed ✓")
            _mark_page_seen(device, "target app main")
            return True

        press_back(device)
        random_delay(0.5, 1.0)

    dlog.warning("── _back_to_main ── could not reach target app main after 10 attempts")
    return False

# ── Named wrappers ─────────────────────────────────────────────────────────────
# Each wrapper fixes all params so callers need zero knowledge of page names.
# Signature: func(device, dlog, guard) → str
# Caller must have already navigated (zoom + go_up/down) before calling.

# ── top buildings ─────────────────────────────────────────────────────────────

# ── bottom buildings ──────────────────────────────────────────────────────────


# ── vip_collect ───────────────────────────────────────────────────────────────

# ── VIP Collect ───────────────────────────────────────────────────────────────
# The one live task. Deliberately idempotent: it holds no progress state, so an
# interruption at any point is safe to retry — a rerun after a successful click
# simply reads "Sold Out" and returns done.

VIP_FREE_RECT = (1553, 358, 1856, 427)   # the "Free" / "Sold Out" button label


def _vip_normalize_ocr(raw: str) -> str:
    """lowercase, punctuation/newlines -> spaces, collapse runs of whitespace."""
    s = (raw or "").lower()
    s = re.sub(r"[^a-z0-9]+", " ", s)
    return re.sub(r"\s+", " ", s).strip()


def _vip_classify(text: str) -> str:
    """
    "sold_out" | "free" | "unknown".

    Order matters: "sold out" is checked first because a button reading
    "SOLD OUT" must never be mistaken for a collectable one. "free" is matched
    as a whole word so "freebie"-style noise cannot trigger a click.
    """
    if "sold" in text and "out" in text:
        return "sold_out"
    if re.search(r"\bfree\b", text):
        return "free"
    return "unknown"


def vip_collect(device: str, dlog, guard, st=None) -> str:
    """
    Collect the free VIP daily chest.

    Returns one of: "done" | "restart" | "full_restart" | "vpn_down" | "stopped".

    `st` is accepted for signature compatibility with the generic runner and is
    deliberately unused — see the note above about idempotence.

    Does NOT call update_status: the runner writes VipCollect=done only when this
    returns "done". Does NOT return to the main screen on success either; the next
    task is responsible for its own entry navigation.
    """
    dlog.info("── vip_collect ── starting pass")

    # ── STEP 1 — reach the main screen ──────────────────────────────────────────
    if not _back_to_main(device, dlog, guard):
        # Let a real guard/recovery verdict win over a generic retry.
        g = _gc(device, dlog, guard)
        if g is not None and g != "restart":
            dlog.warning(f"── vip_collect ── guard signal while recovering: {g!r}")
            return g
        dlog.warning("── vip_collect ── could not reach main screen — full_restart")
        return "full_restart"

    # ── STEP 2 — click VIP, guarded ──────────────────────────────────────────
    if not _wp2(device, "target app main", dlog, guard=guard):
        dlog.warning("── vip_collect ── main screen not confirmed after _back_to_main")
        return "restart"

    g = _gc(device, dlog, guard)
    if g is not None:
        dlog.warning(f"── vip_collect ── guard signal before vip click: {g!r}")
        return g

    try:
        vip_rect = _get_page_button_rect("target app main", "vip")
    except Exception as exc:
        dlog.error(f"── vip_collect ── vip button rect lookup failed: {exc!r}")
        return "restart"

    # Last moment before the tap. Without this a Stop arriving during the rect
    # lookup still sent the click, and only the guarded_sleep after it noticed.
    if _stop_requested():
        dlog.info("── vip_collect ── manual stop before the VIP click")
        return "stopped"

    dlog.info(f"── vip_collect ── clicking 'vip' on main screen rect={vip_rect}")
    click_in_bounding_box(device, *vip_rect)
    # guarded_sleep returns False for manual stop, a controller pause, or a
    # failed synchronous recovery. Ignoring it let the task carry on through an
    # interrupted step and potentially report "done".
    sleep_ok = guarded_sleep(device, random.uniform(1.0, 1.5),
                             dlog=dlog, guard=guard, context="vip_open")
    if not sleep_ok:
        if _stop_requested():
            dlog.info("── vip_collect ── manual stop during guarded wait")
            return "stopped"
        dlog.warning("── vip_collect ── guarded wait interrupted — restarting task")
        return "restart"

    g = _gc(device, dlog, guard)
    if g is not None:
        # Interrupted before we could read anything. Nothing was collected and
        # nothing is recorded, so the retry is clean.
        dlog.warning(f"── vip_collect ── guard signal after vip click: {g!r}")
        return g

    # ── STEP 3 — confirm the VIP page ────────────────────────────────────────
    if not when_on_page(device, "vip", timeout=8.0, guard=guard, dlog=dlog):
        # No OCR of an unknown screen: reading arbitrary pixels here is how a
        # wrong "free" match would turn into a stray click.
        dlog.warning("── vip_collect ── 'vip' page not confirmed — restart")
        return "restart"

    # ── FUTURE EXTENSION: red VIP badge ──────────────────────────────────────
    # A red-dot detector could be added here once a real screenshot and a
    # confirmed rectangle/threshold exist. No coordinates or HSV ranges are
    # invented in the meantime.
    #
    # If it is added: red PRESENT may be used as a positive hint only. Red
    # ABSENT must still open the VIP page and read the button, because the badge
    # is a notification and not a record of what was collected. A colour check
    # must never become the authoritative "already done" condition.

    # ── STEP 4 — OCR the button ──────────────────────────────────────────────
    # One screenshot, reused by both passes. A second capture would risk reading
    # a different frame than the one that was classified.
    img = get_screenshot(device)
    if img is None:
        dlog.warning("── vip_collect ── no screenshot on the vip page — restart")
        return "restart"

    raw1 = text_detect(image=img, region=VIP_FREE_RECT, engine="tesseract",
                       to_gray=True, tess_psm=7, return_boxes=False) or ""
    norm = _vip_normalize_ocr(raw1)
    verdict = _vip_classify(norm)
    dlog.info(f"── vip_collect ── OCR pass1 raw={raw1!r} normalized={norm!r} "
              f"verdict={verdict}")

    raw2 = ""
    if verdict == "unknown":
        # Second pass on the SAME frame, binarized. Otsu often rescues a label
        # that grayscale alone could not separate from the button art.
        raw2 = text_detect(image=img, region=VIP_FREE_RECT, engine="tesseract",
                           to_gray=True, binarize=True, threshold_method="otsu",
                           tess_psm=7, return_boxes=False) or ""
        norm = _vip_normalize_ocr(raw2)
        verdict = _vip_classify(norm)
        dlog.info(f"── vip_collect ── OCR pass2 (otsu) raw={raw2!r} "
                  f"normalized={norm!r} verdict={verdict}")
    # EasyOCR is deliberately not used: unknown already falls back to clicking,
    # so a third engine would cost ~9s without changing the outcome.

    # ── STEP 5 — act ─────────────────────────────────────────────────────────
    if verdict == "sold_out":
        dlog.info("── vip_collect ── VIP Daily Chest already collected "
                  "(Sold Out) — no click needed ✓")
        return "done"

    if verdict == "free":
        dlog.info("── vip_collect ── 'Free' detected — collecting")
    else:
        dlog.warning("── vip_collect ── OCR inconclusive; clicking anyway. "
                     "A wasted click on a Sold Out button is harmless, whereas "
                     "skipping would silently lose the day's chest.")

    if _stop_requested():
        # Nothing has been collected yet, so stopping here is completely clean.
        dlog.info("── vip_collect ── manual stop before the reward click")
        return "stopped"

    click_in_bounding_box(device, *VIP_FREE_RECT)
    sleep_ok = guarded_sleep(device, random.uniform(1.0, 1.5),
                             dlog=dlog, guard=guard, context="vip_reward")
    if not sleep_ok:
        # The click may well have landed, but this pass was interrupted before
        # that could be established. Never claim "done" here: the retry re-reads
        # the button and, if the click did land, sees Sold Out.
        if _stop_requested():
            dlog.info("── vip_collect ── manual stop during guarded wait")
            return "stopped"
        dlog.warning("── vip_collect ── guarded wait interrupted — restarting task")
        return "restart"

    g = _gc(device, dlog, guard)
    if g is not None:
        # Interrupted AFTER the click. Propagate rather than claiming success —
        # a retry re-reads the button and will see Sold Out.
        dlog.warning(f"── vip_collect ── guard signal after reward click: {g!r}")
        return g

    dlog.info("── vip_collect ── done ✓ (staying on the VIP page; the next task "
              "navigates from its own entry)")
    return "done"




def tutorial(device: str, dlog, guard, st=None) -> str:
    """
    Click through the new-player tutorial, then dismiss whichever post-tutorial
    interstitial offer/event the game lands on afterward.

    Phase 1 — click CLICK_BOX every 1s until "tutorial_pg25" appears (200s cap).
    Phase 2 — click "tutorial_pg25" itself, then click CLICK_BOX up to 4 times,
               5s apart, checking for "tutorial_pg27" before each click. If it
               never appears within those 4 clicks, continue anyway — this
               phase never returns "restart".
    Phase 3 — back to 1s-interval clicking, watching only for one of the four
               known end-state pages (200s cap). When one appears, press back
               once and the task is complete.

    Returns one of: "done" | "restart" | "full_restart" | "stopped".
    """
    CLICK_BOX = (793, 292, 1353, 750)
    END_PAGES = ("crisis forecast 1", "midnight growth pack",
                 "bridge level rush", "hancock offer")
    _PHASE1_MAX_S = 200.0
    _PHASE3_MAX_S = 200.0

    dlog.info("── tutorial ── starting pass")

    # ── STEP 1 — reach a known state ─────────────────────────────────────────
    if not _back_to_main(device, dlog, guard):
        g = _gc(device, dlog, guard)
        if g is not None and g != "restart":
            dlog.warning(f"── tutorial ── guard signal while recovering: {g!r}")
            return g
        dlog.warning("── tutorial ── could not reach main screen — full_restart")
        return "full_restart"

    # ── STEP 2 — phase 1: click until tutorial_pg25 appears (200s cap) ──────
    dlog.info("── tutorial ── phase 1: clicking for tutorial_pg25")
    _t_phase1 = time.time()
    while True:
        g = _gc(device, dlog, guard)
        if g is not None:
            dlog.warning(f"── tutorial ── guard signal during phase 1: {g!r}")
            return g

        if is_on_page(device, "tutorial_pg25"):
            dlog.info("── tutorial ── tutorial_pg25 seen")
            break

        if time.time() - _t_phase1 > _PHASE1_MAX_S:
            dlog.warning(f"── tutorial ── phase 1 exceeded {_PHASE1_MAX_S:.0f}s "
                        "without tutorial_pg25 — restart")
            return "restart"

        if _stop_requested():
            dlog.info("── tutorial ── manual stop during phase 1")
            return "stopped"
        click_in_bounding_box(device, *CLICK_BOX)

        sleep_ok = guarded_sleep(device, 1.0, dlog=dlog, guard=guard,
                                 context="tutorial_phase1")
        if not sleep_ok:
            if _stop_requested():
                dlog.info("── tutorial ── manual stop during phase 1 wait")
                return "stopped"
            dlog.warning("── tutorial ── guarded wait interrupted in phase 1 — restart")
            return "restart"

    # Click the pg25 screen itself before switching to the phase-2 cadence.
    if _stop_requested():
        dlog.info("── tutorial ── manual stop before tutorial_pg25 click")
        return "stopped"
    click_in_bounding_box(device, *CLICK_BOX)
    dlog.info("── tutorial ── clicked tutorial_pg25, entering phase 2 "
              "(max 4 clicks, 5s apart)")

    # ── STEP 3 — phase 2: up to 4 clicks, 5s apart, for tutorial_pg27 ───────
    # No time cap here by design — bounded to at most 4 x 5s, and this phase
    # never returns "restart": if tutorial_pg27 isn't seen after 4 clicks, the
    # task continues into phase 3 anyway.
    for _click_num in range(4):
        g = _gc(device, dlog, guard)
        if g is not None:
            dlog.warning(f"── tutorial ── guard signal during phase 2: {g!r}")
            return g

        if is_on_page(device, "tutorial_pg27"):
            dlog.info("── tutorial ── tutorial_pg27 seen")
            break

        if _stop_requested():
            dlog.info("── tutorial ── manual stop during phase 2")
            return "stopped"
        click_in_bounding_box(device, *CLICK_BOX)

        sleep_ok = guarded_sleep(device, 5.0, dlog=dlog, guard=guard,
                                 context="tutorial_phase2")
        if not sleep_ok:
            if _stop_requested():
                dlog.info("── tutorial ── manual stop during phase 2 wait")
                return "stopped"
            dlog.warning("── tutorial ── guarded wait interrupted in phase 2 — restart")
            return "restart"
    else:
        dlog.info("── tutorial ── tutorial_pg27 not seen after 4 clicks — "
                  "continuing anyway")

    dlog.info("── tutorial ── entering phase 3 (1s wait)")

    # ── STEP 4 — phase 3: 1s clicking, watching for a known end page ────────
    dlog.info("── tutorial ── phase 3: clicking until an end page appears")
    _t_phase3 = time.time()
    while True:
        g = _gc(device, dlog, guard)
        if g is not None:
            dlog.warning(f"── tutorial ── guard signal during phase 3: {g!r}")
            return g

        matched = when_on_page(device, END_PAGES, timeout=0.1, guard=guard, dlog=dlog)
        if matched:
            dlog.info(f"── tutorial ── end page {matched!r} seen — pressing back")
            press_back(device, 1, *END_PAGES, delay=1.0)
            dlog.info("── tutorial ── done \u2713")
            return "done"

        if time.time() - _t_phase3 > _PHASE3_MAX_S:
            dlog.warning(f"── tutorial ── phase 3 exceeded {_PHASE3_MAX_S:.0f}s "
                        "without a known end page — restart")
            return "restart"

        if _stop_requested():
            dlog.info("── tutorial ── manual stop during phase 3")
            return "stopped"
        click_in_bounding_box(device, *CLICK_BOX)

        sleep_ok = guarded_sleep(device, 1.0, dlog=dlog, guard=guard,
                                 context="tutorial_phase3")
        if not sleep_ok:
            if _stop_requested():
                dlog.info("── tutorial ── manual stop during phase 3 wait")
                return "stopped"
            dlog.warning("── tutorial ── guarded wait interrupted in phase 3 — restart")
            return "restart"


# ── task registry ─────────────────────────────────────────────────────────────
# The ONE place a task key maps to a callable. device_worker (Run mode) and the
# controller (Test mode) both resolve through get_task_callable(), so the two
# paths cannot drift apart. The controller's TASK_DEFS is UI/status metadata and
# holds no function objects.

TASK_FUNCTIONS = {
    "vip_collect": vip_collect,
    "tutorial": tutorial,
}


def get_task_callable(task_key: str):
    """Callable for a task key, or None. Never raises KeyError."""
    return TASK_FUNCTIONS.get((task_key or "").strip())




# ------------------------------------------------------------
# 12. MAIN EXECUTION & RUNNER
# ------------------------------------------------------------

def device_worker(dev_id:        str,
                  task_keys:     list,
                  task_defs:     dict,
                  cfg_data:      dict,
                  skip_before:   bool,
                  status_q,
                  stop_flag,
                  pause_flag=None):
    """
    Runs INSIDE a subprocess spawned by the controller for one device.

    Contract
    --------
    - cfg_data was built by BotBridge._build_cfg_data() BEFORE the process
      was spawned — no sheet reads happen here.
    - Pushes dicts to status_q for the UI to consume:
        {"type": "log",       "dev_id": dev_id, "msg": str, "tag": str}
        {"type": "task_done", "dev_id": dev_id, "task_key": str}
        {"type": "all_done",  "dev_id": dev_id, "ok": bool, "result": str}
    - The bot module is freshly imported in this process — completely isolated
      from every other device's process.
    """
    import sys, importlib.util, traceback as _tb, time as _time
    from pathlib import Path

    # ── helpers ────────────────────────────────────────────────────────────────
    def _push(msg_type: str, **kwargs):
        try:
            status_q.put_nowait({"type": msg_type, "dev_id": dev_id, **kwargs})
        except Exception:
            pass

    def _log(msg: str, tag: str = "dim"):
        print(f"[{dev_id}] {msg}", flush=True)
        _push("log", msg=msg, tag=tag)

    # ── Earliest-possible startup marker — written to queue before any risky
    # operation so that a 0-byte device log is diagnosable (see 6585 incident).
    _push("log", msg=f"[DEVICE_WORKER] process started adb_id={dev_id}", tag="dim")
    print(f"[{dev_id}] [DEVICE_WORKER] process started", flush=True)

    # ── import bot module fresh in this process ────────────────────────────────
    bot_path = cfg_data.get("_bot_path", "")
    _push("log", msg="[DEVICE_WORKER] importing bot module...", tag="dim")
    try:
        p    = Path(bot_path)
        name = f"target_app_bot_{abs(hash(str(p.resolve())))}"
        spec = importlib.util.spec_from_file_location(name, str(p))
        mod  = importlib.util.module_from_spec(spec)
        sys.modules[name] = mod
        spec.loader.exec_module(mod)
    except Exception as exc:
        _push("log", msg=f"[DEVICE_WORKER] import FAILED: {type(exc).__name__}: {exc}", tag="err")
        print(f"[{dev_id}] [DEVICE_WORKER] import FAILED: {exc}", flush=True)
        _push("all_done", ok=False, result=f"import error: {exc}")
        return

    _push("log", msg="[DEVICE_WORKER] bot module imported ✓", tag="dim")

    bot  = mod
    # Wire up the process-local status queue so guard can notify internet-down
    bot._WORKER_STATUS_Q = status_q
    # Wire up the controller -> worker pause channel.
    #
    # pause_flag is a DIFFERENT multiprocessing.Event from stop_flag and must
    # never be confused with it: stop means "the run is over", pause means "hold
    # still, the host lost internet, you are still alive".  Every action and
    # checkpoint path in the bot funnels through wait_while_paused(), which
    # reads this event.  pause_flag defaults to None so an older controller can
    # still spawn this worker — in that case the worker falls back to detecting
    # the outage with its own host check.
    bot._set_worker_pause_event(pause_flag)
    # ── logger created immediately after import so ALL failures are captured ──
    dlog = bot._get_device_logger(dev_id)
    dlog.info(f"device_worker started  dev={dev_id}  tasks={task_keys}")
    dlog.info(f"[DEVICE_WORKER] process started adb_id={dev_id}")
    dlog.info("[DEVICE_WORKER] bot module imported ✓")

    # ── D: Monkey-patch update_status and flush_status ────────────────────────
    # update_status: sends status_update to controller queue IMMEDIATELY on every
    #   call so updates are not lost if the process is force-killed between calls
    #   and flush_status.  Also keeps local _PENDING_STATUS buffer as backup.
    #   No Sheets writes happen from this worker process.
    # flush_status:  drains any remaining _PENDING_STATUS buffer to the queue,
    #   then clears the buffer.  No Sheets writes.
    _orig_update_status = bot.update_status  # kept for reference (not called)
    _orig_flush_status  = bot.flush_status   # kept for reference (not called)

    def _worker_update_status(device_name_or_id, header_name, status_value):
        """
        Redirect update_status → immediate queue message.
        Buffer in _PENDING_STATUS ONLY if the immediate send fails (queue full /
        not yet connected), so flush_status can retry it without duplicating
        successful sends.
        """
        key = (device_name_or_id or "").strip()
        if not key:
            return
        # 1. Try immediate send to controller
        sent_ok = False
        if status_q is not None:
            try:
                status_q.put_nowait({
                    "type":   "status_update",
                    "dev_id": key,
                    "header": str(header_name) if header_name is not None else "",
                    "value":  str(status_value),
                })
                sent_ok = True
            except Exception:
                pass
        # 2. Buffer ONLY if the immediate send failed — backup for force-kill
        if not sent_ok:
            if key not in bot._PENDING_STATUS:
                bot._PENDING_STATUS[key] = {}
            bot._PENDING_STATUS[key][header_name] = str(status_value)
        # 3. Log immediately (same as original)
        try:
            bot._get_device_logger(key).debug(
                f"── update_status(worker) ── "
                f"{'sent' if sent_ok else 'buffered (send failed)'} "
                f"{header_name}: {status_value}"
            )
        except Exception:
            pass

    def _worker_flush_status(device_name_or_id):
        """Drain any remaining local buffer to queue; no Sheets write."""
        key = (device_name_or_id or "").strip()
        updates = bot._PENDING_STATUS.pop(key, {})
        if not updates:
            return
        if status_q is not None:
            for hdr, val in updates.items():
                try:
                    status_q.put_nowait({
                        "type":   "status_update",
                        "dev_id": key,
                        "header": str(hdr) if hdr is not None else "",
                        "value":  str(val),
                    })
                except Exception:
                    pass
        try:
            bot._get_device_logger(key).info(
                f"── flush_status(worker) ── {len(updates)} buffered update(s) "
                f"sent to controller queue (no Sheets write)"
            )
        except Exception:
            pass

    bot.update_status = _worker_update_status
    bot.flush_status  = _worker_flush_status
    dlog.info("[DEVICE_WORKER] update_status + flush_status monkey-patched ✓")

    # ── seed this process's globals from cfg_data (no sheet read) ─────────────
    _STATUS_MAP = [
        ("vip_collect_status",        "_vip_collect_status"),
    ]
    for cfg_key, attr_name in _STATUS_MAP:
        val = cfg_data.get(cfg_key, {})
        setattr(bot, attr_name, val if isinstance(val, dict) else {})

    # _tekkman_missions / _redeem_codes are gone with their tasks. _device_type_map
    # stays: setup and the controller both use it independently of any task.
    bot._device_type_map  = cfg_data.get("device_type_map",  {})
    bot._available_version = cfg_data.get("available_version", "")
    dlog.info(f"[DIAG] device_worker ── _available_version seeded as {bot._available_version!r}")
    bot._DEVICE_ROW_CACHE.update(cfg_data.get("device_row_cache", {}))

    # ── Optional run recording ("Record video" checkbox) ─────────────────────
    # Delivered through cfg_data so no extra Process argument is needed.
    #
    # DEFERRED ON PURPOSE. `adb screenrecord` needs a device that is actually
    # connected. Starting it here — before the connect/launch block below — meant
    # that for any closed instance the recorder fired three screenrecord/pull
    # attempts against a device ADB had never heard of, hit its 3-failure limit,
    # gave up, and logged video_recording_failed... moments before the device
    # finished connecting. The real start happens after ADB readiness is
    # confirmed; see "recording video started after ADB ready" below.
    _record_video = bool(cfg_data.get("record_video", False))
    _rec_folder   = None
    if _record_video:
        dlog.info("[RECORD] recording video delayed until ADB ready")
        _log("recording video delayed until ADB ready", "dim")
    else:
        dlog.info("[RECORD] record_video is off for this run")

    # ── Validate page specs once, loudly ─────────────────────────────────────
    # A missing spec used to surface only as repeated "no spec found" debug lines
    # during Loading, which looked like a detection problem rather than a config
    # problem. One ERROR at startup naming the resolved path is far more useful.
    try:
        _pg = bot.validate_pages_config(
            log_fn=lambda msg, tag="dim": _log(msg, tag))
        if not _pg["ok"]:
            _log(f"pages.json missing required specs: {_pg['missing']}", "err")
    except Exception as _pg_exc:
        dlog.warning(f"[PAGES] validation raised: {_pg_exc!r}")

    # ── Warm EasyOCR once per worker process ─────────────────────────────────
    # Pays the model-load cost here rather than in the middle of VPN Connect
    # detection or Loading. Threaded and capped; failure is non-fatal.
    try:
        bot.warm_easyocr(dlog)
    except Exception as _oc_exc:
        dlog.warning(f"[EASYOCR] warmup call raised: {_oc_exc!r}")

    # ── Single finalization path ─────────────────────────────────────────────
    # Every exit from here on records its outcome and calls _finalize(), which
    # runs cleanup in a fixed order and pushes all_done LAST.
    #
    # Previously all_done was pushed at ~20 scattered sites and cleanup happened
    # afterwards (or, for the early returns above the task-loop try, not at all).
    # The controller treats all_done as "worker finished" and may terminate the
    # process, so announcing completion before stop_device_recording() could kill
    # the recorder mid-pull and leave the manifest and report unwritten.
    #
    # Order matters: guard -> recording (+ recording_done) -> flush -> reset ->
    # all_done. recording_done must reach the controller before all_done so the
    # folder path is known before the process is allowed to go away.
    _final_state = {"sent": False}

    def _finalize(ok: bool, result: str) -> None:
        """Run cleanup exactly once, then announce completion. Never raises."""
        if _final_state["sent"]:
            return
        _final_state["sent"] = True

        # 1. Stop TargetAppGuard so it is not running while we write to Sheets.
        try:
            g = bot._target_app_guards.pop(dev_id, None)
            if g:
                g.stop()
        except Exception:
            pass

        # 2. Stop recording and publish where it landed. Before the status flush
        #    so the manifest/report can still read the events file.
        if _record_video:
            try:
                _rec_info = bot.stop_device_recording(dev_id, dlog)
                if _rec_info and _rec_info.get("folder"):
                    _push("recording_done",
                          folder=_rec_info.get("folder", ""),
                          segments=_rec_info.get("segments", 0),
                          events=_rec_info.get("events", 0),
                          report=_rec_info.get("report", ""),
                          duration_s=_rec_info.get("duration_s", 0),
                          # Both flags travel: "lost a segment" and "no usable
                          # video" are different outcomes and the UI shows them
                          # differently.
                          failed=bool(_rec_info.get("failed")),
                          incomplete=bool(_rec_info.get("incomplete")))
                    _log(f"● Recording saved: {_rec_info['folder']} "
                         f"({_rec_info.get('segments', 0)} segment(s), "
                         f"{_rec_info.get('events', 0)} event(s))", "ok")
            except Exception as _rec_exc:
                dlog.warning(f"[RECORD] stop_device_recording raised: {_rec_exc!r}")

        # 3. Flush buffered status.
        try:
            bot.flush_status(dev_id)
        except Exception:
            pass

        # 4. Full per-run state reset.
        try:
            bot.reset_device_finished_state(dev_id)
        except Exception:
            pass

        try:
            bot.cleanup_device_files(dev_id)
        except Exception:
            pass

        # 5. ONLY NOW tell the controller we are finished.
        dlog.info(f"[WORKER-END] cleanup complete — sending all_done "
                  f"ok={ok} result={result!r}")
        _push("all_done", ok=ok, result=result)

    # ── install stop-flag checker ──────────────────────────────────────────────
    _orig_click = bot.click_in_bounding_box
    _orig_adb   = bot._adb_shell

    def _g_click(*a, **kw):
        if stop_flag.is_set():
            raise SystemExit(0)
        return _orig_click(*a, **kw)

    def _g_adb(*a, **kw):
        if stop_flag.is_set():
            raise SystemExit(0)
        return _orig_adb(*a, **kw)

    bot.click_in_bounding_box = _g_click
    bot._adb_shell             = _g_adb

    # Wire the per-thread stop event so unbounded guard wait loops
    # (_guard_verify_offline, Scenario C, _vpn_change_health_check) can exit
    # when the controller signals a stop without needing the flag passed
    # through every call stack.
    bot._thread_local.stop_event = stop_flag

    # ── FIX 2: connect & verify with retry (fixes silent death on slow start) ─
    # On first launch a BlueStacks instance may need several seconds before ADB
    # accepts connections. Without retry, any device that isn't ready at the
    # exact moment of spawn dies with zero log output (as seen with 6765).
    # ── connect & verify — check adb devices first, launch only if absent ─────
    connected = False
    for _attempt in range(2):                        # max 2 full attempts
        # Step 1: check if already listed in adb devices before doing anything
        try:
            _raw_devs = subprocess.run(
                ["adb", "devices"], capture_output=True, text=True, timeout=5
            ).stdout
        except Exception:
            _raw_devs = ""

        _already_listed = any(
            line.startswith(dev_id) and line.strip().endswith("device")
            for line in _raw_devs.splitlines()
        )

        if _already_listed:
            # Device is in adb already — just wait up to 20s for it to be ready
            dlog.info(
                f"[DIAG] device_worker ── attempt {_attempt+1}: "
                f"{dev_id} already in adb devices — waiting up to 20s"
            )
            if bot._adb_wait_for_device(dev_id, timeout=20, interval=2):
                connected = True
                dlog.info(f"ADB connected on attempt {_attempt+1}")
                break
            dlog.warning(
                f"Device not responding after 20s (attempt {_attempt+1}/2)"
            )
        else:
            # Device is NOT in adb at all — launch BlueStacks first, then wait
            dlog.info(
                f"[DIAG] device_worker ── attempt {_attempt+1}: "
                f"{dev_id} NOT in adb devices — launching instance"
            )
            try:
                bot._launch_device_for_worker(dev_id)
            except SystemExit:
                _finalize(ok=False, result="stopped")
                return
            except Exception as _ce:
                dlog.warning(f"_launch_device_for_worker attempt {_attempt+1} error: {_ce}")

            dlog.info(
                f"[DIAG] device_worker ── waiting up to 20s after launch "
                f"(attempt {_attempt+1})"
            )
            if bot._adb_wait_for_device(dev_id, timeout=20, interval=2):
                connected = True
                dlog.info(f"ADB connected on attempt {_attempt+1}")
                break
            dlog.warning(
                f"Device not responding after launch+20s (attempt {_attempt+1}/2)"
            )

    if not connected:
        dlog.error("Device never came online after 2 attempts — aborting")
        _log("ADB connect failed — aborting", "err")
        _finalize(ok=False, result="adb_connect_failed")
        return

    try:
        bot._verify_touch_device(dev_id, dlog)
    except Exception:
        pass

    # ── Start recording now that ADB is confirmed usable ─────────────────────
    # Reached only after `connected` is True, i.e. _adb_wait_for_device()
    # succeeded — for a device that was already open AND for one this worker
    # just launched. screenrecord can now actually reach the device.
    if _record_video:
        try:
            _rec_folder = bot.start_device_recording(dev_id, dlog, record_video=True)
            if _rec_folder:
                dlog.info(f"[RECORD] recording video started after ADB ready "
                          f"-> {_rec_folder}")
                _log(f"● recording video started after ADB ready → {_rec_folder}", "dim")
            else:
                dlog.warning("[RECORD] recording could not start after ADB ready")
                _log("recording could not start — continuing without it", "warn")
        except Exception as _rec_exc:
            dlog.warning(f"[RECORD] start_device_recording raised: {_rec_exc!r}")
            _log(f"recording failed to start ({_rec_exc}) — continuing", "warn")

    # ── Empty task list + skip_before ON → nothing to do ─────────────────────
    # Device connect/open above still happened (the instance is up and attached),
    # but with no tasks AND prepare_target_app skipped there is no work left. Reported as
    # a clean success, NOT a failure, and no task status is written.
    if not task_keys and skip_before:
        dlog.info("device_worker: no tasks configured and skip_before is ON — "
                  "nothing to do (prepare_target_app deliberately not run)")
        _log("No tasks and skip_before on — nothing to do", "warn")
        _finalize(ok=True, result="skipped_no_tasks")
        return

    # ── prepare: prepare_target_app or attach to existing session ─────────────────────
    try:
        activity = bot._get_current_activity(dev_id) or ""
    except Exception:
        activity = ""
    try:
        vpn_up = bool(bot.vpn_activity(dev_id))
    except Exception:
        vpn_up = False

    target_app_open = TARGET_APP_PACKAGE in activity
    try:
        if skip_before and target_app_open and vpn_up:
            guard = bot.TargetAppGuard(dev_id, dlog)
            guard.start()
            guard.set_stage(3)
            guard.set_target_app_opened()
            guard.set_main_page_seen()
            bot._target_app_guards[dev_id] = guard
            _log("Attached to existing TargetApp session", "dim")
        else:
            # Retry prepare_target_app up to 3 attempts total.
            # Each False means _reopen_device_capped already ran (if applicable)
            # and reset device state — so the next attempt starts clean.
            _BEFORE_TARGET_APP_MAX = 3
            _baw_ok = False
            for _baw_attempt in range(_BEFORE_TARGET_APP_MAX):
                if _baw_attempt > 0:
                    dlog.warning(
                        f"[BA-RETRY] prepare_target_app retry {_baw_attempt}/{_BEFORE_TARGET_APP_MAX - 1} "
                        f"for {dev_id}"
                    )
                    dlog.warning(
                        f"prepare_target_app retry {_baw_attempt}/{_BEFORE_TARGET_APP_MAX - 1} "
                        f"for {dev_id}"
                    )
                    _log(f"⟳ prepare_target_app retry {_baw_attempt}/{_BEFORE_TARGET_APP_MAX - 1}", "warn")
                try:
                    dlog.info(
                        f"[DEVICE_WORKER] entering prepare_target_app adb_id={dev_id} "
                        f"attempt={_baw_attempt + 1}/{_BEFORE_TARGET_APP_MAX}"
                    )
                    if bot.prepare_target_app(dev_id, force_stop_first=True):
                        _baw_ok = True
                        break
                except SystemExit:
                    raise
                except Exception as _baw_exc:
                    dlog.warning(
                        f"[BA-RETRY] prepare_target_app attempt {_baw_attempt + 1} raised: "
                        f"{type(_baw_exc).__name__}: {_baw_exc}"
                    )
                    _log(f"⚠ prepare_target_app attempt {_baw_attempt + 1} exception: {_baw_exc}", "warn")
                    if _baw_attempt >= _BEFORE_TARGET_APP_MAX - 1:
                        raise   # last attempt — propagate to outer except
                    _time.sleep(2.0)
            if not _baw_ok:
                dlog.error(f"[BA-RETRY] prepare_target_app failed after {_BEFORE_TARGET_APP_MAX} attempts")
                _finalize(ok=False, result="prepare_target_app failed")
                return
            _log("prepare_target_app completed", "dim")
    except bot.FatalAPKError as exc:
        # Newer TargetApp version found on device but APK missing locally —
        # signal controller to stop all running devices immediately
        msg = f"FATAL: {exc}"
        dlog.error(msg)
        print(f"[{dev_id}] {msg}", flush=True)
        _push("run_fatal_stop", reason=str(exc))
        _finalize(ok=False, result=str(exc))
        return
    except SystemExit:
        _finalize(ok=False, result="stopped")
        return
    except Exception as exc:
        _finalize(ok=False, result=f"prepare error: {exc}")
        return

    guard = bot._target_app_guards.get(dev_id)

    # ── inner helpers for task running ─────────────────────────────────────────

    def _run_one_task(task_key: str) -> str:
        if stop_flag.is_set():
            return "stopped"

        td = task_defs.get(task_key)
        if td is None:
            return f"unknown task: {task_key}"

        status_dict = getattr(bot, td["status_attr"], {})
        sub_attr    = td.get("sub_attr")
        sub_dict    = getattr(bot, sub_attr, None) if sub_attr else None

        if (status_dict.get(dev_id, "") or "").strip().lower() == "done":
            return "skipped"

        substatus = sub_dict.setdefault(dev_id, {}) if sub_dict is not None else None

        # Single source of truth for task callables. Both execution paths — the
        # controller's Test mode and this Run-mode worker — resolve through
        # bot.get_task_callable(), so a task can never exist in one and not the
        # other. task_defs carries UI/status metadata only, never functions.
        func = bot.get_task_callable(task_key)
        if func is None:
            return f"no function for task: {task_key}"

        attempt       = 0
        restart_count = 0
        MAX_RESTARTS  = 3
        while not stop_flag.is_set():
            attempt += 1
            _log(f"  {task_key} attempt #{attempt}", "dim")
            arg = substatus if substatus is not None else {}
            try:
                result = func(dev_id, dlog, guard, arg)
            except SystemExit:
                return "stopped"
            except bot.GuardRecoveryFailed:
                gr_reason = bot._last_guard_recovery_reason.get(dev_id, "")

                # Controller pause that has already been released.  Nothing is
                # wrong with the device — it simply held still while the host had
                # no internet.  Go back to the app and rerun THIS task from the
                # beginning; a full prepare_target_app would be wasted work here.
                if gr_reason == "host_pause_resumed":
                    bot._last_guard_recovery_reason.pop(dev_id, None)
                    dlog.warning(
                        f"── {task_key} ── resumed from controller pause — "
                        f"returning to main screen and restarting this task"
                    )
                    _log(f"  {task_key}: resumed after pause — restarting task", "warn")
                    try:
                        if not bot._back_to_main(dev_id, dlog, guard):
                            dlog.error(
                                f"── {task_key} ── _back_to_main failed after pause "
                                f"— escalating to full restart"
                            )
                            return "full_restart"
                    except Exception as _btm_exc:
                        dlog.error(
                            f"── {task_key} ── _back_to_main raised after pause: "
                            f"{_btm_exc!r} — escalating to full restart"
                        )
                        return "full_restart"
                    restart_count += 1
                    if restart_count >= MAX_RESTARTS:
                        dlog.error(
                            f"── {task_key} ── reached {MAX_RESTARTS} restarts "
                            f"after pause resumes — skipping task"
                        )
                        return "error"
                    continue

                # Check if this was a Scenario D recovery (emulator closed, relaunched,
                # prepare_target_app succeeded — but we must restart the task loop, not continue)
                if gr_reason == "device_closed_recovered":
                    dlog.warning(
                        f"── {task_key} ── GuardRecoveryFailed after Scenario D recovery "
                        f"— mapping to full_restart so task loop restarts from index 0"
                    )
                    bot._last_guard_recovery_reason.pop(dev_id, None)
                    return "full_restart"
                dlog.error(f"── {task_key} ── GuardRecoveryFailed (reason={gr_reason!r})")
                return "full_restart"
            # Stop wins, and is checked BEFORE the commit. Test mode already had
            # this; Run mode did not, so a Stop landing between the task
            # returning and the write below still recorded VipCollect=done.
            if stop_flag.is_set():
                dlog.info(f"── {task_key} ── stop set after the task returned "
                          f"{result!r} — no status commit")
                return "stopped"
            if result in ("stopped", getattr(bot, "SIG_MANUAL_STOP", "manual_stop")):
                dlog.info(f"── {task_key} ── returned {result!r} — "
                          f"manual stop, no status commit")
                return "stopped"

            if result == "done":
                status_dict[dev_id] = "done"
                if td.get("header"):
                    bot.update_status(dev_id, td["header"], "done")
                return "done"
            if result in ("full_restart", "vpn_down"):
                # Propagate immediately — task loop handles these
                return result
            if result == "restart":
                restart_count += 1
                if restart_count >= MAX_RESTARTS:
                    dlog.error(
                        f"── {task_key} ── reached {MAX_RESTARTS} restarts without "
                        f"completing — skipping task"
                    )
                    _log(f"  {task_key} skipped after {MAX_RESTARTS} restarts", "warn")
                    return "error"
                continue
            return str(result)
        return "stopped"

    # ── task loop ──────────────────────────────────────────────────────────────
    try:
        # Empty task list with skip_before OFF is a valid SETUP-ONLY run.
        #
        # prepare_target_app already ran in the prepare block above, so the device is up
        # and sitting on the main screen — that IS the requested work. Reporting a
        # failure here was the bug.
        #
        # The skip_before-ON case never reaches here (early exit above), so by
        # this point prepare_target_app has genuinely completed.
        #
        # No task function is called and NO task status is written: an empty run
        # must never mark any task done.
        if not task_keys:
            dlog.info("device_worker: prepare_target_app completed; no tasks configured "
                      "— setup-only run finished")
            _log("✓ prepare_target_app completed; no tasks configured", "ok")
            # Recorded as a phase event, deliberately NOT "task_done" — no task
            # ran, and a task_done row would misrepresent that in the report.
            bot.record_event(dev_id, "phase", fn="device_worker",
                             phase="setup_only",
                             message="prepare_target_app completed; no tasks configured")
            _finalize(ok=True, result="prepare_target_app_only")
            return
        task_idx = 0
        while task_idx < len(task_keys):
            task_key = task_keys[task_idx]

            if stop_flag.is_set():
                _finalize(ok=False, result="stopped")
                return

            dlog.info(f"{'─' * 20} TASK: {task_key} {'─' * 20}")
            _log(f"▶  starting {task_key}", "info")
            bot.record_event(dev_id, "task_start", task=task_key,
                             index=task_idx + 1, total=len(task_keys))
            _t_task = time.time()
            result = _run_one_task(task_key)

            # A manual stop is not a task failure. Recording it as task_failed
            # put a red entry in the timeline and the report for a run the
            # operator ended deliberately.
            if result == "stopped":
                bot.record_event(dev_id, "task_stopped", task=task_key,
                                 result="stopped",
                                 seconds=round(time.time() - _t_task, 1))
                dlog.info(f"── {task_key} ── RESULT: stopped (manual)")
                _log(f"■ {task_key} stopped", "warn")
                _finalize(ok=False, result="stopped")
                return

            bot.record_event(
                dev_id,
                "task_done" if result in ("done", "skipped") else "task_failed",
                task=task_key, result=str(result),
                seconds=round(time.time() - _t_task, 1),
            )

            if result in ("done", "skipped", "error"):
                if result == "done":
                    # J: only real completions send task_done
                    _push("task_done", task_key=task_key)
                    label = "complete"
                    lvl   = "ok"
                    dlog.info(f"── {task_key} ── RESULT: {label} ✓")
                    _log(f"✓ {task_key} {label}", lvl)
                    task_idx += 1
                    continue
                elif result == "skipped":
                    # J: already done — send task_skipped (not task_done)
                    _push("task_skipped", task_key=task_key)
                    label = "skipped (already done)"
                    dlog.info(f"── {task_key} ── RESULT: {label}")
                    _log(f"✓ {task_key} {label}", "ok")
                    task_idx += 1
                    continue
                else:
                    # K: result == "error" — max restarts reached, device must fail
                    err_label = f"{task_key} failed after max restarts"
                    dlog.error(f"── {task_key} ── RESULT: error — {err_label}")
                    _log(f"✗ {err_label}", "err")
                    _finalize(ok=False, result=err_label)
                    return

            if result == "full_restart":
                dlog.warning("── task loop ── full_restart: device offline, running prepare_target_app()")
                _log("⟳ Device recovered — restarting prepare_target_app", "warn")
                _baw_ok = False
                for _baw_attempt in range(3):
                    if bot.prepare_target_app(dev_id, force_stop_first=True):
                        _baw_ok = True
                        break
                    dlog.warning(f"prepare_target_app retry {_baw_attempt+1}/2")
                if not _baw_ok:
                    _finalize(ok=False, result="prepare_target_app failed after full_restart")
                    return
                guard = bot._target_app_guards.get(dev_id)
                dlog.info("── task loop ── prepare_target_app complete — restarting task loop")
                _log("✓ prepare_target_app complete — resuming tasks", "info")
                task_idx = 0
                continue

            if result == "vpn_down":
                dlog.warning("── task loop ── vpn_down: changing server")
                _log("⟳ VPN down — changing server", "warn")
                cs_ok = bot._vpn_change_server(dev_id, dlog, guard, force_change=True)
                if not cs_ok:
                    cs_reason = bot._last_vpn_change_failure_reason.get(dev_id, "unknown")
                    dlog.error(f"── task loop ── _vpn_change_server failed (reason={cs_reason!r})")
                    if cs_reason == "device_closed":
                        dlog.warning(
                            "── task loop ── device_closed during VPN change — "
                            "treating as full restart (prepare_target_app force_stop_first=True)"
                        )
                        _log("✗ Emulator closed during VPN change — full restart", "warn")
                        _baw_ok = False
                        for _baw_attempt in range(2):
                            try:
                                if bot.prepare_target_app(dev_id, force_stop_first=True):
                                    _baw_ok = True
                                    break
                            except Exception as _baw_e:
                                dlog.warning(f"prepare_target_app attempt {_baw_attempt+1} raised: {_baw_e}")
                            time.sleep(2.0)
                        if not _baw_ok:
                            dlog.error("── task loop ── prepare_target_app failed after device_closed — giving up")
                            _finalize(ok=False, result="device_closed_restart_failed")
                            return
                        # Restart guard and retry from top of task loop
                        guard = bot._target_app_guards.get(dev_id)
                        bot._restart_target_app_guard(guard, 3)
                        guard.set_target_app_opened()
                        task_idx = 0
                        continue
                    # Device alive, VPN unrecoverable -> fail the run.
                    # Deliberately no back_to_main, no task restart, and no
                    # prepare_target_app retry for this failure: none of them restore a
                    # tunnel, and continuing would play with the real IP exposed.
                    try:
                        bot.append_issue(
                            dev_id, "vpn_change_server_failed",
                            f"task-runtime recovery failed; refusing to continue "
                            f"without VPN (reason={cs_reason}, task={task_key})",
                            fn="device_worker", phase="task_loop")
                    except Exception:
                        pass
                    _log("✗ VPN unrecoverable — failing device (will not play "
                         "without VPN)", "err")
                    _finalize(ok=False, result="vpn_change_server failed")
                    return

                # Server change reported success — confirm tun0 before resuming.
                try:
                    _tun_ok = bool(bot.vpn_activity(dev_id))
                except Exception:
                    _tun_ok = False
                if not _tun_ok:
                    dlog.error("── task loop ── vpn_change_server returned OK but "
                               "tun0 is still down — refusing to continue")
                    try:
                        bot.append_issue(
                            dev_id, "vpn_change_server_failed",
                            "server change reported success but tun0 is down; "
                            "refusing to continue without VPN",
                            fn="device_worker", phase="task_loop")
                    except Exception:
                        pass
                    _log("✗ VPN still down after server change — failing device", "err")
                    _finalize(ok=False, result="vpn_change_server failed")
                    return

                _restart_target_app_guard(guard, 3)
                guard.set_target_app_opened()
                dlog.info("── task loop ── Opening TargetApp after server change")
                if not bot._ensure_vpn_prepare_target_app(dev_id, dlog, context="task loop after VPN server change"):
                    dlog.error("── task loop ── VPN gate failed — cannot open TargetApp after server change")
                    _finalize(ok=False, result="vpn_gate_failed_task_loop")
                    return
                if not bot.open_target_app(dev_id):
                    dlog.error("── task loop ── open_target_app failed after VPN server change")
                    _finalize(ok=False, result="target_app_open_failed_after_vpn_change")
                    return
                # Wait for loading to clear then target app main
                t_wait         = time.time()
                _load_gone_tl  = None
                reached        = False
                while time.time() - t_wait < 180.0:
                    _img_tl = bot.get_screenshot(dev_id)
                    if _img_tl is None:
                        time.sleep(2)
                        continue
                    if bot.is_on_page(dev_id, "connection issue", image=_img_tl):
                        try:
                            bot.click_in_bounding_box(
                                dev_id, *bot._get_page_button_rect("connection issue", "ok")
                            )
                            dlog.info("── task loop ── connection issue OK clicked")
                        except Exception:
                            pass
                        time.sleep(1)
                        continue
                    if bot.is_on_page(dev_id, "loading", image=_img_tl):
                        _load_gone_tl = None
                        time.sleep(2)
                        continue
                    else:
                        if _load_gone_tl is None:
                            _load_gone_tl = time.time()
                        elif time.time() - _load_gone_tl < 5.0:
                            time.sleep(1)
                            continue
                    if bot.is_on_page(dev_id, "target app main", image=_img_tl):
                        reached = True
                        break
                    time.sleep(2)

                if not reached:
                    dlog.error("── task loop ── main screen not reached after vpn_down")
                    _finalize(ok=False, result="main screen not reached after vpn_down")
                    return
                dlog.info("── task loop ── main screen confirmed — retrying current task")
                _log("✓ VPN recovered — retrying task", "info")
                # Don't advance task_idx — retry current task
                continue

            # Unknown result — fatal
            dlog.error(f"── {task_key} ── RESULT: failed ({result})")
            _log(f"✗ {task_key} failed: {result}", "err")
            _finalize(ok=False, result=result)
            return

        # ── End-of-run summary ─────────────────────────────────────────────────
        summary_parts = []
        for tk in task_keys:
            td_s   = task_defs.get(tk, {})
            s_attr = td_s.get("status_attr") if td_s else None
            s_dict = getattr(bot, s_attr, {}) if s_attr else {}
            val    = s_dict.get(dev_id, "?")
            summary_parts.append(f"{tk}={val}")
        dlog.info(f"── RUN COMPLETE ── {' | '.join(summary_parts)}")

        _finalize(ok=True, result="done")

    except SystemExit:
        _finalize(ok=False, result="stopped")
    except Exception as exc:
        dlog.error(_tb.format_exc())
        _log(f"Exception: {type(exc).__name__}: {exc}", "err")
        _finalize(ok=False, result=f"{type(exc).__name__}: {exc}")
    finally:
        # Cleanup now lives entirely in _finalize(), which every exit path calls
        # and which is idempotent. This safety net only fires if a path somehow
        # left without finalizing — otherwise it is a no-op.
        if not _final_state["sent"]:
            dlog.warning("[WORKER-END] task loop exited without finalizing — "
                         "running cleanup safety net")
            _finalize(ok=False, result="worker exited without a result")


# ================== Sheets-driven main run ==================

def main():
    if not os.path.exists(PAGES_JSON):
        logging.critical(f"pages.json not found at '{PAGES_JSON}'. Cannot detect any pages. Aborting.")
        print(f"CRITICAL: pages.json not found at '{PAGES_JSON}'. Script cannot run.")
        return

    ws, all_vals = _load_control_sheet()
    maybe_refresh_daily_statuses(ws, all_vals)

    if maybe_refresh_devices_from_conf(ws, all_vals, uncheck_trigger=True):
        print("✅ Refreshed device rows & checkboxes (B3). No tasks executed this run.")
        print("Hint: B3 was TRUE (InputNames). Unticked it for next run.")
        return

    cfg        = read_control_config(ws, all_vals)
    start_from = cfg["start_from"]
    rows       = cfg["rows"]
    run_d_col  = cfg.get("run_d_col")
    id_to_row  = {r["device_id"]: r["row_index"] for r in rows}

    global _vip_collect_status, _device_type_map, _device_friendly
    _vip_collect_status = {r["device_id"]: r.get("vip_collect_status", "") for r in rows}
    _device_type_map    = {r["device_id"]: r["device_type"].strip().lower() for r in rows}
    _device_friendly    = {r["device_id"]: r["friendly"] for r in rows}
    print(f"[main] VipCollect statuses loaded: {_vip_collect_status}")
    print(f"[main] Device type map loaded: {_device_type_map}")

    if not rows:
        print("No device rows configured in Control sheet. Nothing to do.")
        return

    # main() is a startup/diagnostic entry point only. Task execution belongs to
    # the controller, which spawns device_worker per device; the old
    # perform_actions_for_device loop here was a SECOND task runner with its own
    # dispatch, and it went with the tasks it existed to run. Nothing replaces it
    # — running tasks from this module directly is deliberately no longer
    # possible.
    print(f"[main] Control sheet loaded: {len(rows)} device row(s). "
          f"start_from={start_from!r}")
    print("[main] No tasks are executed from main(); use the controller "
          "(controller_ui_v7.py) to run devices.")


if __name__ == "__main__":
    main()