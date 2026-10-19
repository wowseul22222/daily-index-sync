import os
import json
import time
import html
import hashlib
import re
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo

from curl_cffi import requests


# ============================================================
# DAILY INDEX SYNC
# 감지 대상:
# - 메가토크 (GV / 관객과의 대화 포함)
# - 무대인사
#
# 코엑스 지점번호: 1351
#
# 집중 감시 방식:
# - 메가토크/GV: +4~+21일만, 각 날짜 약 8초 주기
# - 무대인사: +7~+42일 중 수/토/일 + 대한민국 법정공휴일만
#   · +7~+21일은 GV lane과 함께 약 8초 주기
#   · +22~+42일은 약 15초 주기
# - 매시 00분/30분: +4~+21일 전체 날짜 추가점검
# - +0~+3일은 조회 제외, GV는 +22일 이후 제외
# - 2 workers 고정, 모든 API 요청 시작 간격 최소 1.0초
# - timeout은 새 세션으로 0.5초 뒤 1회 재시도 후 해당 날짜/소스만 실패 처리
# - 실제 403/429/503 또는 'Workload is so high'만 전역 과부하 보호
# - 정상 감시는 10분마다 💚 heartbeat 요약
# ============================================================

BRANCH_NO = "1351"
BRANCH_NAME = "메가박스 코엑스"

DAYS = 43
WORKERS = 2
REQUEST_GAP = 1.0
OVERLOAD_GAP_STEPS = (2.0, 4.0, 8.0)
OVERLOAD_COOLDOWN_STEPS = (60.0, 120.0, 300.0)
OVERLOAD_RECOVERY_CYCLES = 10

# 네트워크 timeout은 서버 과부하와 분리한다.
SCHEDULE_TIMEOUT = 7.0
MAIN_PAGE_TIMEOUT = 4.0
CONNECTION_RETRY_DELAY = 0.5
TRUE_OVERLOAD_STATUSES = {403, 429, 503}
TRANSIENT_HTTP_STATUSES = {500, 502, 504}

# GitHub Actions에서 RUN_SECONDS로 실행 시간을 지정한다.
RUN_SECONDS = int(os.environ.get("RUN_SECONDS", "19200"))

KST = ZoneInfo("Asia/Seoul")

SCHEDULE_API = (
    "https://www.megabox.co.kr/"
    "on/oh/ohc/Brch/schedulePage.do"
)

STATE_FILE = "cache_index.json"
STATUS_FILE = "cache_snapshot.json"
BASELINE_FILE = ".cache_ready"
ERROR_ALERT_STATE_FILE = "cache_notice.json"
HEARTBEAT_INTERVAL = 600.0  # 10분마다 요약 로그
ERROR_ALERT_COOLDOWN_SECONDS = 600

# 집중 감시 주기
GV_START_OFFSET = 4
GV_END_OFFSET = 21
GV_FAST_INTERVAL = 8.0

STAGE_START_OFFSET = 7
STAGE_END_OFFSET = 42
STAGE_FAR_INTERVAL = 15.0
# 구형 별도 stage-lane 함수 호환용. 현재 main에서는 별도 lane을 사용하지 않는다.
STAGE_FAST_INTERVAL = STAGE_FAR_INTERVAL
STAGE_FAST_WEEKDAYS = {2, 5, 6}  # datetime.weekday(): 월=0 ... 일=6

MAX_DUE_DATES_PER_BATCH = 2

# 정각/30분 추가점검: +4~+21일 전체
SAFETY_SCAN_START_OFFSET = 4
SAFETY_SCAN_END_OFFSET = 21
SAFETY_SCAN_EVERY_MINUTES = 30

# 최초 baseline에서 Discord 실제 회차 확인용 영화 최대 3편
INITIAL_CONFIRM_LIMIT = 3

# 2026~2027 대한민국 법정공휴일/대체공휴일.
# 현재 43일 창에서 수/토/일 외 공휴일도 무대인사 20초 빠른 검사 대상으로 포함한다.
KOREA_PUBLIC_HOLIDAYS = {
    # 2026
    "2026-01-01",
    "2026-02-16", "2026-02-17", "2026-02-18",
    "2026-03-01", "2026-03-02",
    "2026-05-05", "2026-05-24", "2026-05-25",
    "2026-06-03", "2026-06-06", "2026-07-17",
    "2026-08-15", "2026-08-17",
    "2026-09-24", "2026-09-25", "2026-09-26",
    "2026-10-03", "2026-10-05", "2026-10-09",
    "2026-12-25",
    # 2027
    "2027-01-01",
    "2027-02-06", "2027-02-07", "2027-02-08", "2027-02-09",
    "2027-03-01",
    "2027-05-05", "2027-05-13",
    "2027-06-06", "2027-07-17", "2027-07-19",
    "2027-08-15", "2027-08-16",
    "2027-09-14", "2027-09-15", "2027-09-16",
    "2027-10-03", "2027-10-04", "2027-10-09", "2027-10-11",
    "2027-12-25", "2027-12-27",
}

# 기존 baseline과 구분. 이번 배포에서만 새 baseline을 만든다.
BASELINE_SCHEMA = "MEGABOX_COEX_V4_STAGE_FAST_SCREENSHOT_ALERT_20260911"

# Credentials are supplied only through GitHub Actions secrets.
NOTICE_ENDPOINT = os.environ.get("NOTICE_ENDPOINT", "").strip()
NOTICE_TARGET = os.environ.get("NOTICE_TARGET", "").strip()

HEADERS = {
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "ko-KR,ko;q=0.9,en-US;q=0.8",
    "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
    "Referer": (
        "https://www.megabox.co.kr/"
        "theater/time?brchNo=1351"
    ),
    "Origin": "https://www.megabox.co.kr",
    "X-Requested-With": "XMLHttpRequest",
}

_thread_local = threading.local()
_rate_lock = threading.Lock()
_next_request_time = 0.0
_adaptive_lock = threading.Lock()
_active_request_gap = REQUEST_GAP
_overload_until = 0.0
_overload_events = 0
_overload_level = 0
_clean_cycle_streak = 0
_cycle_abort_event = threading.Event()
_error_alert_lock = threading.Lock()


# ============================================================
# Time
# ============================================================

def now_kst():
    return datetime.now(KST)


def make_dates():
    """기준/인덱스용 오늘~+42일 전체 날짜."""
    today = now_kst()
    return [
        (today + timedelta(days=i)).strftime("%Y%m%d")
        for i in range(DAYS)
    ]


def offset_for_date(date):
    try:
        target = datetime.strptime(date, "%Y%m%d").date()
    except Exception:
        return None
    return (target - now_kst().date()).days


def is_stage_calendar_date(date):
    """무대인사 요일 조건: 수/토/일 또는 대한민국 법정공휴일."""
    try:
        target = datetime.strptime(date, "%Y%m%d").date()
    except Exception:
        return False

    hyphen = target.strftime("%Y-%m-%d")
    return (
        target.weekday() in STAGE_FAST_WEEKDAYS
        or hyphen in KOREA_PUBLIC_HOLIDAYS
    )


def is_gv_target_date(date):
    offset = offset_for_date(date)
    return offset is not None and GV_START_OFFSET <= offset <= GV_END_OFFSET


def is_stage_target_date(date):
    offset = offset_for_date(date)
    return (
        offset is not None
        and STAGE_START_OFFSET <= offset <= STAGE_END_OFFSET
        and is_stage_calendar_date(date)
    )


def is_target_event_for_date(date, event_type):
    if event_type == "메가토크":
        return is_gv_target_date(date)
    if event_type == "무대인사":
        return is_stage_target_date(date)
    return False


def make_monitor_dates():
    """GV(+4~+21)와 무대인사(+7~+42 수/토/일/공휴일)의 합집합."""
    return [
        date for date in make_dates()
        if is_gv_target_date(date) or is_stage_target_date(date)
    ]


def make_stage_fast_dates(start_offset=STAGE_START_OFFSET, end_offset=STAGE_END_OFFSET):
    """호환용: 지정 범위 안의 무대인사 대상 날짜만 반환."""
    today = now_kst().date()
    result = []
    for offset in range(start_offset, end_offset + 1):
        date = (today + timedelta(days=offset)).strftime("%Y%m%d")
        if is_stage_target_date(date):
            result.append(date)
    return result


def make_safety_scan_dates():
    """매시 00/30에는 +4~+21일 전체를 한 번 더 확인."""
    today = now_kst().date()
    return [
        (today + timedelta(days=offset)).strftime("%Y%m%d")
        for offset in range(SAFETY_SCAN_START_OFFSET, SAFETY_SCAN_END_OFFSET + 1)
    ]


def next_halfhour_boundary(dt):
    """Return the next KST :00 or :30 boundary strictly after dt."""
    base = dt.replace(second=0, microsecond=0)
    if dt.minute < 30:
        return base.replace(minute=30)
    return base.replace(minute=0) + timedelta(hours=1)


def pretty_date(date):
    dt = datetime.strptime(date, "%Y%m%d")
    weekdays = ["월", "화", "수", "목", "금", "토", "일"]
    return f"{dt:%Y.%m.%d}({weekdays[dt.weekday()]})"


# ============================================================
# Discord / error notification
# ============================================================

def send_notice(message):
    payload = {
        "content": message,
        "flags": 4,
        "allowed_mentions": {
            "parse": [],
            "users": [NOTICE_TARGET],
        },
    }

    try:
        response = requests.post(
            NOTICE_ENDPOINT,
            json=payload,
            impersonate="chrome",
            timeout=15,
        )
        response.raise_for_status()
        print("DISCORD SENT:", response.status_code)
        return True
    except Exception as e:
        # Discord 자체가 실패한 경우 같은 Discord로 재귀 알림하지 않는다.
        print("DISCORD ERROR:", repr(e))
        return False


def _load_error_alert_state():
    try:
        if not os.path.exists(ERROR_ALERT_STATE_FILE):
            return {}
        with open(ERROR_ALERT_STATE_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def _save_error_alert_state(state):
    try:
        temp = ERROR_ALERT_STATE_FILE + ".tmp"
        with open(temp, "w", encoding="utf-8") as f:
            json.dump(state, f, ensure_ascii=False, indent=2, sort_keys=True)
        os.replace(temp, ERROR_ALERT_STATE_FILE)
    except Exception as e:
        print("ERROR ALERT STATE SAVE ERROR:", repr(e))


def notify_error(scope, error=None, details="", dedupe_key=None):
    """동일 계열 오류는 10분 동안 Discord 중복 억제한다."""
    error_text = ""
    if error is not None:
        if isinstance(error, BaseException):
            error_text = f"{type(error).__name__}: {error}"
        else:
            error_text = str(error)

    key = dedupe_key or f"{scope}|{error_text}"
    now = time.time()

    with _error_alert_lock:
        state = _load_error_alert_state()
        previous = float(state.get(key, 0) or 0)
        if now - previous < ERROR_ALERT_COOLDOWN_SECONDS:
            print(f"오류 Discord 중복 억제: {scope}")
            return False

        lines = [
            f"<@{NOTICE_TARGET}>",
            f"**❌ {BRANCH_NAME} 감시 오류**",
            f"🔧 {scope}",
        ]
        if error_text:
            lines.append(f"⚠️ {error_text}")
        if details:
            lines.append(f"📝 {details}")
        lines.append("감시 프로세스는 가능한 범위에서 계속 진행합니다.")

        ok = send_notice("\n".join(lines)[:1950])
        if ok:
            state[key] = now
            _save_error_alert_state(state)
        return ok


# ============================================================
# State
# ============================================================

def load_seen():
    if not os.path.exists(STATE_FILE):
        return set()
    try:
        with open(STATE_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        return set(data) if isinstance(data, list) else set()
    except Exception as e:
        print("STATE LOAD ERROR:", repr(e))
        notify_error("seen 상태파일 읽기 실패", e, dedupe_key="seen-load")
        return set()


def save_seen(seen):
    try:
        temp = STATE_FILE + ".tmp"
        with open(temp, "w", encoding="utf-8") as f:
            json.dump(sorted(seen), f, ensure_ascii=False, indent=2)
        os.replace(temp, STATE_FILE)
    except Exception as e:
        print("STATE SAVE ERROR:", repr(e))
        notify_error("seen 상태파일 저장 실패", e, dedupe_key="seen-save")


def load_status():
    if not os.path.exists(STATUS_FILE):
        return {"shows": {}}
    try:
        with open(STATUS_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, dict):
            raise ValueError("status root is not dict")
        shows = data.get("shows")
        return {"shows": shows if isinstance(shows, dict) else {}}
    except Exception as e:
        print("STATUS LOAD ERROR:", repr(e))
        notify_error("회차 상태파일 읽기 실패", e, dedupe_key="status-load")
        return {"shows": {}}


def save_status(status):
    try:
        temp = STATUS_FILE + ".tmp"
        with open(temp, "w", encoding="utf-8") as f:
            json.dump(status, f, ensure_ascii=False, indent=2, sort_keys=True)
        os.replace(temp, STATUS_FILE)
    except Exception as e:
        print("STATUS SAVE ERROR:", repr(e))
        notify_error("회차 상태파일 저장 실패", e, dedupe_key="status-save")


def baseline_done():
    if not os.path.exists(BASELINE_FILE):
        return False
    try:
        with open(BASELINE_FILE, "r", encoding="utf-8") as f:
            value = f.read().strip()
        return value == BASELINE_SCHEMA
    except Exception as e:
        notify_error("baseline 파일 읽기 실패", e, dedupe_key="baseline-load")
        return False


def mark_baseline_done():
    try:
        with open(BASELINE_FILE, "w", encoding="utf-8") as f:
            f.write(BASELINE_SCHEMA)
        print("BASELINE MARKER CREATED")
    except Exception as e:
        notify_error("baseline 파일 저장 실패", e, dedupe_key="baseline-save")
        raise


# ============================================================
# API / rate helpers
# ============================================================

def get_session():
    session = getattr(_thread_local, "session", None)
    if session is None:
        session = requests.Session(impersonate="chrome")
        _thread_local.session = session
    return session


def reset_thread_session():
    try:
        _thread_local.session = None
    except Exception:
        pass


def reset_rate_clock():
    global _next_request_time
    with _rate_lock:
        _next_request_time = time.monotonic()


def current_request_gap():
    with _adaptive_lock:
        return _active_request_gap


def overload_event_count():
    with _adaptive_lock:
        return _overload_events


def cycle_aborted():
    return _cycle_abort_event.is_set()


def reset_cycle_abort():
    _cycle_abort_event.clear()


def register_overload(reason):
    global _active_request_gap, _overload_until, _overload_events
    global _overload_level, _clean_cycle_streak

    now = time.monotonic()
    should_log = False
    cooldown = 0.0

    # 실제 과부하가 감지되면 현재 조회 묶음은 중단한다.
    _cycle_abort_event.set()

    with _adaptive_lock:
        _overload_events += 1
        _clean_cycle_streak = 0

        # 같은 과부하 파동에서 worker들이 거의 동시에 실패해도
        # 단계/로그는 한 번만 올린다.
        if now >= _overload_until:
            _overload_level = min(
                len(OVERLOAD_GAP_STEPS),
                _overload_level + 1,
            )
            index = _overload_level - 1
            _active_request_gap = OVERLOAD_GAP_STEPS[index]
            cooldown = OVERLOAD_COOLDOWN_STEPS[index]
            _overload_until = now + cooldown
            should_log = True

    if should_log:
        print(
            "⚠️ 메가박스 서버 과부하 감지 -> "
            f"현재 조회 묶음 즉시 중단 / "
            f"{cooldown:.0f}초 휴식 / "
            f"재시도 간격 {current_request_gap():.2f}s | "
            f"원인: {reason}"
        )


def note_clean_cycle():
    global _active_request_gap, _clean_cycle_streak, _overload_level

    changed = None
    with _adaptive_lock:
        _clean_cycle_streak += 1
        if (
            _clean_cycle_streak >= OVERLOAD_RECOVERY_CYCLES
            and _overload_level > 0
        ):
            _overload_level -= 1
            if _overload_level == 0:
                _active_request_gap = REQUEST_GAP
            else:
                _active_request_gap = OVERLOAD_GAP_STEPS[
                    _overload_level - 1
                ]
            _clean_cycle_streak = 0
            changed = _active_request_gap

    if changed is not None:
        print(
            "✅ 과부하 없이 10사이클 완료 -> "
            f"요청간격 {changed:.2f}s로 한 단계 복구"
        )


def wait_rate_slot():
    global _next_request_time

    while True:
        if cycle_aborted():
            return False

        with _adaptive_lock:
            overload_until = _overload_until
            gap = _active_request_gap

        with _rate_lock:
            now = time.monotonic()
            target = max(_next_request_time, overload_until)

            if now < target:
                sleep_for = min(target - now, 0.25)
            else:
                _next_request_time = now + gap
                return True

        time.sleep(sleep_for)


def extract_movie_form_list(data):
    mega_map = data.get("megaMap") or {}
    rows = mega_map.get("movieFormList")

    if isinstance(rows, list):
        return rows

    for value in data.values():
        if not isinstance(value, dict):
            continue
        rows = value.get("movieFormList")
        if isinstance(rows, list):
            return rows

    return []


def request_schedule(date):
    params = {
        "masterType": "brch",
        "detailType": "movie",
        "brchNo": BRANCH_NO,
        "firstAt": "N",
        "brchNo1": BRANCH_NO,
        "spclbYn1": "N",
        "crtDe": now_kst().strftime("%Y%m%d"),
        "playDe": date,
    }
    label = "GENERAL"

    # timeout/연결 오류는 새 세션으로 0.5초 뒤 딱 1회 재시도한다.
    attempts = 2

    for attempt in range(1, attempts + 1):
        if cycle_aborted():
            return None, True, f"{label} {date} CYCLE ABORTED"

        if not wait_rate_slot():
            return None, True, f"{label} {date} CYCLE ABORTED"

        started = time.monotonic()
        session = get_session()

        try:
            response = session.post(
                SCHEDULE_API,
                data=params,
                headers=HEADERS,
                timeout=SCHEDULE_TIMEOUT,
            )
        except Exception as e:
            error_text = repr(e)
            lower = error_text.lower()
            name = type(e).__name__.lower()

            reset_thread_session()

            is_timeout = (
                "timeout" in name
                or "timed out" in lower
                or "curl: (28)" in lower
            )

            if attempt < attempts:
                if is_timeout:
                    print(
                        f"↻ {label} {date} timeout -> "
                        f"{CONNECTION_RETRY_DELAY:.1f}초 후 새 세션으로 1회 즉시 재시도"
                    )
                else:
                    print(
                        f"↻ {label} {date} 연결 오류 -> "
                        f"{CONNECTION_RETRY_DELAY:.1f}초 후 새 세션으로 1회 즉시 재시도"
                    )
                time.sleep(CONNECTION_RETRY_DELAY)
                continue

            if is_timeout:
                # 개별 날짜 timeout은 여기서 Discord를 보내지 않는다.
                # 호출한 묶음(GENERAL / 무대인사 빠른조회 / 00·30 추가점검)이
                # failed_dates를 모아 한 번만 오류 알림을 보내도록 한다.
                print(
                    f"❌ {label} {date} timeout -> 재시도 후 실패 "
                    "(묶음 오류 알림에서 처리)"
                )
                return None, True, f"{label} {date} TIMEOUT"

            notify_error(
                "메가박스 API 연결 오류",
                e,
                details=f"{label} / {date} / 재시도 후 실패",
                dedupe_key="schedule-connection-GENERAL",
            )
            return None, True, f"{label} {date} REQUEST ERROR: {error_text}"

        elapsed = time.monotonic() - started
        status = response.status_code
        body = response.text or ""
        body_lower = body.lower()

        # 실제 과부하 신호만 전역 자동완화.
        if (
            status in TRUE_OVERLOAD_STATUSES
            or "workload is so high" in body_lower
        ):
            reason = f"{label} {date} HTTP {status}"
            if "workload is so high" in body_lower:
                reason += " / Workload is so high"
            register_overload(reason)
            notify_error(
                "메가박스 실제 과부하 감지",
                details=reason,
                dedupe_key=f"overload-{status}",
            )
            return None, True, reason

        # 500/502/504 등 일시 오류는 과부하로 보지 않는다.
        if status in TRANSIENT_HTTP_STATUSES:
            if attempt < attempts:
                reset_thread_session()
                time.sleep(CONNECTION_RETRY_DELAY)
                continue
            notify_error(
                "메가박스 API 일시 HTTP 오류",
                details=f"{label} / {date} / HTTP {status}",
                dedupe_key=f"schedule-transient-{status}",
            )
            return None, True, f"{label} {date} HTTP {status}"

        if status >= 400:
            notify_error(
                "메가박스 API HTTP 오류",
                details=f"{label} / {date} / HTTP {status}",
                dedupe_key=f"schedule-http-{status}",
            )
            return None, True, f"{label} {date} HTTP {status}"

        try:
            data = response.json()
        except Exception as e:
            # JSON 오류는 서버 과부하로 승격하지 않는다.
            if attempt < attempts:
                reset_thread_session()
                time.sleep(CONNECTION_RETRY_DELAY)
                continue
            notify_error(
                "메가박스 API JSON 파싱 오류",
                e,
                details=f"{label} / {date} / HTTP {status}",
                dedupe_key="schedule-json-GENERAL",
            )
            return None, True, f"{label} {date} JSON ERROR"

        rows = extract_movie_form_list(data)
        return rows, False, f"{label} {date} HTTP {status} {elapsed:.2f}s ROWS={len(rows)}"

    return None, True, f"{label} {date} UNKNOWN ERROR"


# ============================================================
# Row helpers / classification
# ============================================================

def all_text(row):
    values = []
    for key, value in row.items():
        if value is None:
            continue
        values.append(f"{key}={value}")
    return " ".join(values)


def is_stage(row):
    text = all_text(row)
    return "무대인사" in text or "舞台挨拶" in text


def is_megatalk(row):
    text = all_text(row)
    compact = re.sub(r"\s+", "", text)
    upper = text.upper()

    if "메가토크" in compact:
        return True
    if "관객과의대화" in compact:
        return True
    if re.search(r"(?<![A-Z0-9])GV(?![A-Z0-9])", upper):
        return True
    return False


def get_target_type(row):
    if is_stage(row):
        return "무대인사"
    if is_megatalk(row):
        return "메가토크"
    return None


# ============================================================
# Event fields
# ============================================================

def clean_text(value):
    return html.unescape(str(value or "")).strip()


def clean_movie_title(value):
    """API 영화명 앞의 [무대인사]/[메가토크]/[GV] 같은 행사표시만 제거한다."""
    title = clean_text(value)

    prefix_patterns = (
        r"^\s*\[(?:무대인사|메가토크|GV|관객과의\s*대화)\]\s*",
        r"^\s*\((?:무대인사|메가토크|GV|관객과의\s*대화)\)\s*",
        r"^\s*(?:무대인사|메가토크|GV|관객과의\s*대화)\s*[:：|\-·]?\s+",
    )

    changed = True
    while changed:
        changed = False
        for pattern in prefix_patterns:
            cleaned = re.sub(pattern, "", title, flags=re.IGNORECASE)
            if cleaned != title:
                title = cleaned.strip()
                changed = True

    return title


def get_movie(row):
    return clean_movie_title(row.get("movieNm") or row.get("movNm") or "")


def get_start(row):
    return clean_text(
        row.get("playStartTime")
        or row.get("scnsrtTm")
        or ""
    )


def get_end(row):
    return clean_text(
        row.get("playEndTime")
        or row.get("scnsEndTime")
        or ""
    )


def get_screen(row):
    return clean_text(
        row.get("theabExpoNm")
        or row.get("theabNm")
        or row.get("screenNm")
        or row.get("scnsNm")
        or ""
    )


def get_schedule_no(row):
    return clean_text(
        row.get("playSchdlNo")
        or row.get("playScheduleNo")
        or ""
    )


def make_booking_link(row):
    schedule_no = get_schedule_no(row)
    if schedule_no:
        return (
            "https://m.megabox.co.kr/"
            "booking/seat"
            f"?playSchdlNo={schedule_no}"
        )

    date = clean_text(row.get("playDe") or "")
    if not date:
        date = now_kst().strftime("%Y%m%d")

    return (
        "https://www.megabox.co.kr/"
        "theater/time"
        f"?brchNo={BRANCH_NO}"
        f"&playDe={date}"
    )


def event_key(date, row, event_type):
    schedule_no = get_schedule_no(row)

    if schedule_no:
        return "|".join([
            BRANCH_NO,
            date,
            schedule_no,
            event_type,
        ])

    return "|".join([
        BRANCH_NO,
        date,
        clean_text(row.get("movieNo") or ""),
        get_movie(row),
        get_start(row),
        get_end(row),
        get_screen(row),
        event_type,
    ])


def to_int(value):
    try:
        if value is None or value == "":
            return None
        return int(str(value).replace(",", "").strip())
    except Exception:
        return None


def get_rest_seat(row):
    for key in (
        "restSeatCnt",
        "restSeatCount",
        "remainSeatCnt",
        "remainSeatCount",
    ):
        value = to_int(row.get(key))
        if value is not None:
            return value
    return None


def get_total_seat(row):
    for key in (
        "totSeatCnt",
        "totSeatCount",
        "theabSeatCnt",
        "totalSeatCnt",
    ):
        value = to_int(row.get(key))
        if value is not None:
            return value
    return None


def booking_status(event):
    # 실제 API 텍스트에 준비중 문구가 직접 있을 때만 PREPARING으로 확정한다.
    if event.get("preparing_explicit"):
        return "PREPARING"

    if event.get("sold_out_explicit"):
        return "SOLD_OUT"

    rest = event.get("rest_seat")
    if isinstance(rest, int):
        return "SOLD_OUT" if rest <= 0 else "OPEN"

    return "UNKNOWN"


def normalize_event(date, row, event_type):
    row_text = all_text(row)
    row_upper = row_text.upper()
    row_compact = re.sub(r"\s+", "", row_text)
    preparing_explicit = (
        "상영준비중" in row_compact
        or "예매준비중" in row_compact
    )
    sold_out_explicit = (
        "매진" in row_text
        or "SOLD_OUT" in row_upper
        or "SOLDOUT" in row_upper
    )

    return {
        "date": date,
        "type": event_type,
        "movie": get_movie(row),
        "start": get_start(row),
        "end": get_end(row),
        "screen": get_screen(row),
        "schedule_no": get_schedule_no(row),
        "link": make_booking_link(row),
        "rest_seat": get_rest_seat(row),
        "total_seat": get_total_seat(row),
        "preparing_explicit": preparing_explicit,
        "sold_out_explicit": sold_out_explicit,
    }


# ============================================================
# Collect - 43 days / 2 workers / adaptive overload protection
# ============================================================

def collect_date(index, date):
    events = {}
    rows, problem, log_text = request_schedule(date)

    if rows is None:
        rows = []

    for row in rows:
        event_type = get_target_type(row)
        if event_type not in ("메가토크", "무대인사"):
            continue
        if not is_target_event_for_date(date, event_type):
            continue

        key = event_key(date, row, event_type)
        events[key] = normalize_event(date, row, event_type)

    return {
        "index": index,
        "date": date,
        "events": events,
        "problem": problem,
        "logs": [log_text],
    }


def collect_all_days(progress=False):
    all_events = {}
    failed_dates = []
    results = []
    dates = make_dates()

    reset_cycle_abort()
    reset_rate_clock()

    with ThreadPoolExecutor(max_workers=WORKERS) as executor:
        futures = [
            executor.submit(collect_date, index, date)
            for index, date in enumerate(dates, start=1)
        ]

        completed = 0
        for future in as_completed(futures):
            try:
                results.append(future.result())
            except Exception as e:
                print("DATE FUTURE ERROR:", repr(e))
            finally:
                completed += 1
                if progress and completed in {10, 20, 30, 40, DAYS}:
                    print(
                        f"⏳ 기준값 진행: {completed}/{DAYS} 날짜 처리 완료"
                    )

    results.sort(key=lambda item: item["index"])

    returned_dates = {item["date"] for item in results}
    for date in dates:
        if date not in returned_dates:
            failed_dates.append(date)

    error_examples = []
    for item in results:
        all_events.update(item["events"])

        if item["problem"]:
            failed_dates.append(item["date"])
            if len(error_examples) < 3:
                error_examples.append(
                    f"{item['date']}: " + " | ".join(item["logs"])
                )

    if error_examples:
        print(
            "⚠️ API 오류 예시(최대 3건): "
            + " || ".join(error_examples)
        )

    failed_dates = sorted(set(failed_dates))
    return all_events, failed_dates



def _semantic_event_identity(event):
    """
    메가박스 내부 playSchdlNo가 재발급되어도 같은 실제 회차로 본다.
    사용자에게 보이는 안정적인 회차 기준:
    날짜 + 종류 + 영화 + 시작/종료시간 + 상영관
    """
    return (
        clean_text(event.get("date", "")),
        clean_text(event.get("type", "")),
        clean_text(event.get("movie", "")),
        clean_text(event.get("start", "")).replace(":", ""),
        clean_text(event.get("end", "")).replace(":", ""),
        clean_text(event.get("screen", "")),
    )


def _find_semantic_previous(event, show_state):
    target = _semantic_event_identity(event)

    for old_key, record_item in show_state.items():
        if not isinstance(record_item, dict):
            continue
        if _semantic_event_identity(record_item) == target:
            return old_key, record_item

    return None, None


def _legacy_reconcile_semantic_seen_unused(events, seen, show_state):
    """
    playSchdlNo만 바뀐 기존 회차를 새 회차로 오판하지 않도록
    현재 key를 seen에 승계한다.
    """
    inherited = 0

    for key, event in events.items():
        if key in seen:
            continue

        old_key, old_record = _find_semantic_previous(
            event,
            show_state,
        )

        if old_record is not None:
            seen.add(key)
            inherited += 1

    if inherited:
        print(
            f"♻️ 내부 회차번호 변경 {inherited}건 기존 회차로 승계 "
            "(중복 Discord 알림 억제)"
        )

    return inherited


# ============================================================
# Discord / booking-state transitions
# ============================================================

def state_record(event, status=None):
    current_status = status or booking_status(event)
    return {
        "status": current_status,
        "date": event.get("date", ""),
        "type": event.get("type", ""),
        "movie": event.get("movie", ""),
        "start": event.get("start", ""),
        "end": event.get("end", ""),
        "screen": event.get("screen", ""),
        "schedule_no": event.get("schedule_no", ""),
        "link": event.get("link", ""),
        "rest_seat": event.get("rest_seat"),
        "total_seat": event.get("total_seat"),
        "preparing_explicit": bool(event.get("preparing_explicit")),
        "sold_out_explicit": bool(event.get("sold_out_explicit")),
        "updated_at_kst": now_kst().isoformat(timespec="seconds"),
    }


def display_type_name(event_type):
    return event_type


def _mega_movie_key(event):
    return clean_text(event.get("movie", "")).casefold()


def alert_time_range(event):
    start = clean_text(event.get("start", ""))
    end = clean_text(event.get("end", ""))
    if start and end:
        return f"{start}–{end}"
    return start or end or "시간 정보 없음"


def alert_line(event):
    movie = event.get("movie") or "영화명 확인 필요"
    link = event.get("link") or (
        f"https://www.megabox.co.kr/theater/time?brchNo={BRANCH_NO}"
    )
    screen = event.get("screen") or "상영관 정보 없음"
    # 링크는 영화 이름에만 건다. 롯데 최종 알림과 같은 형식.
    return f"🎟 {alert_time_range(event)} · [{movie}]({link}) · {screen}"


def alert_detected_text(event_type, status):
    kind = display_type_name(event_type)
    if status == "DETECTED":
        return f"🔎 {kind}가 감지됐습니다"
    if status == "PREPARING":
        return f"⏳ {kind} 상영준비중이 감지됐습니다"
    if status == "OPEN":
        return f"🚨 {kind} 예매가 오픈됐습니다"
    return f"🔎 {kind} 상태가 변경됐습니다"


def _mega_display_group(events, trigger_event, alert_status):
    """알림 하나 = 날짜 1개 + 영화 1편 + 종류 1개. 해당 회차는 모두 표시."""
    date = trigger_event.get("date", "")
    event_type = trigger_event.get("type", "")
    movie_key = _mega_movie_key(trigger_event)
    result = []

    for event in events.values():
        if event.get("date", "") != date:
            continue
        if event.get("type", "") != event_type:
            continue
        if _mega_movie_key(event) != movie_key:
            continue

        current = booking_status(event)
        if alert_status == "PREPARING" and current != "PREPARING":
            continue
        if alert_status == "OPEN" and current != "OPEN":
            continue
        if alert_status == "DETECTED" and current == "SOLD_OUT":
            continue
        result.append(event)

    return result or [trigger_event]


def send_alert_group(events, status):
    """알림 하나 = 날짜 1개 + 영화 1편 + 행사종류 1개."""
    if not events:
        return 0

    events = sorted(
        events,
        key=lambda event: (
            event.get("start", ""),
            event.get("screen", ""),
        ),
    )
    first = events[0]
    event_type = first.get("type", "")
    kind = display_type_name(event_type)

    # 사용자가 지정한 롯데 최종 형식과 동일:
    # @멘션
    # 🔎/⏳/🚨 ...
    # 🎬 극장 · 행사종류
    # 📅 날짜
    # 🎟 시간 · [영화명](링크) · 상영관
    header = [
        f"<@{NOTICE_TARGET}>",
        alert_detected_text(event_type, status),
        f"🎬 {BRANCH_NAME} · {kind}",
        f"📅 {pretty_date(first.get('date', ''))}",
    ]

    current = list(header)
    messages_sent = 0
    for event in events:
        line = alert_line(event)
        candidate = "\n".join(current + [line])

        if len(candidate) > 1900 and len(current) > len(header):
            if send_notice("\n".join(current)):
                messages_sent += 1
            current = list(header)

        current.append(line)

    if len(current) > len(header):
        if send_notice("\n".join(current)):
            messages_sent += 1
        else:
            raise RuntimeError("Discord alert send failed")

    return messages_sent


def select_initial_confirmation_groups(events):
    """
    최초 baseline 확인도 실제 알림과 완전히 같은 형식으로 보낸다.
    한 메시지 = 날짜 1개 + 영화 1편 + 행사종류 1개.
    가능하면 서로 다른 영화 최대 3편을 선택한다.
    """
    grouped = {}
    for event in sorted(
        events.values(),
        key=lambda e: (
            e.get("date", ""),
            e.get("start", ""),
            e.get("movie", ""),
            e.get("type", ""),
        ),
    ):
        group_key = (
            event.get("date", ""),
            _mega_movie_key(event),
            event.get("type", ""),
        )
        grouped.setdefault(group_key, []).append(event)

    selected = []
    used_movies = set()

    for group_key, group in grouped.items():
        movie_key = group_key[1]
        if not movie_key or movie_key in used_movies:
            continue
        selected.append(group)
        used_movies.add(movie_key)
        if len(selected) >= INITIAL_CONFIRM_LIMIT:
            break

    return selected


def reconcile_semantic_seen(events, seen, show_state):
    """playSchdlNo만 바뀐 기존 회차는 새 회차로 알리지 않고 상태까지 승계."""
    inherited = 0
    for key, event in events.items():
        if key in seen and key in show_state:
            continue

        old_key, old_record = _find_semantic_previous(event, show_state)
        if old_record is None:
            continue

        seen.add(key)
        copied = state_record(event, old_record.get("status", "UNKNOWN"))
        show_state[key] = copied
        inherited += 1

    if inherited:
        print(
            f"♻️ 내부 회차번호 변경 {inherited}건 기존 회차로 승계 "
            "(중복 Discord 알림 억제)"
        )
    return inherited


def send_detected_events(events, seen, show_state):
    """API에 대상 회차가 처음 생긴 순간 1회 알림. 날짜+영화+종류 단위로 묶는다."""
    new_items = []
    for key, event in events.items():
        if key in seen:
            continue
        current = booking_status(event)
        if current == "SOLD_OUT":
            # 처음부터 매진인 새 회차는 사용자 알림 없이 기준만 기억.
            seen.add(key)
            show_state[key] = state_record(event, "SOLD_OUT")
            continue
        new_items.append((key, event))

    groups = {}
    for key, event in new_items:
        group_key = (
            event.get("date", ""),
            _mega_movie_key(event),
            event.get("type", ""),
        )
        groups.setdefault(group_key, []).append((key, event))

    sent = 0
    for group_key in sorted(groups):
        members = groups[group_key]
        first = members[0][1]
        display_events = _mega_display_group(events, first, "DETECTED")
        try:
            sent += send_alert_group(display_events, "DETECTED")
        except Exception as e:
            notify_error(
                "신규 회차 Discord 전송 실패",
                e,
                details=f"{first.get('date')} / {first.get('movie')} / {first.get('type')}",
                dedupe_key="discord-detected-send",
            )
            continue

        for key, event in members:
            seen.add(key)
            show_state[key] = state_record(event, "DETECTED")

    return sent


def process_state_transitions(events, show_state):
    """DETECTED -> PREPARING -> OPEN 전환. 매진/재오픈은 사용자 알림 없음."""
    candidates = []

    for key, event in events.items():
        current = booking_status(event)
        previous_record = show_state.get(key) or {}
        previous = previous_record.get("status")

        if current == "SOLD_OUT":
            show_state[key] = state_record(event, "SOLD_OUT")
            continue

        if current == "UNKNOWN":
            # 새 회차 선행감지(DETECTED)는 유지하고, 이미 확정된 상태도 되돌리지 않는다.
            show_state[key] = state_record(event, previous or "UNKNOWN")
            continue

        alert_status = None
        if current == "PREPARING":
            if previous in {None, "DETECTED", "UNKNOWN"}:
                alert_status = "PREPARING"
            elif previous in {"OPEN", "SOLD_OUT"}:
                # 이미 열렸거나 매진된 회차의 준비중 역행은 재알림하지 않는다.
                show_state[key] = state_record(event, previous)
                continue

        elif current == "OPEN":
            if previous in {None, "DETECTED", "UNKNOWN", "PREPARING"}:
                alert_status = "OPEN"
            elif previous == "SOLD_OUT":
                # 매진 -> OPEN = 취소표/재오픈. 사용자 알림 없음.
                show_state[key] = state_record(event, "OPEN")
                continue

        if alert_status:
            candidates.append((key, event, alert_status, previous))
        else:
            show_state[key] = state_record(event, previous or current)

    groups = {}
    for item in candidates:
        key, event, alert_status, previous = item
        group_key = (
            event.get("date", ""),
            _mega_movie_key(event),
            event.get("type", ""),
            alert_status,
        )
        groups.setdefault(group_key, []).append(item)

    sent = 0
    for group_key in sorted(groups):
        members = groups[group_key]
        first = members[0][1]
        alert_status = members[0][2]
        display_events = _mega_display_group(events, first, alert_status)

        try:
            sent += send_alert_group(display_events, alert_status)
        except Exception as e:
            notify_error(
                "상태변화 Discord 전송 실패",
                e,
                details=f"{first.get('date')} / {first.get('movie')} / {first.get('type')} / {alert_status}",
                dedupe_key=f"discord-state-{alert_status}",
            )
            continue

        for key, event, _status, previous in members:
            show_state[key] = state_record(event, alert_status)
            if alert_status == "PREPARING":
                label = "⏳ 상영준비중"
            elif previous == "PREPARING":
                label = "🚨 상영준비중 -> 예매 오픈"
            else:
                label = "🚨 예매 오픈"
            print(
                f"{label}: {display_type_name(event.get('type', ''))} / "
                f"{event.get('movie')} / {event.get('date')} {event.get('start')}"
            )

    return sent


# ============================================================
# Staggered 43-day scheduler
# GENERAL API 날짜별 분산 주기.
# ============================================================

def interval_for_date(date):
    """+4~+21일은 8초, 뒤쪽 무대인사 날짜(+22~+42)는 15초."""
    offset = offset_for_date(date)
    if offset is None:
        return STAGE_FAR_INTERVAL
    if GV_START_OFFSET <= offset <= GV_END_OFFSET:
        return GV_FAST_INTERVAL
    return STAGE_FAR_INTERVAL


def has_preparing_for_date(date, show_state):
    return any(
        isinstance(record, dict)
        and record.get("date") == date
        and record.get("status") == "PREPARING"
        and is_target_event_for_date(date, record.get("type", ""))
        for record in show_state.values()
    )


def effective_interval(date, offset=None, show_state=None):
    base = interval_for_date(date)
    if show_state is not None and has_preparing_for_date(date, show_state):
        return min(base, GV_FAST_INTERVAL)
    return base


def error_retry_interval(offset):
    # 실패한 날짜만 짧게 재확인. 전체 감시는 멈추지 않는다.
    if offset is not None and GV_START_OFFSET <= offset <= GV_END_OFFSET:
        return GV_FAST_INTERVAL
    return STAGE_FAR_INTERVAL


def build_due_schedule(show_state):
    """실제 감시 대상 날짜만 8초/15초 창 안에서 고르게 분산한다."""
    now = time.monotonic()
    groups = {}

    for date in make_monitor_dates():
        interval = effective_interval(date, show_state=show_state)
        groups.setdefault(interval, []).append(date)

    next_due = {}
    for interval, dates in groups.items():
        count = max(1, len(dates))
        for pos, date in enumerate(dates):
            next_due[date] = now + (interval * pos / count)

    return next_due


def collect_due_dates(dates):
    """현재 due인 날짜의 GENERAL 일정만 확인한다."""
    if not dates:
        return {}, []

    all_events = {}
    failed_dates = []
    results = []

    reset_cycle_abort()
    reset_rate_clock()

    with ThreadPoolExecutor(max_workers=WORKERS) as executor:
        futures = []
        full_dates = make_dates()
        index_map = {d: i + 1 for i, d in enumerate(full_dates)}

        for date in dates:
            futures.append(
                executor.submit(
                    collect_date,
                    index_map.get(date, 0),
                    date,
                )
            )

        for future in as_completed(futures):
            try:
                results.append(future.result())
            except Exception as e:
                print("DATE FUTURE ERROR:", repr(e))

    error_examples = []
    for item in results:
        # 성공한 GENERAL 응답의 이벤트는 즉시 감지에 사용.
        all_events.update(item.get("events", {}))

        if item.get("problem"):
            failed_dates.append(item.get("date", ""))
            if len(error_examples) < 2:
                error_examples.append(
                    f"{item.get('date', '')}: "
                    + " | ".join(item.get("logs", []))
                )

    returned_dates = {item.get("date") for item in results}
    for date in dates:
        if date not in returned_dates:
            failed_dates.append(date)

    failed_dates = sorted(set(d for d in failed_dates if d))

    if error_examples:
        print(
            "⚠️ API 오류 예시(최대 2건): "
            + " || ".join(error_examples)
        )

    return all_events, failed_dates



def collect_stage_date(index, date):
    """무대인사 빠른 lane: GENERAL 한 소스만 조회하고 무대인사만 반환."""
    events = {}
    rows, problem, log_text = request_schedule(date)
    if rows is None:
        rows = []
    for row in rows:
        if not is_stage(row):
            continue
        event_type = "무대인사"
        key = event_key(date, row, event_type)
        events[key] = normalize_event(date, row, event_type)
    return {
        "index": index,
        "date": date,
        "events": events,
        "problem": problem,
        "logs": [log_text],
    }


def collect_stage_dates(dates):
    if not dates:
        return {}, []

    all_events = {}
    failed_dates = []
    results = []
    reset_cycle_abort()
    reset_rate_clock()

    full_dates = make_dates()
    index_map = {date: index + 1 for index, date in enumerate(full_dates)}
    with ThreadPoolExecutor(max_workers=WORKERS) as executor:
        futures = [
            executor.submit(collect_stage_date, index_map.get(date, 0), date)
            for date in dates
        ]
        for future in as_completed(futures):
            try:
                results.append(future.result())
            except Exception as e:
                print("STAGE FUTURE ERROR:", repr(e))
                notify_error(
                    "무대인사 빠른검사 worker 오류",
                    e,
                    dedupe_key="stage-worker-error",
                )

    returned_dates = {item.get("date") for item in results}
    for date in dates:
        if date not in returned_dates:
            failed_dates.append(date)

    for item in results:
        all_events.update(item.get("events", {}))
        if item.get("problem"):
            failed_dates.append(item.get("date", ""))

    return all_events, sorted(set(date for date in failed_dates if date))


def build_stage_due_schedule():
    """수/토/일/공휴일 날짜들을 20초 창 안에 고르게 분산."""
    dates = make_stage_fast_dates(0, DAYS - 1)
    now = time.monotonic()
    count = max(1, len(dates))
    return {
        date: now + (STAGE_FAST_INTERVAL * index / count)
        for index, date in enumerate(dates)
    }


def state_count_cache(show_state):
    """heartbeat 표시용 시작 count cache."""
    valid_dates = set(make_monitor_dates())
    cache = {}

    for record in show_state.values():
        if not isinstance(record, dict):
            continue

        date = record.get("date")
        kind = record.get("type")
        if date not in valid_dates or kind not in {"메가토크", "무대인사"}:
            continue
        if not is_target_event_for_date(date, kind):
            continue

        bucket = cache.setdefault(
            date,
            {"메가토크": 0, "무대인사": 0},
        )
        bucket[kind] += 1

    return cache


def total_counts_from_cache(cache):
    total = {"메가토크": 0, "무대인사": 0}
    for counts in cache.values():
        for key in total:
            total[key] += counts.get(key, 0)
    return total


# ============================================================
# Diagnostics
# ============================================================

def count_events(events):
    counts = {
        "메가토크": 0,
        "무대인사": 0,
    }

    for event in events.values():
        event_type = event.get("type", "")
        if event_type in counts:
            counts[event_type] += 1

    return counts


def print_counts(events):
    counts = count_events(events)
    print("MEGATALK COUNT:", counts["메가토크"])
    print("무대인사 COUNT:", counts["무대인사"])


# ============================================================
# Main
# ============================================================

def main():
    program_started = time.monotonic()
    print("=" * 72)
    print("DAILY INDEX SYNC")
    print("=" * 72)
    print("BRANCH:", BRANCH_NAME)
    print("BRANCH NO:", BRANCH_NO)
    print("TARGET: 메가토크(GV·관객과의 대화 포함) / 무대인사")
    print("DATE RANGE: GV +4~+21 / 무대인사 +7~+42")
    print("GENERAL: 필요한 날짜만 집중 분산감시 / 2 workers")
    print("GV/MEGATALK: +4~+21일 / 약 8초")
    print("STAGE: +7~+42일 수/토/일/공휴일 / +7~+21 약 8초 / +22~+42 약 15초")
    print("00/30 EXTRA SCAN: +4~+21일 전체 / 2 workers")
    print("ALERT: 한 날짜 + 한 영화 + 한 행사종류 / 같은 날짜 해당 영화 회차 전부 표시")
    print("ALERT LINK: 영화 이름에만 예매 링크")
    print("STATE: 선행감지 -> 상영준비중(명시 문구) -> 예매오픈")
    print("SOLD OUT / REOPEN: 사용자 알림 없음 / 내부 상태만 저장")
    print(f"ERROR Discord 중복 억제: {ERROR_ALERT_COOLDOWN_SECONDS // 60}분")
    print("REQUEST START GAP:", f"{REQUEST_GAP:.2f}s START / overload auto-backoff")
    print("OVERLOAD: 실제 403/429/503 또는 Workload is so high만 자동완화")
    print("RUN SECONDS:", RUN_SECONDS)
    print("KST NOW:", now_kst().strftime("%Y-%m-%d %H:%M:%S"))
    print("=" * 72)

    # 메인 페이지 확인은 참고용. 실패해도 API 감시는 계속한다.
    try:
        session = requests.Session(impersonate="chrome")
        response = session.get(
            "https://www.megabox.co.kr/",
            headers=HEADERS,
            timeout=MAIN_PAGE_TIMEOUT,
        )
        print("MEGABOX PAGE STATUS:", response.status_code)
        if response.status_code != 200:
            notify_error(
                "메가박스 메인 페이지 확인 오류",
                details=f"HTTP {response.status_code}",
                dedupe_key=f"main-page-http-{response.status_code}",
            )
    except Exception as e:
        print("MEGABOX PAGE CHECK WARNING:", repr(e))
        print("MAIN PAGE CHECK FAILED - CONTINUE MONITORING")
        notify_error(
            "메가박스 메인 페이지 확인 실패",
            e,
            dedupe_key="main-page-check",
        )

    # --------------------------------------------------------
    # 최초/업그레이드 baseline
    # --------------------------------------------------------
    if not baseline_done():
        print()
        print("=" * 72)
        print("INITIAL 43-DAY BASELINE")
        print("=" * 72)
        print("현재 43일 메가토크/무대인사 회차를 기준값으로 등록합니다.")

        events, failed_dates = collect_all_days(progress=True)
        if failed_dates:
            print("BASELINE FAILED DATES:", ", ".join(failed_dates))
            notify_error(
                "최초 baseline 43일 조회 실패",
                details=(
                    f"실패 {len(failed_dates)}일. 불완전 baseline 생성을 막고 이번 실행을 종료합니다. "
                    f"예: {', '.join(failed_dates[:5])}"
                ),
                dedupe_key="baseline-scan-failed",
            )
            return

        seen = set(events.keys())
        show_state = {
            key: state_record(event)
            for key, event in events.items()
        }
        status = {"shows": show_state}

        # 최초 확인용 Discord도 실제 알림과 같은 형식.
        # 한 알림 = 날짜 1개 + 영화 1편 + 행사종류 1개.
        selected = select_initial_confirmation_groups(events)
        confirm_sent = 0
        for group in selected:
            try:
                confirm_sent += send_alert_group(group, "DETECTED")
            except Exception as e:
                notify_error(
                    "최초 확인용 Discord 전송 실패",
                    e,
                    dedupe_key="baseline-confirm-send",
                )

        print("BASELINE EVENT COUNT:", len(seen))
        print_counts(events)
        print(f"📣 최초 확인용 실제 형식 알림 {confirm_sent}/{len(selected)} 전송")
        save_seen(seen)
        save_status(status)
        mark_baseline_done()
        print("현재 회차 전체 baseline 등록 완료")
        print("BASELINE COMPLETE")

    # --------------------------------------------------------
    # 정상 감시
    # --------------------------------------------------------
    seen = load_seen()
    status = load_status()
    show_state = status["shows"]

    monitor_started = time.monotonic()
    next_due = build_due_schedule(show_state)
    stage_next_due = {}  # 통합 lane 사용: 별도 무대인사 lane 비활성
    offsets = {date: offset_for_date(date) for date in make_monitor_dates()}
    next_safety_scan_at = next_halfhour_boundary(now_kst())

    date_count_cache = state_count_cache(show_state)
    latest_counts = total_counts_from_cache(date_count_cache)

    heartbeat_started = monitor_started
    heartbeat_date_checks = 0
    heartbeat_stage_checks = 0
    heartbeat_alerts = 0
    heartbeat_failed_dates = 0

    gv_dates = [date for date in make_monitor_dates() if is_gv_target_date(date)]
    stage_dates = [date for date in make_monitor_dates() if is_stage_target_date(date)]
    print(
        "✅ 집중 감시 시작 | GV/메가토크 +4~+21일 약 8초 | "
        "무대인사 +7~+42일 수/토/일/공휴일"
    )
    print(
        f"🎤 무대인사 대상 {len(stage_dates)}일 | "
        + ", ".join(
            datetime.strptime(date, "%Y%m%d").strftime("%Y-%m-%d")
            for date in stage_dates
        )
    )
    print(f"🎬 GV/메가토크 대상 {len(gv_dates)}일 | +4~+21일 | 약 8초")
    print("⚡ 00/30 추가점검 | +4~+21일 전체 | 2 worker")

    while True:
        now_mono = time.monotonic()
        if now_mono - program_started >= RUN_SECONDS:
            print("MONITOR TIME FINISHED")
            break

        # ----------------------------------------------------
        # GENERAL 기본 분산 lane
        # ----------------------------------------------------
        due_dates = [
            date
            for date, due in sorted(next_due.items(), key=lambda item: item[1])
            if due <= now_mono
        ][:MAX_DUE_DATES_PER_BATCH]

        if due_dates:
            overload_before = overload_event_count()
            events, failed_dates = collect_due_dates(due_dates)
            batch_overloads = overload_event_count() - overload_before
            valid_dates = set(due_dates) - set(failed_dates)

            if events or valid_dates:
                reconcile_semantic_seen(events, seen, show_state)
                detected = send_detected_events(events, seen, show_state)
                state_alerts = process_state_transitions(events, show_state)
                heartbeat_alerts += detected + state_alerts

                for date in valid_dates:
                    date_events = {
                        key: event
                        for key, event in events.items()
                        if event.get("date") == date
                    }
                    date_count_cache[date] = count_events(date_events)
                latest_counts = total_counts_from_cache(date_count_cache)
                save_seen(seen)
                save_status({"shows": show_state})

            heartbeat_date_checks += len(due_dates)
            heartbeat_failed_dates += len(failed_dates)

            if failed_dates:
                notify_error(
                    "GENERAL 분산조회 일부 실패",
                    details=f"실패 {len(failed_dates)}/{len(due_dates)}일 | 예: {', '.join(failed_dates[:3])}",
                    dedupe_key="regular-batch-failure",
                )

            reschedule_base = time.monotonic()
            for date in due_dates:
                offset = offsets.get(date, DAYS - 1)
                interval = effective_interval(date, offset, show_state)
                if date in failed_dates:
                    interval = min(interval, error_retry_interval(offset))
                next_due[date] = reschedule_base + interval

                # 방금 GENERAL에서 본 날짜가 stage fast 대상이면 중복 직후 호출을 피하고 20초 뒤로.
                if date in stage_next_due and date not in failed_dates:
                    stage_next_due[date] = reschedule_base + STAGE_FAST_INTERVAL

            if not failed_dates and batch_overloads == 0:
                note_clean_cycle()

        # ----------------------------------------------------
        # 별도 무대인사 lane은 통합 스케줄로 대체되어 비활성
        # ----------------------------------------------------
        now_mono = time.monotonic()
        stage_due_dates = [
            date
            for date, due in sorted(stage_next_due.items(), key=lambda item: item[1])
            if due <= now_mono
        ][:MAX_DUE_DATES_PER_BATCH]

        if stage_due_dates:
            overload_before = overload_event_count()
            stage_events, stage_failed = collect_stage_dates(stage_due_dates)
            stage_overloads = overload_event_count() - overload_before
            valid_stage_dates = set(stage_due_dates) - set(stage_failed)

            if stage_events or valid_stage_dates:
                reconcile_semantic_seen(stage_events, seen, show_state)
                detected = send_detected_events(stage_events, seen, show_state)
                state_alerts = process_state_transitions(stage_events, show_state)
                heartbeat_alerts += detected + state_alerts

                # stage count만 갱신하고 메가토크 count는 기존 캐시 유지.
                for date in valid_stage_dates:
                    date_events = {
                        key: event
                        for key, event in stage_events.items()
                        if event.get("date") == date
                    }
                    bucket = date_count_cache.setdefault(
                        date,
                        {"메가토크": 0, "무대인사": 0},
                    )
                    bucket["무대인사"] = count_events(date_events)["무대인사"]
                latest_counts = total_counts_from_cache(date_count_cache)
                save_seen(seen)
                save_status({"shows": show_state})

            heartbeat_stage_checks += len(stage_due_dates)
            heartbeat_failed_dates += len(stage_failed)

            if stage_failed:
                notify_error(
                    "무대인사 20초 빠른조회 일부 실패",
                    details=f"실패 {len(stage_failed)}/{len(stage_due_dates)}일 | 예: {', '.join(stage_failed[:3])}",
                    dedupe_key="stage-fast-batch-failure",
                )

            base = time.monotonic()
            for date in stage_due_dates:
                stage_next_due[date] = base + STAGE_FAST_INTERVAL

            if not stage_failed and stage_overloads == 0:
                note_clean_cycle()

        # ----------------------------------------------------
        # 매시 00/30: +4~+21일 전체 추가점검 (GV + 조건에 맞는 무대인사)
        # ----------------------------------------------------
        now_wall = now_kst()
        if now_wall >= next_safety_scan_at:
            safety_slot = next_safety_scan_at
            safety_dates = make_safety_scan_dates()
            safety_started = time.monotonic()

            if safety_dates:
                overload_before = overload_event_count()
                safety_events, safety_failed = collect_due_dates(safety_dates)
                safety_overloads = overload_event_count() - overload_before
                valid_dates = set(safety_dates) - set(safety_failed)

                if safety_events or valid_dates:
                    reconcile_semantic_seen(safety_events, seen, show_state)
                    detected = send_detected_events(safety_events, seen, show_state)
                    state_alerts = process_state_transitions(safety_events, show_state)
                    heartbeat_alerts += detected + state_alerts

                    for date in valid_dates:
                        date_events = {
                            key: event
                            for key, event in safety_events.items()
                            if event.get("date") == date
                        }
                        date_count_cache[date] = count_events(date_events)
                    latest_counts = total_counts_from_cache(date_count_cache)
                    save_seen(seen)
                    save_status({"shows": show_state})

                heartbeat_stage_checks += len(safety_dates)
                heartbeat_failed_dates += len(safety_failed)

                if safety_failed:
                    notify_error(
                        "00/30 추가점검 일부 실패",
                        details=f"실패 {len(safety_failed)}/{len(safety_dates)}일 | 예: {', '.join(safety_failed[:3])}",
                        dedupe_key="0030-extra-failure",
                    )

                base = time.monotonic()
                for date in valid_dates:
                    if date in next_due:
                        next_due[date] = base + effective_interval(
                            date, show_state=show_state
                        )

                elapsed = time.monotonic() - safety_started
                error_count = len(safety_failed) + safety_overloads
                icon = "⚡" if error_count == 0 else "⚠️"
                print(
                    f"{icon} {safety_slot.strftime('%H:%M')} 00/30 추가점검 완료 | "
                    f"대상 {len(safety_dates)}일 | 성공 {len(valid_dates)}/{len(safety_dates)} | "
                    f"{elapsed:.2f}초 | 오류 {error_count}"
                )

                if error_count == 0:
                    note_clean_cycle()
            else:
                print(f"⚡ {safety_slot.strftime('%H:%M')} 00/30 대상 날짜 없음")

            while next_safety_scan_at <= now_kst():
                next_safety_scan_at += timedelta(minutes=SAFETY_SCAN_EVERY_MINUTES)

        # ----------------------------------------------------
        # 10분 heartbeat
        # ----------------------------------------------------
        now_mono = time.monotonic()
        if now_mono - heartbeat_started >= HEARTBEAT_INTERVAL:
            mins = max(1, int((now_mono - heartbeat_started) // 60))
            health = "💚 정상 감시중" if heartbeat_failed_dates == 0 else "⚠️ 감시중(API 오류 있음)"
            print(
                f"{health} | 최근 {mins}분 기본 날짜조회 {heartbeat_date_checks}회 | "
                f"무대인사 빠른조회 {heartbeat_stage_checks}회 | "
                f"메가토크 {latest_counts['메가토크']} | 무대인사 {latest_counts['무대인사']} | "
                f"Discord 알림 {heartbeat_alerts} | "
                f"오류 {heartbeat_failed_dates} | 요청간격 {current_request_gap():.2f}s"
            )
            heartbeat_started = now_mono
            heartbeat_date_checks = 0
            heartbeat_stage_checks = 0
            heartbeat_alerts = 0
            heartbeat_failed_dates = 0

        # 다음 일정까지 짧게 sleep.
        now_mono = time.monotonic()
        next_regular = min(next_due.values()) if next_due else now_mono + 1.0
        next_stage = min(stage_next_due.values()) if stage_next_due else now_mono + 1.0
        seconds_to_safety = max(0.0, (next_safety_scan_at - now_kst()).total_seconds())
        next_safety = now_mono + seconds_to_safety
        next_heartbeat = heartbeat_started + HEARTBEAT_INTERVAL
        next_wake = min(next_regular, next_stage, next_safety, next_heartbeat)
        time.sleep(max(0.05, min(0.5, next_wake - time.monotonic())))

    save_seen(seen)
    save_status({"shows": show_state})
    print("FINAL SEEN STATE:", len(seen))
    print("DONE")


if __name__ == "__main__":
    if not NOTICE_ENDPOINT or not NOTICE_TARGET:
        raise SystemExit("Missing required Actions secrets: NOTICE_ENDPOINT, NOTICE_TARGET")
    main()
