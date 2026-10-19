# -*- coding: utf-8 -*-
"""
石大查询 · AstrBot 插件

免登录：空教室、附近教室、图书馆实时空座
需 token：图书馆房间空位、座位图、我的预约（token 失效时给友好提示，不影响其他命令）

数据来源：
    空教室   https://app.upc.edu.cn/freeclass/wap/default/all
    图书馆   https://libspace.upc.edu.cn/libseat/
"""

import asyncio
import datetime
import hashlib
import hmac
import http.cookiejar
import json
import os
import re
import ssl
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
from concurrent.futures import ThreadPoolExecutor

from astrbot.api.event import filter, AstrMessageEvent
from astrbot.api.star import Context, Star, register

# ================================================================ 通用 ====
SSL_CTX = ssl.create_default_context()
SSL_CTX.check_hostname = False
SSL_CTX.verify_mode = ssl.CERT_NONE

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36")

WEEKDAY_CN = ["周一", "周二", "周三", "周四", "周五", "周六", "周日"]

PERIOD_GROUPS = {
    "上午": [1, 2, 3, 4, 5],
    "下午": [6, 7, 8, 9],
    "晚上": [10, 11, 12, 13],
    "白天": list(range(1, 10)),
    "全天": list(range(1, 14)),
}

PERIOD_ALIASES = {
    "am": "上午", "morning": "上午",
    "pm": "下午", "afternoon": "下午",
    "night": "晚上", "evening": "晚上",
    "day": "白天", "all": "全天",
}

BUILDING_ALIASES = {
    "nanjiao": "南教楼", "nanjiaolou": "南教楼",
    "nantang": "南堂",
    "donghuan": "东环", "donglang": "东廊",
    "xihuan": "西环", "xilang": "西廊",
    "zonghe": "综合实验楼", "zhuoyue": "卓越教学楼",
}

CAMPUS_ALIASES = {
    "tangdao": "唐岛湾校区", "tangdaowan": "唐岛湾校区", "td": "唐岛湾校区",
    "guzhenkou": "古镇口校区", "gzk": "古镇口校区",
}

# 图书馆
LIB_BASE = "https://libspace.upc.edu.cn"
# 登录态和白名单都放在用户目录下，跨平台、且插件更新不会丢
DATA_DIR = os.path.join(os.path.expanduser("~"), ".astrbot_plugin_upc")
TOKEN_FILE = os.path.join(DATA_DIR, "token")
LIB_HMAC_KEY = "leos3cr3t"   # 前端 NUMCODE 解出来的签名密钥
LIB_BUILDINGS = {"东馆": 1, "总馆": 3}


# ============================================================== 小工具 ====
def _today():
    return datetime.date.today().isoformat()


def _date_label(date_str):
    try:
        dt = datetime.date.fromisoformat(date_str)
        return "%d月%d日（%s）" % (dt.month, dt.day, WEEKDAY_CN[dt.weekday()])
    except ValueError:
        return date_str


def _current_periods():
    h = datetime.datetime.now().hour
    if h < 12:
        return PERIOD_GROUPS["上午"]
    if h < 18:
        return PERIOD_GROUPS["下午"]
    return PERIOD_GROUPS["晚上"]


def _parse_periods(text):
    if not text:
        return _current_periods()
    text = PERIOD_ALIASES.get(text.strip().lower(), text.strip())
    if text in PERIOD_GROUPS:
        return PERIOD_GROUPS[text]
    out = []
    for part in text.replace("，", ",").split(","):
        part = part.strip()
        if not part:
            continue
        if "-" in part:
            a, b = part.split("-", 1)
            if a.isdigit() and b.isdigit():
                out.extend(range(int(a), int(b) + 1))
        elif part.isdigit():
            out.append(int(part))
    return sorted(set(out)) or _current_periods()


def _periods_label(periods):
    for name, group in PERIOD_GROUPS.items():
        if periods == group:
            return "%s（%d-%d节）" % (name, group[0], group[-1])
    if len(periods) == 1:
        return "第%d节" % periods[0]
    return "第%s节" % "、".join(str(p) for p in periods)


def _lib_default_date():
    """图书馆默认日期：07:00-22:00 之外用明天（闭馆时查今天没意义）。"""
    now = datetime.datetime.now()
    if now.hour < 7 or now.hour >= 22:
        return (now.date() + datetime.timedelta(days=1)).isoformat()
    return now.date().isoformat()


def _parse_time_range(tok):
    """'08:00-10:00' / '8-10' / '8:00~10:00' → (开始分钟, 结束分钟)。"""
    if not tok:
        return None
    m = re.match(r"^\s*(\d{1,2})(?::(\d{2}))?\s*[-~—到]\s*(\d{1,2})(?::(\d{2}))?\s*$",
                 str(tok))
    if not m:
        return None
    b = int(m.group(1)) * 60 + int(m.group(2) or 0)
    e = int(m.group(3)) * 60 + int(m.group(4) or 0)
    if 0 <= b < e <= 24 * 60:
        return b, e
    return None


def _fmt_min(m):
    return "%02d:%02d" % (int(m) // 60, int(m) % 60)


def _looks_like_date(tok):
    t = str(tok)
    return t in ("今天", "明天", "后天", "today", "tomorrow") or bool(
        re.match(r"^\d{4}-\d{1,2}-\d{1,2}$", t))


def _split_date_window(tokens, default_date):
    """从参数里拆出日期和时间段，两个都支持任意顺序。"""
    date, window = default_date, None
    for t in tokens:
        w = _parse_time_range(t)
        if w:
            window = w
        elif _looks_like_date(t):
            date = _parse_date_arg(t)
    return date, window


def _lib_free_keys(room_id, date, window, token):
    """指定时间段内可约的座位 key 集合。"""
    if not window:
        return None, None
    begin, end = window
    path = "/rest/v2/searchSeats/%s/%d/%d?roomId=%s" % (date, begin, end, room_id)
    obj = _lib_get(path, token=token)
    data = obj.get("data")
    if data is None:
        return None, obj.get("message") or "接口没返回数据"
    return set((data.get("seats") or {}).keys()), None


def _lib_building_window(building_id, date, window, token):
    """按时间段统计整栋楼各房间空位：返回 {roomId: free}。"""
    begin, end = window
    path = "/rest/v2/searchSeats/%s/%d/%d?buildingId=%s" % (date, begin, end, building_id)
    obj = _lib_get(path, token=token)
    data = obj.get("data")
    if data is None:
        return None, obj.get("message") or "接口没返回数据"
    counts = {}
    for _k, cell in (data.get("seats") or {}).items():
        rid = cell.get("roomId")
        counts[rid] = counts.get(rid, 0) + 1
    return counts, None


def _parse_date_arg(tok):
    """支持 今天/明天/后天/YYYY-MM-DD，默认今天。"""
    if not tok:
        return _today()
    t = str(tok).strip()
    today = datetime.date.today()
    if t in ("今天", "today"):
        return today.isoformat()
    if t in ("明天", "tomorrow"):
        return (today + datetime.timedelta(days=1)).isoformat()
    if t in ("后天",):
        return (today + datetime.timedelta(days=2)).isoformat()
    if re.match(r"^\d{4}-\d{1,2}-\d{1,2}$", t):
        y, m, d = t.split("-")
        return "%04d-%02d-%02d" % (int(y), int(m), int(d))
    return today.isoformat()


def _args(event, names):
    text = (event.message_str or "").replace("\u3000", " ").strip()
    toks = [t for t in text.split() if t and not t.startswith("@")]
    if toks:
        head = toks[0].lstrip("/").split("@")[0]
        if head in names:
            toks = toks[1:]
    return toks


def _http_json(url, data=None, method="GET", headers=None, retries=3):
    pairs = None
    if data:
        pairs = urllib.parse.urlencode(data, doseq=True).encode()
    last = None
    for attempt in range(retries):
        req = urllib.request.Request(url, data=pairs, method=method,
                                     headers=dict(headers or {}))
        try:
            with urllib.request.urlopen(req, timeout=20, context=SSL_CTX) as r:
                return json.loads(r.read().decode("utf-8", "replace"))
        except urllib.error.HTTPError as e:
            body = e.read().decode("utf-8", "replace")
            try:
                return json.loads(body)
            except json.JSONDecodeError:
                return {"error": "HTTP %s" % e.code, "raw": body[:200]}
        except Exception as e:  # noqa: BLE001 连接被掐就重试
            last = e
            if attempt < retries - 1:
                time.sleep(0.6 * (attempt + 1))
    return {"error": "%s: %s" % (type(last).__name__, last)}


# ========================================================== 空教室查询 ====
FC_BASE = "https://app.upc.edu.cn"
FC_SEARCH = FC_BASE + "/freeclass/wap/default/search-all"
FC_DETAIL = FC_BASE + "/freeclass/wap/default/detail"

FC_HEADERS = {
    "User-Agent": UA,
    "Accept": "application/json, text/javascript, */*; q=0.01",
    "X-Requested-With": "XMLHttpRequest",
    "Referer": FC_BASE + "/freeclass/wap/default/all",
    "Origin": FC_BASE,
}


def _fc_query(campus, date, periods, building="全部"):
    data = [("xq", campus), ("date", date), ("lh", building)]
    for p in periods:
        data.append(("jc[]", str(p)))
    obj = _http_json(FC_SEARCH, data=data, method="POST", headers=FC_HEADERS)
    if obj.get("error"):
        raise RuntimeError(obj["error"])
    if obj.get("e") != 0:
        raise RuntimeError("接口返回 e=%s" % obj.get("e"))
    d = obj.get("d") or {}
    return {
        "campus": campus,
        "date": date,
        "periods": periods,
        "rooms": d.get("js") or {},
        "all": d.get("all") or {},
    }


def _fc_room_busy(code, date):
    obj = _http_json(FC_DETAIL, data=[("code", code), ("date", date)],
                     method="POST", headers=FC_HEADERS)
    d = obj.get("d") or {}
    weekdays = d.get("weekdays") or []
    kclist = d.get("kclist") or {}
    idx = weekdays.index(date) + 1 if date in weekdays else 1
    return kclist.get(str(idx)) or {}


def _room_digits(code):
    m = re.search(r"(\d{2,4})", code or "")
    return m.group(1) if m else ""


def _infer_campus(text):
    for alias, campus in CAMPUS_ALIASES.items():
        if alias in text.lower():
            return campus
    return "唐岛湾校区"


def _infer_building(text):
    for alias, building in BUILDING_ALIASES.items():
        if alias in text.lower():
            return building
    for prefix, building in [("南教", "南教楼"), ("南堂", "南堂"), ("东环", "东环"),
                             ("东廊", "东廊"), ("西环", "西环"), ("西廊", "西廊"),
                             ("综合", "综合实验楼"), ("卓越", "卓越教学楼")]:
        if prefix in text:
            return building
    return None


def _render_freeclass(res, building_filter=None):
    rooms = res["rooms"]
    total = sum(len(v) for v in rooms.values())
    head = "📍 %s · %s · %s" % (
        res["campus"].replace("校区", ""), _date_label(res["date"]),
        _periods_label(res["periods"]))

    if not rooms:
        return head + "\n\n这个时段没有空教室。"

    lines = [head, ""]
    if building_filter and building_filter != "全部":
        for bname, items in rooms.items():
            names = [it.get("name", "?") for it in items]
            lines.append("【%s】%d 间" % (bname, len(names)))
            for i in range(0, len(names), 8):
                lines.append("  " + "、".join(names[i:i + 8]))
        lines.append("")
        lines.append("合计 %d 间。" % total)
    else:
        for bname, items in sorted(rooms.items(), key=lambda kv: -len(kv[1])):
            names = [it.get("name", "?") for it in items]
            preview = "、".join(names[:5])
            more = " 等" if len(names) > 5 else ""
            lines.append("%s %d 间：%s%s" % (bname, len(names), preview, more))
        lines.append("")
        lines.append("合计 %d 间空教室。" % total)
        lines.append("发「/空教室 南教楼」看单栋楼全部。")
    return "\n".join(lines)


def _render_nearby(nb):
    t = nb["target"]
    lines = [
        "📍 %s · %s · %s" % (_infer_campus(nb["campus"]).replace("校区", ""),
                             _date_label(nb["date"]), _periods_label(nb["periods"])),
        "你在：%s（%s楼）" % (t.get("name"), nb["floor"]),
        "",
    ]
    if not nb["near"]:
        lines.append("附近没有同层其他教室。")
        return "\n".join(lines)
    free_n = 0
    for _d, it in nb["near"]:
        is_free = it.get("free")
        if is_free:
            free_n += 1
        courses = it.get("courses") or []
        if is_free:
            state = "空"
        elif courses:
            state = "有课：" + "、".join(courses)
        else:
            state = "有课"
        lines.append("  %s %-10s %s" % ("✅" if is_free else "⛔", it.get("name", "?"), state))
    lines.append("")
    lines.append("附近 %d 间：%d 空 / %d 有课" % (len(nb["near"]), free_n,
                                              len(nb["near"]) - free_n))
    return "\n".join(lines)


def _fc_find_nearby(room_text, date, periods, radius=6, limit=10):
    building = _infer_building(room_text)
    campus = "古镇口校区" if building == "卓越教学楼" else _infer_campus(room_text)
    res = _fc_query(campus, date, periods)
    all_rooms = res["all"]
    free_rooms = res["rooms"]

    target = None
    for bname, items in all_rooms.items():
        for it in items:
            code = (it.get("code") or "").upper()
            name = (it.get("name") or "").upper()
            t = room_text.strip().upper()
            if t == code or name.startswith(t) or (t.isdigit() and _room_digits(code) == t):
                target = (bname, it)
                break
        if target:
            break
    if not target:
        raise RuntimeError("找不到教室「%s」，试试 南教305 这种写法" % room_text)

    bname, troom = target
    free_codes = {it.get("code") for it in free_rooms.get(bname, [])}
    tdigits = _room_digits(troom.get("code"))
    tfloor = int(tdigits[0]) if tdigits else None
    tblock = ""
    if "-" in (troom.get("code") or ""):
        m = re.match(r"([A-Za-z]+)", troom.get("code").split("-")[-1])
        tblock = (m.group(1) or "").upper() if m else ""

    near = []
    for it in all_rooms.get(bname, []):
        if it.get("code") == troom.get("code"):
            continue
        dg = _room_digits(it.get("code"))
        if not dg or (int(dg[0]) if dg else None) != tfloor:
            continue
        block = ""
        if "-" in (it.get("code") or ""):
            m = re.match(r"([A-Za-z]+)", it.get("code").split("-")[-1])
            block = (m.group(1) or "").upper() if m else ""
        if block != tblock:
            continue
        diff = abs(int(dg) - int(tdigits))
        if diff <= radius:
            near.append((diff, it))
    near.sort(key=lambda x: (x[0], x[1].get("name", "")))
    near = near[:limit]

    items = []
    for diff, it in near:
        item = dict(it)
        item["free"] = it.get("code") in free_codes
        item["courses"] = []
        items.append(item)

    occupied = [it for it in items if not it["free"]][:8]

    def _fetch(item):
        try:
            busy = _fc_room_busy(item["code"], date)
            names = []
            for p in periods:
                v = busy.get("c_%d" % p)
                nm = v.get("name") if isinstance(v, dict) else None
                if nm and nm not in names:
                    names.append(nm)
            return item["code"], names
        except Exception:  # noqa: BLE001
            return item["code"], []

    if occupied:
        with ThreadPoolExecutor(max_workers=6) as pool:
            found = dict(pool.map(_fetch, occupied))
        for it in items:
            it["courses"] = found.get(it["code"], [])

    return {
        "campus": campus,
        "date": date,
        "periods": periods,
        "target": troom,
        "floor": tfloor,
        "near": [(d, it) for d, it in zip([x[0] for x in near], items)],
    }


# ========================================================== 图书馆 ====
def _lib_signed_headers(method):
    rid = str(uuid.uuid4())
    ts = str(int(time.time() * 1000))
    msg = "seat::%s::%s::%s" % (rid, ts, method.upper())
    key = hmac.new(LIB_HMAC_KEY.encode(), msg.encode(), hashlib.sha256).hexdigest()
    return {
        "User-Agent": UA,
        "Accept": "application/json, text/plain, */*",
        "Referer": LIB_BASE + "/libseat/",
        "loginType": "PC",
        "X-request-id": rid,
        "X-request-date": ts,
        "X-hmac-request-key": key,
    }


def _lib_get(path, token=None):
    url = path if path.startswith("http") else LIB_BASE + path
    if token:
        sep = "&" if "?" in url else "?"
        url += sep + "token=" + urllib.parse.quote(token, safe="")
    return _http_json(url, headers=_lib_signed_headers("GET"))


BLACKLIST_FILE = os.path.join(DATA_DIR, "blacklist.json")


def _ensure_data_dir():
    try:
        os.makedirs(DATA_DIR, exist_ok=True)
        return True
    except OSError:
        return False


def _load_blacklist():
    try:
        with open(BLACKLIST_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except (OSError, json.JSONDecodeError):
        return {}


def _save_blacklist(data):
    try:
        _ensure_data_dir()
        with open(BLACKLIST_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        return True
    except OSError:
        return False


def _blacklist_for(room_id):
    return set(_load_blacklist().get(str(room_id)) or [])


def _parse_seat_names(args):
    out = []
    for a in args:
        for part in str(a).replace("，", ",").split(","):
            part = part.strip()
            if part:
                out.append(part)
    return out


def _load_lib_token():
    try:
        with open(TOKEN_FILE, "r", encoding="utf-8") as f:
            return f.read().strip() or None
    except OSError:
        return None


def _lib_status_text():
    avail = _lib_get("/rest/v2/availSeats")
    if avail.get("status") != "success":
        return "⚠️ 图书馆接口暂时不可用。"
    d = avail.get("data") or {}
    not_free = d.get("notFree") or {}
    settings = (_lib_get("/rest/v2/settings").get("data") or {})
    oc = settings.get("buildingOpenClose") or []
    hours = "、".join("%s-%s" % (a, b) for _i, a, b in oc) if oc else "?"

    lines = [
        "📚 图书馆（实时）",
        "",
        "空座：%s" % d.get("seats"),
        "已签到在座：%s" % not_free.get("checkInCount"),
    ]
    if not_free.get("reserveNotYetCount"):
        lines.append("已预约未到：%s" % not_free.get("reserveNotYetCount"))
    lines.append("")
    lines.append("开馆：%s" % hours)
    if settings.get("checkInAheadMins") is not None:
        lines.append("可提前签到：%s 分钟" % settings["checkInAheadMins"])
    return "\n".join(lines)


def _lib_stats_text(building_name, date, token, window=None):
    bid = LIB_BUILDINGS.get(building_name)
    if not bid:
        return "馆区只有：东馆 / 总馆"
    obj = _lib_get("/rest/v2/room/stats2/%s/%s" % (bid, date), token=token)
    if obj.get("status") != "success":
        return ("⚠️ 图书馆登录态失效了。\n"
                "在电脑上跑一次 login.bat 重新登录。\n（%s）" % (obj.get("message") or "接口异常"))
    rooms = obj.get("data") or []
    if window:
        counts, err = _lib_building_window(bid, date, window, token)
        if counts is None:
            return "⚠️ 按时间段查询失败：%s" % err
        for r in rooms:
            r["free"] = counts.get(r.get("roomId"), 0)
    total_free = sum(r.get("free", 0) for r in rooms)
    total_seats = sum(r.get("totalSeats", 0) for r in rooms)
    lines = ["🏛 %s · %s" % (building_name, _date_label(date)),
             "空位合计：%d / %d" % (total_free, total_seats), ""]
    for r in sorted(rooms, key=lambda x: -x.get("free", 0))[:8]:
        lines.append("  %-12s %dF  空 %d/%d" % (
            r.get("room", "?"), r.get("floor", 0), r.get("free", 0), r.get("totalSeats", 0)))
    if len(rooms) > 8:
        lines.append("  …还有 %d 个房间" % (len(rooms) - 8))
    return "\n".join(lines)


def _lib_layout_text(room_id, date, token, free_keys=None, window=None):
    obj = _lib_get("/rest/v2/room/layoutByDate/%s/%s" % (room_id, date), token=token)
    if obj.get("status") != "success":
        return ("⚠️ 图书馆登录态失效了。\n"
                "在电脑上跑一次 login.bat 重新登录。\n（%s）" % (obj.get("message") or "接口异常"))
    d = obj.get("data") or {}
    layout = d.get("layout") or {}

    seats = []
    free = []
    for k, c in layout.items():
        if c.get("type") != "seat" or c.get("enabled") is False:
            continue
        seats.append(c)
        is_free = (k in free_keys) if free_keys is not None else (c.get("status") == "FREE")
        if is_free:
            free.append(c)

    when = _date_label(date)
    if window:
        when += " · %s-%s" % (_fmt_min(window[0]), _fmt_min(window[1]))

    lines = ["🪑 %s · %s" % (d.get("name"), when),
             "空位：%d / %d" % (len(free), len(seats))]
    if free:
        names = sorted(c.get("name", "?") for c in free)
        preview = " ".join(names[:40])
        lines.append("座位号：" + preview + (" …" if len(names) > 40 else ""))
    else:
        lines.append("这个时段没有可约座位。")
    return "\n".join(lines)


def _lib_quiet_seats_text(room_id, date, token, radius=2, top=10, blacklist=None,
                          free_keys=None):
    """从座位图里挑「周围没人的座位」：周边格子被占越少越安静。"""
    obj = _lib_get("/rest/v2/room/layoutByDate/%s/%s" % (room_id, date), token=token)
    if obj.get("status") != "success":
        return ("⚠️ token 过期了（重新登录：电脑上跑 login.bat）。\n（%s）"
                % (obj.get("message") or "接口异常"))
    d = obj.get("data") or {}
    cols = int(d.get("cols") or 1)
    rows = int(d.get("rows") or 0)
    layout = d.get("layout") or {}

    seats = {}
    key_of = {}
    for k, c in layout.items():
        if c.get("type") != "seat" or c.get("enabled") is False:
            continue
        pos = _cell_pos(k, cols, rows)
        if pos:
            seats[pos] = c
            key_of[pos] = k

    if not seats:
        return "这间教室没有可预约的座位。"

    if free_keys is not None:
        free = {p for p in seats if key_of.get(p) in free_keys}
    else:
        free = {p for p, c in seats.items() if c.get("status") == "FREE"}
    if blacklist:
        free = {p for p in free if str(seats[p].get("name") or "") not in blacklist}
    occupied = set(seats) - free

    def neighbors(pos, r):
        rr, cc = pos
        out = []
        for dr in range(-r, r + 1):
            for dc in range(-r, r + 1):
                if dr == 0 and dc == 0:
                    continue
                np = (rr + dr, cc + dc)
                if np in seats:
                    out.append(np)
        return out

    scored = []
    for p in free:
        nb = neighbors(p, radius)
        occ = sum(1 for q in nb if q in occupied)
        scored.append((occ, len(nb), p))

    # 先按「周围有人」少→多，再按周围空位多→少
    scored.sort(key=lambda x: (x[0], -x[1], seats[x[2]].get("name", "")))

    lines = ["🪑 %s · %s" % (d.get("name"), _date_label(date)),
             "空位：%d / %d" % (len(free), len(seats))]
    if not free:
        lines.append("")
        lines.append("现在没有空位了。")
        return "\n".join(lines)

    lines.append("")
    lines.append("最安静的 %d 个（看周围 %d 格内有没有人）：" % (min(top, len(scored)), radius))
    for occ, nb_total, pos in scored[:top]:
        c = seats[pos]
        if occ == 0:
            tag = "周边全空"
        else:
            tag = "周边 %d 人有座" % occ
        flags = "".join(["🪟" if c.get("window") else "",
                         "🔌" if c.get("power") else ""])
        lines.append("  %s 座位 %s%s" % (tag, c.get("name", "?"), flags))

    if len(scored) > top:
        lines.append("…共 %d 个空位" % len(scored))
    lines.append("")
    lines.append("（按座位图网格算的近似：只统计座位上有没有人）")
    return "\n".join(lines)


def _lib_rooms_text(building_filter, token):
    """列出馆区和房间 id，用于 /图书馆 地图 <id>。"""
    obj = _lib_get("/rest/v2/free/filters", token=token)
    if obj.get("status") != "success":
        return ("⚠️ 图书馆登录态失效了。\n（%s）"
                % (obj.get("message") or "接口异常"))
    d = obj.get("data") or {}
    buildings = d.get("buildings") or []
    rooms = d.get("rooms") or []

    lines = []
    for b in buildings:
        bid, bname = b[0], b[1]
        if building_filter and building_filter not in (str(bname), str(bid)):
            continue
        lines.append("🏛 %s（id=%s）" % (bname, bid))
        for r in rooms:
            if len(r) >= 4 and r[2] == bid:
                lines.append("  %-4s %-18s %sF" % (r[0], r[1], r[3]))
        lines.append("")
    if not lines:
        return "没有匹配的馆区。用法：/图书馆 列表 [东馆|总馆]"
    lines.append("看座位图：/图书馆 地图 <房间id>")
    return "\n".join(lines).strip()


def _lib_reservations_text(token):
    """我的预约。"""
    obj = _lib_get("/rest/v2/user/reservations", token=token)
    if obj.get("status") != "success":
        return ("⚠️ 图书馆登录态失效了。\n"
                "在电脑上跑一次 login.bat 重新登录。\n（%s）" % (obj.get("message") or "接口异常"))
    data = obj.get("data")
    if not data:
        return "📋 当前没有预约。"
    lines = ["📋 我的预约："]
    if isinstance(data, list):
        for item in data[:5]:
            lines.append("  " + json.dumps(item, ensure_ascii=False)[:200])
    else:
        lines.append(json.dumps(data, ensure_ascii=False)[:800])
    return "\n".join(lines)


# ===================================================== 座位示意图 =====
# 3x5 点阵数字（用于在图上标座位号，不依赖字体文件）
_FONT_3x5 = {
    "0": ("111", "101", "101", "101", "111"),
    "1": ("010", "110", "010", "010", "111"),
    "2": ("111", "001", "111", "100", "111"),
    "3": ("111", "001", "111", "001", "111"),
    "4": ("101", "101", "111", "001", "001"),
    "5": ("111", "100", "111", "001", "111"),
    "6": ("111", "100", "111", "101", "111"),
    "7": ("111", "001", "010", "010", "010"),
    "8": ("111", "101", "111", "101", "111"),
    "9": ("111", "101", "111", "001", "111"),
}


def _text_width(text, scale=2):
    return len(text) * (3 * scale + scale)


def _draw_number(canvas, width, height, x, y, text, color, scale=2):
    """把数字画到 canvas（每行 bytearray，RGB）。"""
    cx = x
    for ch in text:
        glyph = _FONT_3x5.get(ch)
        if glyph:
            for row_i, row in enumerate(glyph):
                for col_i, bit in enumerate(row):
                    if bit != "1":
                        continue
                    px = cx + col_i * scale
                    py = y + row_i * scale
                    for dy in range(scale):
                        yy = py + dy
                        if not (0 <= yy < height):
                            continue
                        line = canvas[yy]
                        for dx in range(scale):
                            xx = px + dx
                            if 0 <= xx < width:
                                i = xx * 3
                                line[i:i + 3] = bytes(color)
        cx += 3 * scale + scale


def _cell_pos(key, cols, rows):
    """座位图坐标是 row*1000+col（实测三间房都符合），不是 row*cols+col。"""
    try:
        idx = int(key)
    except (TypeError, ValueError):
        return None
    r, c = divmod(idx, 1000)
    if r < 0 or r >= rows or c < 0 or c >= cols:
        return None
    return r, c


def _write_png(path, width, height, rows_rgb):
    """极简 PNG 编码器（不依赖 Pillow）。rows_rgb: 每行一个 bytearray。"""
    import binascii
    import struct
    import zlib

    raw = b"".join(b"\x00" + bytes(row) for row in rows_rgb)

    def chunk(tag, data):
        body = tag + data
        return (struct.pack(">I", len(data)) + body
                + struct.pack(">I", binascii.crc32(body) & 0xFFFFFFFF))

    ihdr = struct.pack(">IIBBBBB", width, height, 8, 2, 0, 0, 0)
    png = (b"\x89PNG\r\n\x1a\n"
           + chunk(b"IHDR", ihdr)
           + chunk(b"IDAT", zlib.compress(raw, 6))
           + chunk(b"IEND", b""))
    with open(path, "wb") as f:
        f.write(png)


def _render_layout_png(data, path, cell=26, blacklist=None, show_numbers=True,
                       free_keys=None):
    """把 seat layout 画成示意图（带座位号），返回 (路径, 统计)。"""
    cols = int(data.get("cols") or 1)
    rows = int(data.get("rows") or 1)
    layout = data.get("layout") or {}
    blacklist = blacklist or set()

    C_BG = (255, 255, 255)
    C_GRID = (225, 225, 225)
    C_FREE = (150, 215, 150)
    C_USED = (235, 130, 130)
    C_BLOCK = (90, 90, 90)
    C_DESK = (192, 202, 222)
    C_DISABLED = (205, 205, 205)
    C_TEXT_DARK = (25, 25, 25)
    C_TEXT_LIGHT = (255, 255, 255)

    width, height = cols * cell, rows * cell
    canvas = [bytearray(C_BG * width) for _ in range(height)]

    def paint(px, py, color, size):
        for dy in range(size):
            y = py + dy
            if 0 <= y < height:
                row = canvas[y]
                for dx in range(size):
                    x = px + dx
                    if 0 <= x < width:
                        i = x * 3
                        row[i:i + 3] = bytes(color)

    free_n = used_n = seat_n = block_n = disabled_n = 0
    numbers = []
    for k, c in layout.items():
        pos = _cell_pos(k, cols, rows)
        if not pos:
            continue
        r, col = pos
        typ = c.get("type")
        status = c.get("status")
        if typ == "seat":
            if c.get("enabled") is False:
                paint(col * cell + 1, r * cell + 1, C_DISABLED, cell - 2)
                disabled_n += 1
                continue
            seat_n += 1
            name = str(c.get("name") or "")
            is_free = (k in free_keys) if free_keys is not None else (status == "FREE")
            if name in blacklist:
                block_n += 1
                paint(col * cell + 1, r * cell + 1, C_BLOCK, cell - 2)
                numbers.append((r, col, name, C_TEXT_LIGHT))
            elif is_free:
                free_n += 1
                paint(col * cell + 1, r * cell + 1, C_FREE, cell - 2)
                numbers.append((r, col, name, C_TEXT_DARK))
            else:
                used_n += 1
                paint(col * cell + 1, r * cell + 1, C_USED, cell - 2)
                numbers.append((r, col, name, C_TEXT_DARK))
        elif typ == "desk":
            paint(col * cell + 1, r * cell + 1, C_DESK, cell - 2)

    # 网格线
    for r in range(rows):
        y = r * cell
        if 0 <= y < height:
            row = canvas[y]
            for x in range(width):
                row[x * 3:x * 3 + 3] = bytes(C_GRID)
    for col in range(cols):
        x = col * cell
        if 0 <= x < width:
            for y in range(height):
                i = x * 3
                canvas[y][i:i + 3] = bytes(C_GRID)

    # 座位号（放最后画，避免被网格线盖住）
    if show_numbers:
        scale = 2 if cell >= 22 else 1
        for r, col, name, color in numbers:
            if not name:
                continue
            w = _text_width(name, scale)
            x = col * cell + max(1, (cell - w) // 2)
            y = r * cell + max(1, (cell - 5 * scale) // 2)
            _draw_number(canvas, width, height, x, y, name, color, scale)

    _write_png(path, width, height, canvas)
    return path, {"seats": seat_n, "free": free_n, "used": used_n,
                   "blocked": block_n, "disabled": disabled_n}


# ====================================================== CAS 自动登录 ====
LIB_TOKEN_SAVE = TOKEN_FILE


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *a, **k):
        return None


class _CasSession:
    def __init__(self):
        self.jar = http.cookiejar.CookieJar()
        self.follow = urllib.request.build_opener(
            urllib.request.HTTPCookieProcessor(self.jar),
            urllib.request.HTTPSHandler(context=SSL_CTX))
        self.no_follow = urllib.request.build_opener(
            urllib.request.HTTPCookieProcessor(self.jar),
            urllib.request.HTTPSHandler(context=SSL_CTX),
            _NoRedirect())

    def get(self, url, follow=True):
        op = self.follow if follow else self.no_follow
        req = urllib.request.Request(url, headers={
            "User-Agent": UA, "Accept-Language": "zh-CN,zh;q=0.9"})
        try:
            with op.open(req, timeout=20) as r:
                return r.status, r.headers.get("Location"), r.read().decode("utf-8", "replace")
        except urllib.error.HTTPError as e:
            return e.code, e.headers.get("Location"), e.read().decode("utf-8", "replace")
        except Exception as e:  # noqa: BLE001
            return None, None, str(e)

    def post(self, url, data):
        body = urllib.parse.urlencode(data).encode()
        req = urllib.request.Request(url, data=body, method="POST", headers={
            "User-Agent": UA,
            "Accept-Language": "zh-CN,zh;q=0.9",
            "Content-Type": "application/x-www-form-urlencoded"})
        try:
            with self.follow.open(req, timeout=20) as r:
                return r.status, r.geturl(), r.read().decode("utf-8", "replace")
        except urllib.error.HTTPError as e:
            return e.code, e.geturl(), e.read().decode("utf-8", "replace")
        except Exception as e:  # noqa: BLE001
            return None, url, str(e)


def _captcha_visible(html):
    m = re.search(r'<div[^>]*id="captchaParent"[^>]*>', html or "")
    if not m:
        return False
    return "display: none" not in m.group(0) and "display:none" not in m.group(0)


def _looks_like_jwt(token):
    return bool(token) and token.startswith("eyJ") and token.count(".") == 2


def _find_token_in(text_url, body):
    text = (text_url or "") + " \n " + (body or "")
    for pat in (r"[?&#]token=([A-Za-z0-9._\-%]+)", r'"token"\s*:\s*"([A-Za-z0-9._\-]+)"'):
        m = re.search(pat, text)
        if m:
            return urllib.parse.unquote(m.group(1))
    return None


def _exchange_sso(jwt_token):
    """30 秒登录 JWT → 会话 token。"""
    url = LIB_BASE + "/rest/ssoAuth?token=" + urllib.parse.quote(jwt_token, safe="")
    body = urllib.parse.urlencode({"token": jwt_token}).encode()
    headers = _lib_signed_headers("POST")
    headers["Content-Type"] = "application/x-www-form-urlencoded"
    req = urllib.request.Request(url, data=body, headers=headers, method="POST")
    try:
        with urllib.request.urlopen(req, timeout=15, context=SSL_CTX) as r:
            obj = json.loads(r.read().decode("utf-8", "replace"))
    except urllib.error.HTTPError as e:
        return None, "ssoAuth HTTP %s" % e.code
    except Exception as e:  # noqa: BLE001
        return None, str(e)
    if obj.get("status") != "success":
        return None, str(obj.get("message") or obj)[:100]
    data = obj.get("data") or {}
    token = data.get("token") if isinstance(data, dict) else None
    return (token, None) if token else (None, "ssoAuth 没返回 token")


def _verify_token(token):
    if not token:
        return False
    return _lib_get("/rest/v2/user", token=token).get("status") == "success"


def _save_lib_token(token):
    try:
        _ensure_data_dir()
        with open(LIB_TOKEN_SAVE, "w", encoding="utf-8") as f:
            f.write(token)
        return True
    except OSError:
        return False


def _cas_login(user, password):
    """返回 (ok, token_or_message)。"""
    s = _CasSession()

    entry = LIB_BASE + "/remote/static/sso/login?redirectUrl=" + urllib.parse.quote(
        LIB_BASE + "/libseat/", safe="")
    _, cas_url, _ = s.get(entry, follow=False)
    if not cas_url:
        return False, "拿不到 CAS 跳转地址"

    st, _, html = s.get(cas_url)
    if st != 200:
        return False, "CAS 页面打不开（%s）" % st
    m = re.search(r'name="execution"[^>]*value="([^"]+)"', html)
    if not m:
        return False, "CAS 页面结构变了"
    if _captcha_visible(html):
        return False, "这次登录要求验证码"

    st, final_url, body = s.post(cas_url, {
        "username": user,
        "password": password,
        "submit": "LOGIN",
        "type": "username_password",
        "execution": m.group(1),
        "_eventId": "submit",
    })
    if st == 401 or "用户名或密码错误" in (body or "") or "Invalid credentials" in (body or ""):
        return False, "账号或密码错误"
    if st is None:
        return False, "请求失败：%s" % str(body)[:80]

    token = _find_token_in(final_url, body)
    if not token:
        m3 = re.search(r"[?&]ticket=([^&#]+)", final_url or "")
        if m3:
            cb = (LIB_BASE + "/remote/static/casAuth/getServiceByVerifyTicket/casLogin?ticket="
                  + m3.group(1))
            _, _, body2 = s.get(cb)
            token = _find_token_in(None, body2)
    if not token:
        return False, "CAS 通过但没拿到 token"

    if _looks_like_jwt(token):
        token, err = _exchange_sso(token)
        if not token:
            return False, "换会话 token 失败：%s" % err

    if not _verify_token(token):
        return False, "token 验证没通过"
    return True, token


# ================================================================ 插件 ====
@register("astrbot_plugin_upc", "kaoruko",
          "石大查询：空教室 / 附近教室 / 图书馆空座", "0.1.0")
class UPCPlugin(Star):
    def __init__(self, context: Context, config=None):
        super().__init__(context)
        self.config = config or {}
        self._token = None
        self._token_ts = 0.0

    # ---------------- 登录态管理 ----------------
    def _cfg(self, key, default=None):
        try:
            return self.config.get(key, default)
        except AttributeError:
            return default

    async def _get_token(self):
        """取图书馆 token：本地有效就用；失效则用配置里的账号密码自动登录。"""
        return await asyncio.to_thread(self._sync_token)

    def _sync_token(self):
        now = time.time()
        if self._token and now - self._token_ts < 60:
            return self._token

        # 1) 本地 token 还有效？
        token = _load_lib_token()
        if token and _verify_token(token):
            self._token, self._token_ts = token, now
            return token

        # 2) 用配置里的账号密码自动登录
        if str(self._cfg("auto_login", True)).lower() not in ("false", "0", "none"):
            user = str(self._cfg("username") or "").strip()
            pwd = str(self._cfg("password") or "").strip()
            if user and pwd:
                ok, result = _cas_login(user, pwd)
                if ok:
                    _save_lib_token(result)
                    self._token, self._token_ts = result, now
                    return result
        return None

    # ---------------- 空教室 ----------------
    @filter.command("空教室", alias={"空闲教室", "自习室"})
    async def cmd_freeclass(self, event: AstrMessageEvent):
        """查空教室：/空教室 [教学楼] [节次]"""
        args = _args(event, {"空教室", "空闲教室", "自习室"})
        building = "全部"
        periods_text = None
        if args:
            if _infer_building(args[0]) or args[0] in ("全部",):
                building = _infer_building(args[0]) or "全部"
                if len(args) > 1:
                    periods_text = args[1]
            else:
                periods_text = args[0]

        campus = "古镇口校区" if building == "卓越教学楼" else _infer_campus(
            " ".join(args))
        date = _today()
        periods = _parse_periods(periods_text)

        try:
            res = await asyncio.to_thread(_fc_query, campus, date, periods, building)
            text = _render_freeclass(res, building)
        except Exception as e:  # noqa: BLE001
            text = "⚠️ 查询失败：%s" % e
        yield event.plain_result(text)

    # ---------------- 附近教室 ----------------
    @filter.command("附近", alias={"附近教室"})
    async def cmd_nearby(self, event: AstrMessageEvent):
        """查某教室附近：/附近 南教305 [节次]"""
        args = _args(event, {"附近", "附近教室"})
        if not args:
            yield event.plain_result("用法：/附近 南教305 [节次]\n例：/附近 南教305 3-4")
            return
        periods = _parse_periods(args[1] if len(args) > 1 else None)
        try:
            nb = await asyncio.to_thread(_fc_find_nearby, args[0], _today(), periods)
            text = _render_nearby(nb)
        except Exception as e:  # noqa: BLE001
            text = "⚠️ 查询失败：%s" % e
        yield event.plain_result(text)

    # ---------------- 图书馆 ----------------
    @filter.command("图书馆", alias={"座位", "空座"})
    async def cmd_library(self, event: AstrMessageEvent):
        """图书馆：/图书馆 | 东馆 | 总馆 | 座位 <id> | 我的"""
        args = _args(event, {"图书馆", "座位", "空座"})
        sub = args[0] if args else ""
        date = _lib_default_date()
        window = None
        if sub in ("东馆", "总馆"):
            date, window = _split_date_window(args[1:], date)
        elif sub in ("地图", "示意图", "图", "空位", "安静", "筛选", "座位", "座位图"):
            date, window = _split_date_window(args[2:], date)
        image_path = None

        try:
            if not sub:
                text = await asyncio.to_thread(_lib_status_text)
            elif sub in ("东馆", "总馆"):
                token = await self._get_token()
                if not token:
                    text = ("⚠️ 房间级查询需要图书馆登录态。\n"
                            "在电脑上跑一次 login.bat（约 10 秒），或者先看 /图书馆 的实时空座。")
                else:
                    text = await asyncio.to_thread(
                        _lib_stats_text, sub, date, token, window)
            elif sub in ("空位", "安静", "筛选"):
                token = await self._get_token()
                if not token:
                    text = "⚠️ 查空位需要图书馆登录态（先在插件配置里填学号密码（或跑 login.bat））。"
                elif len(args) < 2 or not args[1].isdigit():
                    text = "用法：/图书馆 空位 <房间id>\n例：/图书馆 空位 2（阅览区1F-A）"
                else:
                    free_keys, err = await asyncio.to_thread(
                        _lib_free_keys, args[1], date, window, token)
                    if free_keys is None and window:
                        text = "⚠️ 按时间段查询失败：%s" % err
                    else:
                        text = await asyncio.to_thread(
                            _lib_quiet_seats_text, args[1], date, token,
                            blacklist=_blacklist_for(args[1]),
                            free_keys=free_keys)
            elif sub in ("座位", "座位图"):
                token = await self._get_token()
                if not token:
                    text = "⚠️ 查座位图需要图书馆登录态（先在插件配置里填学号密码（或跑 login.bat））。"
                elif len(args) < 2 or not args[1].isdigit():
                    text = "用法：/图书馆 座位 <房间id>\n例：/图书馆 座位 2"
                else:
                    free_keys, err = await asyncio.to_thread(
                        _lib_free_keys, args[1], date, window, token)
                    if free_keys is None and window:
                        text = "⚠️ 按时间段查询失败：%s" % err
                    else:
                        text = await asyncio.to_thread(
                            _lib_layout_text, args[1], date, token, free_keys, window)
            elif sub in ("我的", "预约"):
                token = await self._get_token()
                if not token:
                    text = "⚠️ 查预约需要图书馆登录态（先在插件配置里填学号密码（或跑 login.bat））。"
                else:
                    text = await asyncio.to_thread(_lib_reservations_text, token)
            elif sub in ("列表", "房间", "房间列表"):
                token = await self._get_token()
                if not token:
                    text = "⚠️ 查房间列表需要图书馆登录态（先在插件配置里填学号密码）。"
                else:
                    text = await asyncio.to_thread(
                        _lib_rooms_text, args[1] if len(args) > 1 else None, token)
            elif sub in ("拉黑", "屏蔽"):
                if len(args) < 3:
                    text = ("用法：/图书馆 拉黑 <房间id> <座位号...>\n"
                            "例：/图书馆 拉黑 2 007 008\n"
                            "座位号在地图或 /图书馆 座位 <房间id> 里能看到。")
                else:
                    room = str(args[1])
                    names = _parse_seat_names(args[2:])
                    bl = _load_blacklist()
                    cur = set(bl.get(room) or [])
                    cur.update(names)
                    bl[room] = sorted(cur)
                    if _save_blacklist(bl):
                        text = ("✅ 已拉黑房间 %s 的 %d 个座位：%s\n"
                                "现在共拉黑 %d 个。" % (room, len(names), "、".join(names), len(cur)))
                    else:
                        text = "⚠️ 保存黑名单失败（文件写不进去）"
            elif sub in ("取消拉黑", "解禁", "恢复"):
                if len(args) < 3:
                    text = "用法：/图书馆 取消拉黑 <房间id> <座位号...>"
                else:
                    room = str(args[1])
                    names = _parse_seat_names(args[2:])
                    bl = _load_blacklist()
                    cur = set(bl.get(room) or [])
                    removed = [n for n in names if n in cur]
                    cur -= set(names)
                    if cur:
                        bl[room] = sorted(cur)
                    else:
                        bl.pop(room, None)
                    text = ("✅ 已解除 %d 个：%s" % (len(removed), "、".join(removed))
                            if removed else "这些座位本来就不在黑名单里")
                    _save_blacklist(bl)
            elif sub in ("黑名单",):
                bl = _load_blacklist()
                if not bl:
                    text = "📋 黑名单是空的。\n用 /图书馆 拉黑 <房间id> <座位号> 添加。"
                else:
                    lines = ["📋 座位黑名单："]
                    for room, names in bl.items():
                        lines.append("  房间 %s：%s" % (room, "、".join(names)))
                    lines.append("")
                    lines.append("取消：/图书馆 取消拉黑 <房间id> <座位号>")
                    text = "\n".join(lines)
            elif sub in ("地图", "示意图", "图"):
                token = await self._get_token()
                if not token:
                    text = ("⚠️ 查座位示意图需要图书馆登录态。\n"
                            "先在插件配置里填学号密码（或跑 login.bat）。")
                elif len(args) < 2 or not args[1].isdigit():
                    text = "用法：/图书馆 地图 <房间id>\n例：/图书馆 地图 2（阅览区1F-A）"
                else:
                    obj = await asyncio.to_thread(
                        _lib_get,
                        "/rest/v2/room/layoutByDate/%s/%s" % (args[1], date),
                        token=token)
                    if obj.get("status") != "success":
                        text = "⚠️ 登录态失效了：%s" % (obj.get("message") or "接口异常")
                    else:
                        d = obj.get("data") or {}
                        free_keys, err = await asyncio.to_thread(
                            _lib_free_keys, args[1], date, window, token)
                        if free_keys is None and window:
                            text = "⚠️ 按时间段查询失败：%s" % err
                        else:
                            png = os.path.join(tempfile.gettempdir(),
                                               "upc_seat_%s.png" % args[1])
                            png, st = await asyncio.to_thread(
                                _render_layout_png, d, png, 26,
                                _blacklist_for(args[1]), True, free_keys)
                            image_path = png
                            when = _date_label(date)
                            if window:
                                when += " · %s-%s" % (_fmt_min(window[0]), _fmt_min(window[1]))
                            text = ("🪑 %s · %s\n空位 %d / 座位 %d（不可约 %d，黑名单 %d）\n"
                                    "图例：绿=空座  红=该时段已占/不可约  深黑=黑名单  "
                                    "浅灰=不可用  蓝=桌子  白=走廊"
                                    % (d.get("name"), when,
                                       st["free"], st["seats"], st["used"],
                                       st.get("blocked", 0)))
                        if st["seats"] > 0 and st["free"] == 0:
                            text += ("\n\n⚠️ 这一天全部显示为已占（可能已闭馆或不可预约）。\n"
                                     "试试：/图书馆 地图 %s 明天" % args[1])
                        elif st["seats"] == 0:
                            text += ("\n\n⚠️ 这一天的座位图是空的（可能已闭馆或还没开放）。\n"
                                     "试试指定日期：/图书馆 地图 %s 明天" % args[1])
            else:
                text = ("可用：\n"
                        "/图书馆          实时空座\n"
                        "/图书馆 东馆     各房间空位（需登录）\n"
                        "/图书馆 总馆\n"
                        "/图书馆 空位 2  找周围没人的座位（需登录）\n"
                        "/图书馆 座位 2  座位号（需登录）\n"
                        "/图书馆 我的    我的预约（需登录）")
        except Exception as e:  # noqa: BLE001
            text = "⚠️ 查询失败：%s" % e
        yield event.plain_result(text)
        if image_path:
            sent = False
            # 优先用本地文件图片（AstrBot 4.x 的 make_result().file_image）
            try:
                res = event.make_result()
                res.file_image(image_path)
                yield res
                sent = True
            except Exception:  # noqa: BLE001
                pass
            if not sent:
                try:
                    yield event.image_result(image_path)
                except Exception:  # noqa: BLE001 图片发不出去就算了，文字已经有了
                    pass

    # ---------------- 帮助 ----------------
    @filter.command("石大帮助", alias={"upc帮助"})
    async def cmd_help(self, event: AstrMessageEvent):
        yield event.plain_result(
            "🏫 石大查询\n\n"
            "/空教室 [楼] [节次]   例：/空教室 南教楼 3-4\n"
            "/附近 南教305 [节次]  看附近哪间空着\n"
            "/图书馆              实时空座 / 开馆时间\n"
            "/图书馆 东馆         各房间空位（需登录）\n"
            "/图书馆 列表         房间 id 列表（需登录）\n"
            "/图书馆 拉黑 2 007   拉黑座位（地图变深灰、不再推荐）\n"
            "/图书馆 黑名单       查看黑名单\n"
            "/图书馆 空位 2       找周围没人的座位（需登录）\n"
            "/图书馆 地图 2       座位示意图（需登录）\n"
            "                     可加日期/时间段：\n"
            "                     /图书馆 地图 2 明天 08:00-10:00\n"
            "/图书馆 东馆 08:00-10:00  房间空位（可按时间）\n"
            "/图书馆 座位 2       座位号（需登录）\n"
            "/图书馆 我的         预约记录（需登录）\n\n"
            "节次：上午/下午/晚上/白天/全天/3-4/10,11")
