#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ربات خبری خاورمیانه -> کانال/گروه تلگرام + پنل کنترل در پی‌وی

دو حالت اجرا:
  1) python bot.py            اجرای یک‌باره (مخصوص GitHub Actions، هر ساعت)
  2) python bot.py serve      حالت زنده: پنل دکمه‌شیشه‌ای در پی‌وی، چند مقصد،
                              ارسال خودکار هر N دقیقه (مخصوص Termux/سرور)
  3) python bot.py web        حالت وب‌هوک برای میزبان ابری رایگان (Render و مشابه آن)؛
                              همان پنل دکمه‌شیشه‌ای، بدون نیاز به روشن‌بودن گوشی

متغیرهای حالت web (اختیاری ولی توصیه‌شده):
  GITHUB_TOKEN  توکن fine-grained گیت‌هاب (دسترسی Contents روی همین مخزن)
  GITHUB_REPO   مثل username/me-news-bot  <- حافظه در مخزن ذخیره می‌شود
  WEBHOOK_URL   اختیاری؛ روی Render خودکار از RENDER_EXTERNAL_URL ساخته می‌شود

متغیرهای محیطی:
  BOT_TOKEN   توکن BotFather (الزامی)
  CHAT_ID     اختیاری: مقصد پیش‌فرض اگر هنوز مقصدی اضافه نکرده‌اید
  OWNER_ID    اختیاری: شناسهٔ عددی مدیر؛ اگر خالی باشد، اولین /start مالک می‌شود
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import html
import json
import os
import random
import threading
import re
import sys
import time
import unicodedata
from datetime import datetime, timedelta, timezone
from pathlib import Path

from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import feedparser
import jdatetime
import requests

BASE = Path(__file__).resolve().parent
STATE_DIR = Path(os.environ.get("STATE_DIR", BASE / ".state"))
FEEDS_FILE = STATE_DIR / "feeds.json"
SEEN_FILE = STATE_DIR / "seen.json"
DESTS_FILE = STATE_DIR / "channels.json"
SETTINGS_FILE = STATE_DIR / "settings.json"
OFFSET_FILE = STATE_DIR / "offset.json"

TELEGRAM_API = "https://api.telegram.org/bot{token}/{method}"
USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
)

# ---------------------------------------------------------------- تنظیمات ---

TZ_TEHRAN = timezone(timedelta(hours=3, minutes=30))

MAX_PER_RUN = int(os.environ.get("MAX_PER_RUN", "6"))
MAX_AGE_HOURS = int(os.environ.get("MAX_AGE_HOURS", "24"))
SUMMARY_CHARS = int(os.environ.get("SUMMARY_CHARS", "420"))
DELAY_SECONDS = float(os.environ.get("DELAY_SECONDS", "3"))
SEEN_LIMIT = int(os.environ.get("SEEN_LIMIT", "4000"))
SKIP_NO_DATE = os.environ.get("SKIP_NO_DATE", "1") == "1"
FIRST_RUN_MAX = int(os.environ.get("FIRST_RUN_MAX", "3"))

INTERVAL_CHOICES = [15, 30, 60, 120, 180, 360]   # دقیقه

PERSIAN_RE = re.compile(r"[\u0600-\u06FF]")

# کلیدواژه‌های منطقهٔ خاورمیانه (فیدهای با برچسب region معاف‌اند)
REGION_KEYWORDS = [
    "ایران", "ایرانی", "تهران", "خامن", "پزشکیان", "پاسداران", "بسیج", "مجلس شورای",
    "عراق", "بغداد", "اربیل", "کردستان عراق", "نجف", "بصره", "حشد",
    "سوریه", "دمشق", "حلب", "لاذقیه", "درعا", "ادلب",
    "لبنان", "بیروت", "حزب الله", "حزب‌الله", "ضاحیه", "نبیه بری",
    "فلسطین", "غزه", "کرانه باختری", "قدس", "بیت المقدس", "حماس", "فتح",
    "اسرائیل", "تل آویو", "نتانیاهو", "ارتش اسرائیل",
    "یمن", "صنعا", "انصارالله", "حوثی", "حدیده", "باب المندب",
    "اردن", "عمان", "بحرین", "منامه", "کویت", "قطر", "دوحه",
    "عربستان", "ریاض", "جده", "نفت", "آرامکو", "محمد بن سلمان",
    "امارات", "دبی", "ابوظبی",
    "افغانستان", "کابل", "طالبان", "قندهار", "هرات",
    "ترکیه", "آنکارا", "استانبول", "اردوغان", "پ ک ک", "کردهای سوریه",
    "مصر", "قاهره", "سینا", "کانال سوئز",
    "لیبی", "طرابلس", "سودان", "خارطوم", "تونس", "الجزایر", "مراکش",
    "آذربایجان", "باکو", "ارمنستان", "ایروان", "قره باغ", "قره‌باغ",
    "پاکستان", "اسلام آباد", "هند", "کشمیر",
    "آژانس بین المللی انرژی اتمی", "آژانس بین‌المللی انرژی اتمی", "آژانس",
    "برجام", "تحریم", "سانتریفیوژ", "غنی سازی", "غنی‌سازی", "اورانیوم", "نطنز", "فردو",
    "سپاه پاسداران", "سپاه", "نیروی قدس", "محور مقاومت", "نیابتی",
    "تنگه هرمز", "خلیج فارس", "دریای سرخ", "خاورمیانه", "خاور نزدیک",
    "اسلامی", "مسلمان", "شیعه", "سنی",
    "امریکا", "آمریکا", "ترامپ", "کاخ سفید", "پنتاگون", "ناو",
    "روسیه", "مسکو", "پوتین", "اوکراین", "کی یف", "کی‌یف",
    "چین", "پکن",
]
REGION_RE = re.compile("|".join(re.escape(k.strip()) for k in REGION_KEYWORDS if k.strip()))


DEFAULT_FEEDS = {
    "region_filter": True,
    "feeds": [
        {"name": "بی‌بی‌سی فارسی", "url": "https://feeds.bbci.co.uk/persian/rss.xml", "lang": "fa", "enabled": True},
        {"name": "رادیو فردا", "url": "https://www.radiofarda.com/api/", "lang": "fa", "enabled": True},
        {"name": "یورونیوز فارسی", "url": "https://fa.euronews.com/rss?level=theme&name=news", "lang": "fa", "enabled": True},
        {"name": "صدای آمریکا", "url": "https://www.voanews.com/api/", "lang": "fa", "enabled": True, "require_persian": True},
        {"name": "الجزیره (عربی)", "url": "https://www.aljazeera.net/aljazeerarss/a7c186be-1baa-4bd4-9d80-a84db769f779/73d0e1b4-532f-45ef-b135-bfdff8b8cab9", "lang": "ar", "enabled": False, "region": True},
        {"name": "BBC Middle East", "url": "http://feeds.bbci.co.uk/news/world/middle_east/rss.xml", "lang": "en", "enabled": False, "region": True},
        {"name": "ایران اینترنشنال (تلگرام)", "channel": "iranintltv", "enabled": True},
        {"name": "رضاپهلوی (تلگرام)", "channel": "OfficialRezaPahlavi", "enabled": True},
        {"name": "ایران و جهان در لحظه (تلگرام)", "channel": "iran_jahan_darlahze", "enabled": True},
        {"name": "ایرنا", "url": "https://fa.irna.ir/rss/tp/1", "lang": "fa", "enabled": False,
         "note": "از سرورهای ابری در دسترس نیست"},
    ],
}


TG_DEFAULT_CHANNELS = [
    ("ایران اینترنشنال (تلگرام)", "iranintltv"),
    ("رضاپهلوی (تلگرام)", "OfficialRezaPahlavi"),
    ("ایران و جهان در لحظه (تلگرام)", "iran_jahan_darlahze"),
]


def ensure_feeds() -> None:
    if not FEEDS_FILE.exists():
        save_json(FEEDS_FILE, DEFAULT_FEEDS)
        print("[info] feeds.json پیش‌فرض ساخته شد")
        return
    # مهاجرت: افزودن کانال‌های تلگرامی پیش‌فرض که هنوز نیستند
    cfg = load_json(FEEDS_FILE, {})
    feeds = cfg.setdefault("feeds", [])
    have = {str(f.get("channel", "")).lower() for f in feeds}
    added = False
    for nm, ch in TG_DEFAULT_CHANNELS:
        if ch.lower() not in have:
            feeds.append({"name": nm, "channel": ch, "enabled": True})
            added = True
    if added:
        save_json(FEEDS_FILE, cfg)
        print("[info] منابع تلگرامی جدید به feeds اضافه شد")


# -------------------------------------------------------------- ابزارها ---

def load_json(path: Path, default):
    if not path.exists():
        return default
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        print(f"[warn] {path.name} خراب است، از مقدار پیش‌فرض استفاده می‌شود: {exc}")
        return default


def save_json(path: Path, data) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(data, ensure_ascii=False, indent=1), encoding="utf-8")
    tmp.replace(path)


# ------------------------------------------- همگام‌سازی حافظه با گیت‌هاب ---

SYNC_FILES = ("seen.json", "channels.json", "settings.json", "images.json", "images_state.json", "feeds.json")


class GitState:
    # حافظهٔ ربات را در مخزن گیت‌هاب نگه می‌دارد تا میزبان‌های بدون دیسک
    # (مثل Render رایگان) با هر ری‌استارت حافظه را از دست ندهند و چند حالت
    # اجرا (Actions + وب) بدون پست تکراری کنار هم کار کنند.

    def __init__(self, token: str, repo: str, branch: str = "main"):
        self.token = token
        self.repo = repo
        self.branch = branch
        self.base = os.environ.get("GITHUB_API", "https://api.github.com")
        self._hashes = {}
        self._lock = threading.Lock()
        self.last_error = ""

    def _req(self, method, path, payload=None):
        try:
            r = requests.request(method, self.base + path, json=payload, timeout=30,
                                 headers={"Authorization": "Bearer " + self.token,
                                          "Accept": "application/vnd.github+json"})
            try:
                return r.status_code, r.json()
            except ValueError:
                return r.status_code, {}
        except requests.RequestException as exc:
            self.last_error = str(exc)
            print(f"[warn] GitHub: {exc}")
            return 0, {}

    def pull(self):
        for name in SYNC_FILES:
            code, data = self._req("GET", f"/repos/{self.repo}/contents/.state/{name}?ref={self.branch}")
            if code == 200 and data.get("content"):
                try:
                    content = base64.b64decode(data["content"]).decode("utf-8")
                    (STATE_DIR / name).parent.mkdir(parents=True, exist_ok=True)
                    (STATE_DIR / name).write_text(content, encoding="utf-8")
                    self._hashes[name] = hashlib.sha256(content.encode()).hexdigest()
                    print(f"[info] حافظه از گیت‌هاب خواند شد: {name}")
                except Exception as exc:
                    print(f"[warn] pull {name}: {exc}")

    def push_file(self, path, force=False):
        name = path.name
        try:
            content = path.read_text(encoding="utf-8")
        except OSError:
            self.last_error = f"فایل محلی {name} نیست"
            return False
        h = hashlib.sha256(content.encode()).hexdigest()
        if not force and self._hashes.get(name) == h:
            return True
        b64 = base64.b64encode(content.encode()).decode()
        for _attempt in range(2):
            code, meta = self._req("GET", f"/repos/{self.repo}/contents/.state/{name}?ref={self.branch}")
            sha = meta.get("sha") if code == 200 else None
            payload = {"message": f"state: {name} [skip ci]", "content": b64, "branch": self.branch}
            if sha:
                payload["sha"] = sha
            code, meta = self._req("PUT", f"/repos/{self.repo}/contents/.state/{name}", payload)
            if code in (200, 201):
                self._hashes[name] = h
                return True
            self.last_error = f"HTTP {code}: {meta.get('message', '')}"
        print(f"[warn] push {name} ناموفق — {self.last_error}")
        return False

    def sync_report(self) -> dict:
        """تست واقعی اتصال: هر سه فایل حافظه را زورکی push می‌کند."""
        out = {}
        with self._lock:
            for name in SYNC_FILES:
                path = STATE_DIR / name
                if not path.exists():
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text("{}" if name.endswith(".json") else "", encoding="utf-8")
                out[name] = self.push_file(path, force=True)
        return out

    def sync(self):
        with self._lock:
            for name in SYNC_FILES:
                self.push_file(STATE_DIR / name)


STORE = None


def init_store():
    token = os.environ.get("GITHUB_TOKEN", "")
    repo = os.environ.get("GITHUB_REPO", "")
    if token and repo:
        return GitState(token, repo, os.environ.get("GITHUB_BRANCH", "main"))
    return None


def sync_state():
    if STORE:
        STORE.sync()


def normalize(text: str) -> str:
    if not text:
        return ""
    text = re.sub(r"<(script|style)[^>]*>.*?</\1>", " ", text, flags=re.S | re.I)
    text = re.sub(r"<br\s*/?>|</p>|</div>", "\n", text, flags=re.I)
    text = re.sub(r"<[^>]+>", " ", text)
    text = html.unescape(text)
    text = unicodedata.normalize("NFC", text)
    text = text.replace("\u200c", " ").replace("\u200f", "").replace("\u200e", "")
    text = re.sub(r"[ \t\u00a0]+", " ", text)
    text = re.sub(r"\n\s*\n+", "\n", text)
    return text.strip(" .\u200c-–—\n\t ")


def to_digits(text: str) -> str:
    return text.translate(str.maketrans("0123456789", "۰۱۲۳۴۵۶۷۸۹"))


def clean_link(raw: str) -> str:
    if not raw:
        return ""
    raw = html.unescape(raw).strip()
    raw = re.sub(r"[?&](utm_[a-z]+|cmpid|fbclid|at_medium|at_campaign|at_bbc_team|at_ptr_name)=[^&]*", "", raw, flags=re.I)
    raw = re.sub(r"[?&]$", "", raw)
    return raw


def fetch_tg_channel(feed: dict) -> list[dict]:
    """خواندن پیش‌نمایش عمومی یک کانال تلگرام از t.me/s — بدون لاگین."""
    import html as _html
    ch = str(feed.get("channel", "")).strip().lstrip("@")
    if not ch:
        return []
    try:
        resp = requests.get(f"https://t.me/s/{ch}", timeout=20,
                            headers={"User-Agent": USER_AGENT, "Accept": "*/*"})
        resp.raise_for_status()
        raw = resp.text
    except Exception as exc:  # noqa: BLE001
        print(f"[warn] کانال تلگرامی {ch}: {exc}")
        return []
    entries = []
    for b in raw.split("tgme_widget_message_wrap")[1:]:
        m = re.search(r'class="tgme_widget_message_text[^"]*"[^>]*>(.*?)</div>', b, re.S)
        if not m:
            continue
        txt = re.sub(r"<br\s*/?>", "\n", m.group(1))
        txt = _html.unescape(re.sub(r"<[^>]+>", "", txt)).strip()
        if len(txt) < 40:  # پیام‌های سرویسی مثل «عکس کانال به‌روز شد»
            continue
        link_m = re.search(r'href="(https://t\.me/[^"]+/\d+)"', b)
        time_m = re.search(r'datetime="([^"]+)"', b)
        link = link_m.group(1) if link_m else ""
        dt = None
        if time_m:
            try:
                dt = datetime.fromisoformat(time_m.group(1)).astimezone(timezone.utc)
            except ValueError:
                dt = None
        title = txt.split("\n", 1)[0][:110]
        summary = txt[len(title):].lstrip(" \n.:-–—")
        if len(summary) > SUMMARY_CHARS:
            summary = summary[:SUMMARY_CHARS].rsplit(" ", 1)[0] + "…"
        entries.append({
            "id": link, "title": title, "summary": summary, "link": link,
            "published_parsed": dt.timetuple() if dt else None,
        })
    return entries


def entry_id(entry) -> str:
    raw = entry.get("id") or entry.get("link") or entry.get("title") or ""
    raw = str(raw).strip()
    if not raw:
        return ""
    raw = raw.split("#")[0]
    raw = re.sub(r"[?&](utm_[a-z]+|cmpid|fbclid|at_medium|at_campaign|at_bbc_team|at_ptr_name)=[^&]*", "", raw, flags=re.I)
    raw = re.sub(r"[?&]$", "", raw)
    raw = re.sub(r"/+$", "", raw)
    return raw.lower()


def entry_time(entry) -> datetime | None:
    for key in ("published_parsed", "updated_parsed"):
        val = entry.get(key)
        if val:
            try:
                return datetime(*val[:6], tzinfo=timezone.utc)
            except (TypeError, ValueError):
                continue
    return None


def is_persian(text: str) -> bool:
    letters = [c for c in text if c.isalpha()]
    if not letters:
        return False
    return sum(1 for c in letters if PERSIAN_RE.match(c)) / len(letters) > 0.4


def jalali_stamp(dt: datetime) -> str:
    local = dt.astimezone(TZ_TEHRAN)
    jd = jdatetime.datetime.fromgregorian(datetime=local)
    return f"{jd.year}/{jd.month:02d}/{jd.day:02d} — {jd.hour:02d}:{jd.minute:02d}"


# ------------------------------------------------------------- کلاینت تلگرام ---

class Tg:
    """پوشش سبک روی Bot API با مدیریت خطا و ۴۲۹."""

    def __init__(self, token: str):
        self.token = token
        self._me = None

    def call(self, method: str, payload: dict | None = None, retries: int = 2) -> dict:
        url = TELEGRAM_API.format(token=self.token, method=method)
        for _ in range(retries + 1):
            try:
                resp = requests.post(url, json=payload or {}, timeout=40)
                data = resp.json()
            except (requests.RequestException, ValueError) as exc:
                return {"ok": False, "description": str(exc)}
            if not isinstance(data, dict):
                return {"ok": False, "description": str(data)}
            data["http_status"] = resp.status_code
            if (data.get("error_code") or resp.status_code) == 429:
                time.sleep(float(data.get("parameters", {}).get("retry_after", 3)) + 1)
                continue
            return data
        return {"ok": False, "description": "retry limit"}

    def me(self) -> dict:
        if self._me is None:
            r = self.call("getMe")
            self._me = r.get("result", {}) if r.get("ok") else {}
        return self._me

    def send(self, chat_id, text: str, markup=None, parse="HTML") -> dict:
        payload = {"chat_id": chat_id, "text": text, "parse_mode": parse,
                   "disable_web_page_preview": False}
        if markup:
            payload["reply_markup"] = {"inline_keyboard": markup}
        return self.call("sendMessage", payload)

    def edit(self, chat_id, message_id, text: str, markup=None) -> dict:
        payload = {"chat_id": chat_id, "message_id": message_id, "text": text,
                   "parse_mode": "HTML"}
        if markup:
            payload["reply_markup"] = {"inline_keyboard": markup}
        r = self.call("editMessageText", payload)
        if not r.get("ok") and "message is not modified" in str(r.get("description")):
            return {"ok": True}
        return r

    def answer(self, callback_query_id: str, text: str | None = None) -> None:
        payload = {"callback_query_id": callback_query_id}
        if text:
            payload["text"] = text
            payload["show_alert"] = False
        self.call("answerCallbackQuery", payload)

    def send_photo(self, chat_id, url: str, caption: str) -> dict:
        for attempt in range(2):
            r = self.call("sendPhoto", {"chat_id": chat_id, "photo": url,
                                        "caption": caption, "parse_mode": "HTML"})
            if r.get("ok"):
                return r
            desc = str(r.get("description", ""))
            if "429" in desc or (r.get("error_code") or 0) == 429:
                time.sleep(float(r.get("parameters", {}).get("retry_after", 3)) + 1)
                continue
            # لینک عکس از دسترس تلگرام خارج بود؟ یکی دیگر لازم است
            return r
        return {"ok": False, "description": "retry limit"}

    def get_updates(self, offset: int | None, timeout: int = 25) -> list:
        payload = {"timeout": timeout, "allowed_updates": ["message", "callback_query"]}
        if offset is not None:
            payload["offset"] = offset
        r = self.call("getUpdates", payload, retries=1)
        return r.get("result", []) if r.get("ok") else []

    def get_chat(self, chat_id) -> dict:
        return self.call("getChat", {"chat_id": chat_id})

    def chat_member(self, chat_id, user_id) -> dict:
        return self.call("getChatMember", {"chat_id": chat_id, "user_id": user_id})


# ---------------------------------------------------------------- فیدها ---

def fetch_feed(feed: dict):
    name = feed["name"]
    try:
        resp = requests.get(feed["url"], timeout=25,
                            headers={"User-Agent": USER_AGENT, "Accept": "*/*"})
    except requests.RequestException as exc:
        print(f"[warn] {name}: خطای شبکه — {exc}")
        return []
    if resp.status_code != 200:
        print(f"[warn] {name}: کد HTTP {resp.status_code}")
        return []
    parsed = feedparser.parse(resp.content)
    if not parsed.entries:
        print(f"[warn] {name}: خبری پیدا نشد (bozo={parsed.bozo})")
        return []
    return parsed.entries


def collect_items(cfg: dict) -> list[dict]:
    items = []
    dropped_region = 0
    region_filter = bool(cfg.get("region_filter", True))

    for feed in cfg.get("feeds", []):
        if not feed.get("enabled", True):
            continue
        name = feed["name"]
        is_region_feed = bool(feed.get("region", False)) or bool(feed.get("channel"))
        entries = fetch_tg_channel(feed) if feed.get("channel") else fetch_feed(feed)
        print(f"[info] {name}: {len(entries)} خبر")
        for entry in entries:
            title = normalize(entry.get("title", ""))
            if not title:
                continue
            if feed.get("require_persian") and not is_persian(title):
                continue

            published = entry_time(entry)
            if published is None and SKIP_NO_DATE:
                continue

            summary_raw = (entry.get("summary") or entry.get("description")
                           or (entry.get("content") or [{}])[0].get("value", ""))
            summary = normalize(summary_raw)
            if summary and summary[:40] == title[:40]:
                summary = summary[len(title):].lstrip(" .:-–—")
            if len(summary) > SUMMARY_CHARS:
                summary = summary[:SUMMARY_CHARS].rsplit(" ", 1)[0] + "…"

            if region_filter and not is_region_feed and not REGION_RE.search(title + " " + summary):
                dropped_region += 1
                continue

            items.append({
                "dests": feed.get("dests"),
                "id": entry_id(entry),
                "title": title,
                "summary": summary,
                "link": clean_link(entry.get("link") or ""),
                "source": name,
                "published": published,
            })

    if dropped_region:
        print(f"[info] {dropped_region} خبر غیرمرتبط با خاورمیانه فیلتر شد.")

    unique, seen_ids = [], set()
    for item in items:
        if not item["id"] or item["id"] in seen_ids:
            continue
        seen_ids.add(item["id"])
        unique.append(item)
    unique.sort(key=lambda x: x["published"] or datetime.min.replace(tzinfo=timezone.utc),
                reverse=True)
    return unique


def build_message(item: dict) -> str:
    stamp = jalali_stamp(item["published"]) if item["published"] else ""
    lines = [f"🔴 <b>{html.escape(item['title'])}</b>"]
    if item["summary"]:
        lines.append("")
        lines.append(html.escape(item["summary"]))
    lines.append("")
    lines.append(f"🕒 {to_digits(stamp)} (به وقت ایران)")
    lines.append(f"📰 منبع: {html.escape(item['source'])}")
    if item["link"]:
        lines.append(f'🔗 <a href="{html.escape(item["link"], quote=True)}">متن کامل خبر</a>')
    return "\n".join(lines)


# ---------------------------------------------------- مقصدها و تنظیمات ---

def load_dests() -> list:
    return load_json(DESTS_FILE, {"dests": []}).get("dests", [])


def save_dests(dests: list) -> None:
    save_json(DESTS_FILE, {"dests": dests, "updated": int(time.time())})


def load_settings() -> dict:
    s = load_json(SETTINGS_FILE, {})
    s.setdefault("owner_id", os.environ.get("OWNER_ID") or None)
    s.setdefault("interval_minutes", 60)
    s.setdefault("max_per_run", MAX_PER_RUN)
    s.setdefault("admins", [])
    return s


def save_settings(s: dict) -> None:
    save_json(SETTINGS_FILE, s)


def ensure_chat_id_dest(tg: Tg) -> None:
    """کانالِ متغیر CHAT_ID را برای همیشه به فهرست مقصدها اضافه می‌کند
    تا با افزودن کانال‌های دیگر از پنل، هرگز از قلم نیفتد."""
    cid = os.environ.get("CHAT_ID", "")
    if not cid:
        return
    dests = load_dests()
    key, title = cid, "(متغیر CHAT_ID)"
    r = tg.get_chat(cid)
    if r.get("ok"):
        key = r["result"]["id"]
        title = r["result"].get("title", title)
    if any(str(d["id"]) == str(key) for d in dests):
        return
    dests.insert(0, {"id": key, "title": title, "kind": "channel"})
    save_dests(dests)
    print(f"[info] کانال CHAT_ID به مقصدها اضافه شد: {title}")


def effective_dests() -> list:
    return load_dests()


# ------------------------------------------------------------ انتشار خبر ---

def publish_once(tg: Tg, dry_run: bool = False, limit: int | None = None,
                 force: bool = False) -> dict:
    cfg = load_json(FEEDS_FILE, {"feeds": []})
    if not cfg.get("feeds"):
        return {"error": "feeds.json خالی است"}

    dests = effective_dests()
    if not dests:
        return {"error": "هیچ مقصدی ثبت نشده (کانال/گروه اضافه کن یا CHAT_ID بگذار)"}

    seen = load_json(SEEN_FILE, {"seen": {}}).get("seen", {})
    items = collect_items(cfg)
    cutoff = datetime.now(timezone.utc) - timedelta(hours=MAX_AGE_HOURS)
    limit = limit or load_settings().get("max_per_run", MAX_PER_RUN)

    fresh = [it for it in items
             if it["published"] and it["published"] >= cutoff
             and (force or it["id"] not in seen)]

    first_run = not seen and not force and not dry_run
    if first_run:
        for it in items:
            seen[it["id"]] = int(time.time())
        fresh = fresh[:FIRST_RUN_MAX]
        print(f"[info] اولین اجراست؛ فقط {len(fresh)} خبر منتشر و بقیه ثبت می‌شوند.")
    else:
        fresh = fresh[:limit]

    stats = {"new_total": len(items), "fresh": len(fresh), "sent": 0, "errors": 0,
             "dests": len(dests)}
    if not fresh:
        print("[info] خبر تازه‌ای نبود.")
        return stats

    for item in fresh:
        text = build_message(item)
        if dry_run:
            print("=" * 50)
            print(re.sub(r"</?(b|i|a)[^>]*>", "", text))
            seen[item["id"]] = int(time.time())
            stats["sent"] += 1
            continue
        ok_all = True
        for d in dests:
            route = [str(x) for x in (item.get("dests") or [])]
            if route and str(d["id"]) not in route:
                continue
            r = tg.send(d["id"], text)
            if r.get("ok"):
                print(f"  ✔ {d['title'] if isinstance(d.get('title'), str) else d['id']} | {item['title'][:40]}")
            else:
                ok_all = False
                stats["errors"] += 1
                stats.setdefault("failed", []).append(str(d.get("title", d["id"])))
                print(f"  ✘ {d['id']}: {r.get('description')}")
            time.sleep(DELAY_SECONDS)
        if ok_all:
            seen[item["id"]] = int(time.time())
            stats["sent"] += 1

    if len(seen) > SEEN_LIMIT:
        seen = dict(sorted(seen.items(), key=lambda kv: kv[1], reverse=True)[:SEEN_LIMIT])
    if not dry_run:
        save_json(SEEN_FILE, {"seen": seen, "updated": int(time.time())})
    stats["memory"] = len(seen)
    print(f"[info] {stats['sent']} خبر به {len(dests)} مقصد منتشر شد.")
    sync_state()
    return stats


# ------------------------------------------------------------ تصویر روز ---

IMAGES_FILE = STATE_DIR / "images.json"
IMAGES_STATE = STATE_DIR / "images_state.json"
COMMONS_API = "https://commons.wikimedia.org/w/api.php"


def load_images_cfg() -> dict:
    d = load_json(IMAGES_FILE, {})
    d.setdefault("enabled", True)
    d.setdefault("categories", ["Reza_Shah", "Mohammad_Reza_Pahlavi",
                                "Pahlavi_dynasty", "Farah_Pahlavi"])
    d.setdefault("per_day", 1)
    d.setdefault("start_hour", 9)
    d.setdefault("gallery_dest", None)
    d.setdefault("terms", DEFAULT_TERMS)
    return d


def save_images_cfg(d: dict) -> None:
    save_json(IMAGES_FILE, d)


COMMONS_UA = "me-news-bot/1.0 (Telegram channel bot; personal project)"
IMAGES_POOL_FILE = STATE_DIR / "images_pool.json"


def _commons_get(params: dict) -> dict:
    """درخواست به API با بررسی وضعیت و یک تلاش مجدد در صورت ۴۲۹."""
    for attempt in range(2):
        try:
            r = requests.get(COMMONS_API, timeout=25,
                             headers={"User-Agent": COMMONS_UA}, params=params)
        except requests.RequestException:
            return {}
        if r.status_code == 200:
            try:
                return r.json()
            except ValueError:
                return {}
        if r.status_code == 429 and attempt == 0:
            time.sleep(6)
            continue
        return {}
    return {}


def _commons_files(cat: str) -> list:
    """فایل‌های یک رده + فایل‌های زیررده‌های یک‌سطحی آن."""
    out = []
    members = _commons_get({"action": "query", "list": "categorymembers",
                            "cmtitle": "Category:" + cat, "cmtype": "file|subcat",
                            "cmlimit": "50", "format": "json"}).get("query", {}).get("categorymembers", [])
    subs = []
    for m in members:
        t = m.get("title", "")
        if t.startswith("File:"):
            out.append(t)
        elif t.startswith("Category:"):
            subs.append(t)
    for sub in subs[:6]:
        m2 = _commons_get({"action": "query", "list": "categorymembers",
                           "cmtitle": sub, "cmtype": "file", "cmlimit": "30",
                           "format": "json"}).get("query", {}).get("categorymembers", [])
        out += [m.get("title", "") for m in m2 if m.get("title", "").startswith("File:")]
        time.sleep(1)
    return out


DEFAULT_TERMS = ["Pahlavi", "Reza Shah", "Mohammad Reza Pahlavi",
                 "Farah Pahlavi", "Iran Pahlavi"]


def _commons_search(term: str, limit: int = 25) -> list:
    """جست‌وجوی متنی فایل‌های تصویری در Commons — پوشش بسیار فراتر از رده‌ها."""
    d = _commons_get({"action": "query", "list": "search", "srsearch": term,
                      "srnamespace": "6", "srlimit": str(limit), "format": "json"})
    return [r.get("title", "") for r in d.get("query", {}).get("search", [])]


def load_pool(cfg: dict) -> list:
    """در لحظهٔ ارسال هیچ تماس API گرفته نمی‌شود (آی‌پی‌های ابری بلاک می‌شوند):
    استخر = کش امروز یا بانک آمادهٔ images_pool_seed.json."""
    jd = jdatetime.datetime.fromgregorian(datetime=datetime.now(TZ_TEHRAN))
    today = f"{jd.year}/{jd.month:02d}/{jd.day:02d}"
    cache = load_json(IMAGES_POOL_FILE, {"date": "", "pool": []})
    if (cache.get("date") == today and cache.get("pool")
            and isinstance(cache["pool"][0], dict)):
        return cache["pool"]
    items = [it for it in load_json(SEED_FILE, []) if isinstance(it, dict)]
    print(f"[info] بانک آمادهٔ عکس: {len(items)} آیتم")
    if items:
        save_json(IMAGES_POOL_FILE, {"date": today, "pool": items})
    return items or cache.get("pool", [])


SEED_FILE = BASE / "images_pool_seed.json"


def _resolve_items(titles: list) -> list:
    """عنوان فایل‌ها را به آیتم‌های دارای لینک مستقیم تبدیل می‌کند."""
    items = []
    for i in range(0, len(titles), 40):
        pages = _commons_get({"action": "query", "prop": "imageinfo",
                              "iiprop": "url|extmetadata", "iiurlwidth": "1024",
                              "titles": "|".join(titles[i:i + 40]),
                              "format": "json"}).get("query", {}).get("pages", {})
        for pg in pages.values():
            ii = (pg.get("imageinfo") or [{}])[0]
            url = ii.get("thumburl") or ii.get("url")
            if not url:
                continue
            lic = ((ii.get("extmetadata") or {}).get("LicenseShortName") or {}).get("value", "مشاهدهٔ منبع")
            items.append({"title": pg.get("title", ""), "url": url,
                          "page": ii.get("descriptionurl", ""), "license": lic})
        time.sleep(1)
    return items


def fetch_image_items(cfg: dict, want: int, seen: list):
    """برمی‌گرداند (items, error) — بدون نیاز به API در لحظهٔ ارسال."""
    pool = [it for it in load_pool(cfg)
            if isinstance(it, dict) and it.get("title") not in seen]
    if not pool:
        return [], "empty"
    random.shuffle(pool)
    return pool[:want], None


def clean_file_title(t: str) -> str:
    t = t.replace("File:", "", 1)
    t = re.sub(r"\.[A-Za-z]+$", "", t)
    t = t.replace("_", " ").strip()
    return t[:140]


def image_slots(cfg: dict) -> list:
    n = cfg["per_day"]
    step = 24.0 / n
    return sorted(int((cfg["start_hour"] + i * step) % 24) for i in range(n))


def post_images(tg: Tg, dry_run: bool = False, force: bool = False) -> dict:
    cfg = load_images_cfg()
    if not cfg["enabled"] and not force:
        return {"due": 0}
    st = load_json(IMAGES_STATE, {})
    st.setdefault("seen", [])
    st.setdefault("date", "")
    st.setdefault("posted_today", 0)
    now = datetime.now(TZ_TEHRAN)
    jd = jdatetime.datetime.fromgregorian(datetime=now)
    today = f"{jd.year}/{jd.month:02d}/{jd.day:02d}"
    if st.get("date") != today:
        st["date"] = today
        st["posted_today"] = 0

    if force:
        due = 1
    else:
        due = min(cfg["per_day"], sum(1 for h in image_slots(cfg) if h <= now.hour)) - st["posted_today"]
    if due <= 0:
        return {"due": 0}

    dest = cfg.get("gallery_dest") or os.environ.get("IMAGE_CHAT_ID")
    if not dest:
        print("[warn] تصویر روز: مقصد گالری انتخاب نشده (از پنل 🖼 یا IMAGE_CHAT_ID)")
        return {"due": 0, "error": "مقصد گالری انتخاب نشده؛ از منوی 🖼 یک کانال را 📌 بزن"}

    pool = load_pool(cfg)
    items, err = fetch_image_items(cfg, due, st["seen"])
    if err == "api":
        print("[warn] تصویر روز: ویکی‌مدیا پاسخ نداد (شلوغی/نرخ)")
        return {"due": due, "sent": 0, "api_error": True, "pool": len(pool)}
    sent = 0
    for it in items:
        stamp = jalali_stamp(now)
        caption = (f"🏛 <b>{html.escape(clean_file_title(it['title']))}</b>\n\n"
                   f"📜 از آرشیو تصاویر تاریخی ایران — دوران پهلوی\n"
                   f"🕒 {to_digits(stamp)}\n"
                   f'🔗 <a href="{html.escape(it["page"], quote=True)}">منبع و پروانهٔ اثر: {html.escape(it["license"])}</a>')
        if dry_run:
            print("=" * 40)
            print(re.sub(r"</?(b|a)[^>]*>", "", caption))
            print("   ", it["url"][:70])
            sent += 1
        else:
            r = tg.send_photo(dest, it["url"], caption)
            if r.get("ok"):
                print(f"  ✔ تصویر روز -> {dest}")
                sent += 1
            else:
                print(f"  ✘ تصویر روز: {r.get('description')}")
                continue
        st["seen"].append(it["title"])
        st["posted_today"] += 1
        time.sleep(DELAY_SECONDS)

    st["seen"] = st["seen"][-2000:]
    if not dry_run:
        save_json(IMAGES_STATE, st)
        sync_state()
    print(f"[info] تصویر روز: {sent} عکس ارسال شد.")
    return {"due": due, "sent": sent, "pool": len(pool)}


# ------------------------------------------------------------ پنل کنترل ---

def kb(rows):
    return rows


def btn(text, data=None, url=None):
    b = {"text": text}
    if data:
        b["callback_data"] = data
    if url:
        b["url"] = url
    return b


def main_menu_text(tg: Tg, settings: dict) -> str:
    dests = load_dests()
    cfg = load_json(FEEDS_FILE, {"feeds": []})
    on = sum(1 for f in cfg.get("feeds", []) if f.get("enabled", True))
    total = len(cfg.get("feeds", []))
    cloud = "✅ متصل به گیت‌هاب" if STORE else "⚠️ خاموش! تنظیمات با هر دیپلوی می‌پرد — GITHUB_TOKEN/GITHUB_REPO را در Render بگذار"
    return (
        "🎛 <b>پنل کنترل ربات خبری</b>\n\n"
        f"☁️ حافظهٔ ابری: {cloud}\n"
        f"📡 مقصدها: {to_digits(str(len(dests)))}\n"
        f"📰 منابع فعال: {to_digits(str(on))} از {to_digits(str(total))}\n"
        f"⏱ ارسال خودکار: هر {to_digits(str(settings.get('interval_minutes', 60)))} دقیقه\n"
        f"🔢 حداکثر خبر در هر نوبت: {to_digits(str(settings.get('max_per_run', MAX_PER_RUN)))}\n\n"
        "چه کاری انجام بدهم؟"
    )


def main_menu_kb():
    return kb([
        [btn("🔴 فوری خبر", "p:now"), btn("🖼 فوری عکس", "i:now")],
        [btn("📡 مقصدها", "d:list"), btn("📰 منابع خبری", "s:list")],
        [btn("🖼 تصویر روز", "i:main"), btn("⚙️ تنظیمات", "c:main")],
        [btn("👥 کاربران", "u:list"), btn("❓ راهنما", "h:show")],
    ])


def dests_text(dests: list) -> str:
    if not dests:
        return "📡 هنوز هیچ مقصدی نداری.\nبا دکمهٔ ➕ اضافه، اولین کانال یا گروه را اضافه کن."
    lines = ["📡 <b>مقصدهای فعال:</b>\n"]
    for i, d in enumerate(dests):
        kind = "📢" if d.get("kind") == "channel" else "👥"
        lines.append(f"{kind} {to_digits(str(i + 1))}. {html.escape(str(d.get('title', d['id'])))}")
    lines.append("\nبرای حذف، ❌ همان ردیف را بزن.")
    return "\n".join(lines)


def dests_kb(dests: list) -> list:
    rows = []
    for i, d in enumerate(dests):
        rows.append([btn(f"❌ {str(d.get('title', d['id']))[:24]}", f"d:rm:{i}")])
    rows.append([btn("➕ افزودن کانال/گروه", "d:add"), btn("🔙 بازگشت", "m:main")])
    return kb(rows)


def sources_text(cfg: dict) -> str:
    lines = ["📰 <b>منابع خبری:</b>\n"]
    for i, f in enumerate(cfg.get("feeds", [])):
        mark = "✅" if f.get("enabled", True) else "⛔️"
        lines.append(f"{mark} {to_digits(str(i + 1))}. {html.escape(f['name'])}")
    lines.append("\nبرای روشن/خاموش‌کردن، روی همان بزن.")
    return "\n".join(lines)


def sources_kb(cfg: dict) -> list:
    rows = []
    for i, f in enumerate(cfg.get("feeds", [])):
        mark = "✅" if f.get("enabled", True) else "⛔️"
        route = f.get("dests")
        rlabel = "🌐 همه" if not route else f"🎯 {to_digits(str(len(route)))}"
        rows.append([btn(f"{mark} {f['name'][:20]}", f"s:t:{i}"),
                     btn(rlabel, f"s:dst:{i}")])
    rows.append([btn("🔙 بازگشت", "m:main")])
    return kb(rows)


def sd_text(feed: dict, dests: list) -> str:
    route = [str(x) for x in feed.get("dests", [])]
    name = html.escape(feed.get("name", "?"))
    lines = [f"🎯 <b>مقصدهای «{name}»</b>\n"]
    if not dests:
        lines.append("هنوز مقصدی نداری؛ از 📡 مقصدها اضافه کن.")
        return "\n".join(lines)
    if not route:
        lines.append("🌐 الان به <b>همهٔ مقصدها</b> می‌رود.")
    else:
        lines.append("فقط به مقصدهای تیک‌خورده می‌رود:")
    for d in dests:
        mark = "✅" if str(d["id"]) in route else "⬜️"
        lines.append(f"{mark} {html.escape(str(d.get('title', d['id'])))}")
    lines.append("\nهر مقصد را بزنی انتخاب/حذف می‌شود؛ 🌐 یعنی همه.")
    return "\n".join(lines)


def sd_kb(feed: dict, idx: int, dests: list) -> list:
    route = [str(x) for x in feed.get("dests", [])]
    rows = [[btn("🌐 همهٔ مقصدها", f"sd:all:{idx}")]]
    for j, d in enumerate(dests):
        mark = "✅" if str(d["id"]) in route else "⬜️"
        rows.append([btn(f"{mark} {str(d.get('title', d['id']))[:26]}", f"sd:t:{idx}:{j}")])
    rows.append([btn("🔙 بازگشت", "sd:back")])
    return kb(rows)


def settings_text(settings: dict, cfg: dict) -> str:
    region = "روشن 🌍" if cfg.get("region_filter", True) else "خاموش"
    return (
        "⚙️ <b>تنظیمات</b>\n\n"
        f"⏱ فاصلهٔ ارسال خودکار: هر {to_digits(str(settings['interval_minutes']))} دقیقه\n"
        f"🔢 حداکثر خبر هر نوبت: {to_digits(str(settings['max_per_run']))}\n"
        f"🌍 فیلتر «فقط خاورمیانه»: {region}\n"
    )


def settings_kb(settings: dict, cfg: dict) -> list:
    iv = settings["interval_minutes"]
    region_on = cfg.get("region_filter", True)
    return kb([
        [btn("⏱ −", "c:i:-"), btn(f"هر {to_digits(str(iv))} دقیقه", "c:i:0"), btn("⏱ +", "c:i:+")],
        [btn("🔢 −", "c:l:-"), btn(f"حداکثر {to_digits(str(settings['max_per_run']))}", "c:l:0"), btn("🔢 +", "c:l:+")],
        [btn("🌍 فیلتر خاورمیانه: " + ("روشن" if region_on else "خاموش"), "c:r")],
        [btn("☁️ تست حافظه", "c:cloud")],
        [btn("🔙 بازگشت", "m:main")],
    ])


def hour_kb(cfg: dict) -> list:
    rows, row = [], []
    for h in range(24):
        mark = "📌 " if h == cfg["start_hour"] else ""
        row.append(btn(f"{mark}{to_digits(f'{h:02d}')}", f"i:hs:{h}"))
        if len(row) == 6:
            rows.append(row)
            row = []
    rows.append([btn("🔙 بازگشت", "i:main")])
    return kb(rows)


def users_text(settings: dict) -> str:
    lines = ["👥 <b>کاربران مجاز پنل</b>\n",
             f"👑 مالک: {to_digits(str(settings['owner_id']))}"]
    for i, a in enumerate(settings.get("admins", [])):
        lines.append(f"{to_digits(str(i + 1))}. {html.escape(a.get('name') or '—')} "
                     f"({to_digits(str(a['id']))})")
    lines.append("\n➕ افزودن: یک کد ۴رقمی می‌گیری، به شخص می‌دهی و او در پی‌وی ربات کد را می‌فرستد.")
    return "\n".join(lines)


def users_kb(settings: dict) -> list:
    rows = []
    for i, a in enumerate(settings.get("admins", [])):
        rows.append([btn(f"❌ {(a.get('name') or str(a['id']))[:24]}", f"u:rm:{i}")])
    rows.append([btn("➕ کد دسترسی", "u:add"), btn("🔙 بازگشت", "m:main")])
    return kb(rows)


def images_text(cfg: dict, dests: list) -> str:
    status = "روشن ✅" if cfg["enabled"] else "خاموش ⛔️"
    slots = "، ".join(to_digits(f"{h:02d}:00") for h in image_slots(cfg))
    gtitle = "— هنوز انتخاب نشده"
    for d in dests:
        if d["id"] == cfg.get("gallery_dest"):
            gtitle = f"«{d.get('title', d['id'])}»"
    return (
        "🖼 <b>تصویر روز</b>\n\n"
        f"وضعیت: {status}\n"
        f"🔢 تعداد در روز: {to_digits(str(cfg['per_day']))}\n"
        f"⏰ ساعت‌ها: {slots} (به وقت ایران)\n"
        f"📡 کانال گالری: {gtitle}\n\n"
        + ("👆 برای انتخاب کانال عکس، روی نام یکی از کانال‌های پایین بزن.\n" if gtitle.startswith("—") else "")
        + "موضوع فعلی: آرشیو تاریخی دوران پهلوی (Wikimedia Commons)"
    )


def images_kb(cfg: dict, dests: list) -> list:
    status = "✅ روشن" if cfg["enabled"] else "⛔️ خاموش"
    rows = [
        [btn(status, "i:tg"), btn(f"⏰ ساعت: {to_digits(str(cfg['start_hour']))} (انتخاب)", "i:h")],
        [btn("🔢 −", "i:p:-"), btn(f"روزی {to_digits(str(cfg['per_day']))}", "i:p:0"), btn("🔢 +", "i:p:+")],
    ]
    if dests:
        for i, d in enumerate(dests):
            mark = "📌" if d["id"] == cfg.get("gallery_dest") else "📡"
            rows.append([btn(f"{mark} {str(d.get('title', d['id']))[:28]}", f"i:d:{i}")])
    else:
        rows.append([btn("➕ اول از «مقصدها» کانالی اضافه کن", "d:add")])
    rows.append([btn("🔙 بازگشت", "m:main")])
    return kb(rows)


HELP_TEXT = (
    "❓ <b>راهنما</b>\n\n"
    "📡 <b>افزودن مقصد:</b> ربات را در کانال/گروه موردنظر «مدیر» کن (با تیک ارسال پیام)، "
    "بعد از دکمهٔ ➕ اضافه، یکی از این‌ها را همین‌جا بفرست:\n"
    "• آیدی با @ مثل @mychannel\n"
    "• یا یک پست از همان کانال/گروه را فوروارد کن\n"
    "• یا شناسهٔ عددی مثل -1001234567890\n\n"
    "🔴 <b>ارسال فوری:</b> همین حالا تازه‌ترین خبرها را به همهٔ مقصدها می‌فرستد.\n"
    "👥 <b>کاربران:</b> مالک می‌تواند با کد ۴رقمی، به دیگران هم دسترسی پنل بدهد.\n"
    "⏱ <b>ارسال خودکار:</b> هر N دقیقه یک‌بار خودش خبر تازه می‌فرستد.\n"
)


def render(tg: Tg, chat_id, message_id, view: str, settings: dict):
    cfg = load_json(FEEDS_FILE, {"feeds": []})
    dests = load_dests()
    if view == "main":
        r = tg.edit(chat_id, message_id, main_menu_text(tg, settings), main_menu_kb())
    elif view == "dests":
        r = tg.edit(chat_id, message_id, dests_text(dests), dests_kb(dests))
    elif view == "sources":
        ensure_feeds()
        cfg = load_json(FEEDS_FILE, {"feeds": []})
        r = tg.edit(chat_id, message_id, sources_text(cfg), sources_kb(cfg))
    elif view.startswith("sd:"):
        ensure_feeds()
        idx = int(view.split(":", 1)[1])
        _cfg = load_json(FEEDS_FILE, {"feeds": []})
        _feeds = _cfg.get("feeds", [])
        _feed = _feeds[idx] if 0 <= idx < len(_feeds) else {}
        r = tg.edit(chat_id, message_id, sd_text(_feed, dests), sd_kb(_feed, idx, dests))
    elif view == "settings":
        r = tg.edit(chat_id, message_id, settings_text(settings, cfg), settings_kb(settings, cfg))
    elif view == "images":
        icfg = load_images_cfg()
        r = tg.edit(chat_id, message_id, images_text(icfg, dests), images_kb(icfg, dests))
    elif view == "ipick":
        rows = [[btn(f"🖼 {str(d.get('title', d['id']))[:28]}", f"i:pick:{i}")]
                for i, d in enumerate(dests)]
        rows.append([btn("🔙 بازگشت", "m:main")])
        r = tg.edit(chat_id, message_id,
                    "🖼 عکس‌ها به کدام کانال فرستاده شود؟\n"
                    "(یک‌بار انتخاب کن؛ بعداً از «تصویر روز» قابل تغییر است)", kb(rows))
    elif view == "ihour":
        icfg = load_images_cfg()
        r = tg.edit(chat_id, message_id, "⏰ ساعت ارسال اولین عکس را انتخاب کن:", hour_kb(icfg))
    elif view == "users":
        r = tg.edit(chat_id, message_id, users_text(settings), users_kb(settings))
    elif view == "help":
        r = tg.edit(chat_id, message_id, HELP_TEXT, kb([[btn("🔙 بازگشت", "m:main")]]))
    else:
        r = {"ok": True}
    if not r.get("ok"):
        # اگر edit نشد (مثلاً پیام حذف شده)، پیام جدید بفرست
        tg.send(chat_id, "بروزرسانی نشد؛ /start بزن.")
    return r


# ------------------------------------------------------------ افزودن مقصد ---

def parse_dest_input(tg: Tg, msg: dict):
    """از متن یا پیام فورواردشده، مقصد را استخراج و اعتبارسنجی می‌کند."""
    chat_id = None
    fwd = msg.get("forward_from_chat") or {}
    if fwd.get("id"):
        chat_id = fwd["id"]
    elif msg.get("text"):
        raw = msg["text"].strip()
        if raw.startswith("@") and len(raw) > 3:
            chat_id = raw
        elif re.fullmatch(r"-?\d{5,}", raw):
            chat_id = int(raw)
    if chat_id is None:
        return None, ("❌ نفهمیدم. یکی از این‌ها را بفرست:\n"
                       "• @username\n• شناسهٔ عددی (-100…)\n• یا فوروارد یک پست از مقصد")

    r = tg.get_chat(chat_id)
    if not r.get("ok"):
        return None, f"❌ پیدا نکردم: {r.get('description')} (مطمئن شو ربات عضو آنجا شده)"
    chat = r["result"]
    kind = chat.get("type", "")
    if kind not in ("channel", "supergroup", "group"):
        return None, "❌ این یک کانال/گروه نیست."

    # بررسی دسترسی ربات
    me_id = tg.me().get("id")
    warn = ""
    if me_id:
        m = tg.chat_member(chat["id"], me_id)
        st = (m.get("result") or {}).get("status", "")
        if kind == "channel" and st != "administrator":
            warn = "\n⚠️ من آنجا «مدیر» نیستم! تا خبرها برود، مرا با تیک ارسال پیام مدیر کن."
        if kind in ("group", "supergroup") and st in ("left", "kicked"):
            return None, "❌ من عضو آن گروه نیستم؛ اول مرا عضو کن."
    return {"id": chat["id"], "title": chat.get("title", str(chat["id"])), "kind": kind}, warn


# --------------------------------------------------------------- حلقهٔ زنده ---

def serve(tg: Tg) -> int:
    me = tg.me()
    if not me.get("id"):
        print("[error] توکن نامعتبر است (getMe ناموفق).")
        return 1
    print(f"[info] حالت زنده شروع شد: @{me.get('username')}")

    settings = load_settings()
    offset = load_json(OFFSET_FILE, {"offset": None}).get("offset")
    waiting = {}
    next_auto = time.time() + 60  # یک دقیقه تنفس اولیه

    while True:
        updates = tg.get_updates(offset, timeout=25)
        for up in updates:
            offset = up["update_id"] + 1
            save_json(OFFSET_FILE, {"offset": offset})
            try:
                handle_update(tg, up, settings, waiting)
            except Exception as exc:  # نباید حلقه بمیرد
                print(f"[error] خطا در پردازش update: {exc}")

        post_images(tg)

        if time.time() >= next_auto:
            settings = load_settings()
            print(f"[info] ارسال خودکار (هر {settings['interval_minutes']} دقیقه)…")
            publish_once(tg)
            next_auto = time.time() + settings["interval_minutes"] * 60


def is_owner(settings: dict, user_id: int) -> bool:
    owner = settings.get("owner_id")
    if owner in (None, "", "None"):
        return False
    return int(user_id) == int(owner)


def is_admin(settings: dict, user_id: int) -> bool:
    if is_owner(settings, user_id):
        return True
    return any(int(a.get("id", -1)) == int(user_id) for a in settings.get("admins", []))


def handle_update(tg: Tg, up: dict, settings: dict, waiting: dict):
    if "callback_query" in up:
        cb = up["callback_query"]
        uid = cb["from"]["id"]
        chat_id = cb["message"]["chat"]["id"]
        msg_id = cb["message"]["message_id"]
        data = cb.get("data", "")
        tg.answer(cb["id"])

        if not is_admin(settings, uid):
            tg.answer(cb["id"], "🔒 فقط مدیر")
            return

        part = data.split(":")
        if data == "m:main":
            render(tg, chat_id, msg_id, "main", settings)
        elif data == "d:list":
            render(tg, chat_id, msg_id, "dests", settings)
        elif data == "d:add":
            waiting[uid] = "dest"
            tg.edit(chat_id, msg_id,
                    "📥 <b>افزودن مقصد</b>\n\n"
                    "اول ربات را در کانال/گروه «مدیر» کن، بعد یکی را بفرست:\n"
                    "• @username\n• شناسهٔ عددی\n• فوروارد یک پست از مقصد\n\n"
                    "برای انصراف: /cancel",
                    kb([[btn("🔙 بازگشت", "d:list")]]))
        elif part[0] == "d" and part[1] == "rm":
            dests = load_dests()
            idx = int(part[2])
            if 0 <= idx < len(dests):
                removed = dests.pop(idx)
                save_dests(dests)
                tg.answer(cb["id"], f"حذف شد: {removed.get('title', '')}")
            render(tg, chat_id, msg_id, "dests", settings)
        elif data == "p:now":
            tg.answer(cb["id"], "⏳ در حال ارسال…")
            stats = publish_once(tg)
            if stats.get("error"):
                tg.send(chat_id, f"❌ {stats['error']}")
            elif stats["fresh"] == 0:
                tg.send(chat_id, "🤷 خبر تازه‌ای نبود.")
            else:
                extra = ""
                if stats.get("failed"):
                    extra = "\n⚠️ خطا در: " + "، ".join(stats["failed"])
                tg.send(chat_id, f"✅ {to_digits(str(stats['sent']))} خبر به "
                                 f"{to_digits(str(stats['dests']))} مقصد فرستاده شد" + extra)
            render(tg, chat_id, msg_id, "main", settings)
        elif data == "s:list":
            render(tg, chat_id, msg_id, "sources", settings)
        elif part[0] == "s" and part[1] == "t":
            ensure_feeds()
            cfg = load_json(FEEDS_FILE, {"feeds": []})
            idx = int(part[2])
            feeds = cfg.get("feeds", [])
            if 0 <= idx < len(feeds):
                feeds[idx]["enabled"] = not feeds[idx].get("enabled", True)
                save_json(FEEDS_FILE, cfg)
                sync_state()
            render(tg, chat_id, msg_id, "sources", settings)
        elif part[0] == "s" and part[1] == "dst":
            idx = int(part[2])
            render(tg, chat_id, msg_id, f"sd:{idx}", settings)
        elif part[0] == "sd" and part[1] == "all":
            idx = int(part[2])
            cfg = load_json(FEEDS_FILE, {"feeds": []})
            feeds = cfg.get("feeds", [])
            if 0 <= idx < len(feeds):
                feeds[idx]["dests"] = []
                save_json(FEEDS_FILE, cfg)
                sync_state()
            render(tg, chat_id, msg_id, f"sd:{idx}", settings)
        elif part[0] == "sd" and part[1] == "t":
            idx, j = int(part[2]), int(part[3])
            cfg = load_json(FEEDS_FILE, {"feeds": []})
            feeds = cfg.get("feeds", [])
            dl = load_dests()
            if 0 <= idx < len(feeds) and 0 <= j < len(dl):
                cur = [str(x) for x in feeds[idx].get("dests", [])]
                did = str(dl[j]["id"])
                if did in cur:
                    cur.remove(did)
                else:
                    cur.append(did)
                feeds[idx]["dests"] = cur
                save_json(FEEDS_FILE, cfg)
                sync_state()
            render(tg, chat_id, msg_id, f"sd:{idx}", settings)
        elif data == "sd:back":
            render(tg, chat_id, msg_id, "sources", settings)
        elif data == "c:main":
            render(tg, chat_id, msg_id, "settings", settings)
        elif part[0] == "c" and part[1] == "i" and part[2] in "+-":
            cur = settings["interval_minutes"]
            idx = INTERVAL_CHOICES.index(cur) if cur in INTERVAL_CHOICES else 2
            idx = min(len(INTERVAL_CHOICES) - 1, max(0, idx + (1 if part[2] == "+" else -1)))
            settings["interval_minutes"] = INTERVAL_CHOICES[idx]
            save_settings(settings)
            render(tg, chat_id, msg_id, "settings", settings)
        elif part[0] == "c" and part[1] == "l" and part[2] in "+-":
            cur = settings["max_per_run"]
            cur = min(15, max(1, cur + (1 if part[2] == "+" else -1)))
            settings["max_per_run"] = cur
            save_settings(settings)
            render(tg, chat_id, msg_id, "settings", settings)
        elif data == "c:r":
            ensure_feeds()
            cfg = load_json(FEEDS_FILE, {"feeds": []})
            cfg["region_filter"] = not cfg.get("region_filter", True)
            save_json(FEEDS_FILE, cfg)
            sync_state()
            render(tg, chat_id, msg_id, "settings", settings)
        elif data == "i:now":
            icfg = load_images_cfg()
            if not icfg.get("gallery_dest"):
                if not load_dests():
                    tg.send(chat_id, "❌ اول از 📡 مقصدها یک کانال اضافه کن.")
                else:
                    tg.answer(cb["id"])
                    render(tg, chat_id, msg_id, "ipick", settings)
                return
            tg.answer(cb["id"], "⏳ در حال ارسال عکس…")
            try:
                r = post_images(tg, force=True)
            except Exception as exc:
                import traceback
                try:
                    LAST_ERROR_FILE.write_text(traceback.format_exc(), encoding="utf-8")
                except OSError:
                    pass
                tg.send(chat_id, f"❌ خطای فنی: {exc}")
                render(tg, chat_id, msg_id, "main", settings)
                return
            if r.get("error"):
                tg.send(chat_id, f"❌ {r['error']}")
            elif r.get("api_error"):
                tg.send(chat_id, "⚠️ ویکی‌مدیا موقتاً جواب نداد؛ چند دقیقهٔ دیگر دوباره بزن.")
            elif r.get("sent", 0) == 0:
                tg.send(chat_id, f"🤷 چیزی برای ارسال نیست. (اندازهٔ بانک: "
                                 f"{to_digits(str(r.get('pool', 0)))} عکس)")
            else:
                tg.send(chat_id, f"🖼 {to_digits(str(r['sent']))} عکس به کانال گالری رفت.")
            render(tg, chat_id, msg_id, "main", settings)
        elif part[0] == "i" and part[1] == "pick":
            dests = load_dests()
            idx = int(part[2])
            if 0 <= idx < len(dests):
                icfg = load_images_cfg()
                icfg["gallery_dest"] = dests[idx]["id"]
                save_images_cfg(icfg)
                sync_state()
                r = post_images(tg, force=True)
                title = html.escape(str(dests[idx].get("title", "")))
                if r.get("sent", 0):
                    tg.send(chat_id, f"🖼 {to_digits(str(r['sent']))} عکس به «{title}» رفت.\n"
                                     "از این به بعد عکس‌ها خودکار همین‌جا می‌روند.")
                elif r.get("api_error"):
                    tg.send(chat_id, "⚠️ ویکی‌مدیا موقتاً جواب نداد؛ چند دقیقهٔ دیگر دوباره بزن.")
                elif not r.get("error"):
                    tg.send(chat_id, "🤷 همهٔ عکس‌های موجود ارسال شده‌اند؛ فردا عکس‌های تازه می‌آید.")
            render(tg, chat_id, msg_id, "main", settings)
        elif data == "i:main":
            render(tg, chat_id, msg_id, "images", settings)
        elif data == "i:tg":
            icfg = load_images_cfg()
            icfg["enabled"] = not icfg["enabled"]
            save_images_cfg(icfg)
            sync_state()
            render(tg, chat_id, msg_id, "images", settings)
        elif data == "i:h":
            render(tg, chat_id, msg_id, "ihour", settings)
        elif part[0] == "i" and part[1] == "hs":
            icfg = load_images_cfg()
            icfg["start_hour"] = int(part[2])
            save_images_cfg(icfg)
            sync_state()
            render(tg, chat_id, msg_id, "images", settings)
        elif part[0] == "i" and part[1] == "p" and part[2] in "+-":
            icfg = load_images_cfg()
            icfg["per_day"] = min(24, max(1, icfg["per_day"] + (1 if part[2] == "+" else -1)))
            save_images_cfg(icfg)
            sync_state()
            render(tg, chat_id, msg_id, "images", settings)
        elif part[0] == "i" and part[1] == "d":
            dests = load_dests()
            idx = int(part[2])
            if 0 <= idx < len(dests):
                icfg = load_images_cfg()
                icfg["gallery_dest"] = dests[idx]["id"]
                save_images_cfg(icfg)
                sync_state()
                tg.answer(cb["id"], f"گالری: {dests[idx].get('title', '')}")
            render(tg, chat_id, msg_id, "images", settings)
        elif data == "u:list":
            if not is_owner(settings, uid):
                tg.answer(cb["id"], "🔒 فقط مالک")
                return
            render(tg, chat_id, msg_id, "users", settings)
        elif data == "u:add":
            if not is_owner(settings, uid):
                tg.answer(cb["id"], "🔒 فقط مالک")
                return
            code = "%04d" % random.randint(0, 9999)
            settings["pending_code"] = {"code": code, "ts": int(time.time())}
            save_settings(settings)
            sync_state()
            tg.send(uid, f"🔑 کد دسترسی: <b>{to_digits(code)}</b>\n\n"
                         "این کد را به شخص موردنظر بده؛ او در پی‌وی ربات همین کد را بفرستد.\n"
                         "(۱۰ دقیقه معتبر است)")
            render(tg, chat_id, msg_id, "users", settings)
        elif part[0] == "u" and part[1] == "rm":
            if not is_owner(settings, uid):
                tg.answer(cb["id"], "🔒 فقط مالک")
                return
            idx = int(part[2])
            admins = settings.get("admins", [])
            if 0 <= idx < len(admins):
                removed = admins.pop(idx)
                save_settings(settings)
                sync_state()
                tg.answer(cb["id"], f"حذف شد: {removed.get('name', removed['id'])}")
            render(tg, chat_id, msg_id, "users", settings)
        elif data == "c:cloud":
            if not STORE:
                missing = [k for k in ("GITHUB_TOKEN", "GITHUB_REPO") if not os.environ.get(k)]
                tg.send(chat_id, "☁️ حافظهٔ ابری خاموش است.\n"
                                 "در Environment رندر این متغیرها لازم است: " + "، ".join(missing))
            else:
                rep = STORE.sync_report()
                lines = ["☁️ نتیجه تست حافظه:"]
                for name, ok in rep.items():
                    lines.append(("✅ " if ok else "❌ ") + name + ("" if ok else f" — {STORE.last_error}"))
                if any(not ok for ok in rep.values()):
                    if "404" in STORE.last_error:
                        lines.append("\n💡 404 یعنی GITHUB_TOKEN به این مخزن دسترسی ندارد "
                                     "(یا GITHUB_REPO غلط است) — نه اینکه فایل نباشد. "
                                     "یک توکن Classic با تیک public_repo بساز و در Render جایگزین کن.")
                    elif "401" in STORE.last_error:
                        lines.append("\n💡 401 یعنی خودِ توکن نامعتبر است؛ دوباره کپی‌اش کن.")
                tg.send(chat_id, "\n".join(lines))
            render(tg, chat_id, msg_id, "settings", settings)
        elif data == "h:show":
            render(tg, chat_id, msg_id, "help", settings)
        return

    msg = up.get("message")
    if not msg:
        return
    uid = msg["from"]["id"]
    chat = msg["chat"]
    text = (msg.get("text") or "").strip()

    if chat["type"] != "private":
        if text.startswith("/start"):
            uname = tg.me().get("username", "")
            tg.send(chat["id"], "🎛 کنترل من فقط در پی‌وی است:",
                    kb([[btn("🎛 باز کردن پنل کنترل", url=f"https://t.me/{uname}")]]))
        return

    if text in ("/start", "/menu"):
        if settings.get("owner_id") in (None, "", "None"):
            settings["owner_id"] = uid
            save_settings(settings)
            tg.send(uid, "🎉 تو <b>مدیر</b> این ربات شدی.\n\n" + main_menu_text(tg, settings),
                    main_menu_kb())
        elif is_owner(settings, uid):
            tg.send(uid, main_menu_text(tg, settings), main_menu_kb())
        else:
            tg.send(uid, "🔒 این ربات شخصی است.\nاگر کد دسترسی داری، همین‌جا بفرست.")
        return

    if chat["type"] == "private" and not is_admin(settings, uid):
        pc = settings.get("pending_code") or {}
        if re.fullmatch(r"\d{4,6}", text) and pc.get("code") == text and time.time() - pc.get("ts", 0) < 600:
            settings.setdefault("admins", []).append(
                {"id": uid, "name": (msg["from"].get("first_name") or ""), "added": int(time.time())})
            settings.pop("pending_code", None)
            save_settings(settings)
            sync_state()
            tg.send(uid, "🎉 دسترسی شما فعال شد.", main_menu_kb())
            if settings.get("owner_id"):
                tg.send(int(settings["owner_id"]),
                        f"👥 «{html.escape(msg['from'].get('first_name') or '')}» به پنل اضافه شد.")
            return

    if text == "/cancel":
        waiting.pop(uid, None)
        tg.send(uid, "باشه، لغو شد.", kb([[btn("🎛 منوی اصلی", "m:main")]]))
        return

    if waiting.get(uid) == "dest" and is_admin(settings, uid):
        dest, warn = parse_dest_input(tg, msg)
        if dest is None:
            tg.send(uid, warn or "❌")
            return
        dests = load_dests()
        if any(d["id"] == dest["id"] for d in dests):
            tg.send(uid, "ℹ️ این مقصد قبلاً اضافه شده.", dests_kb(dests))
        else:
            dests.append(dest)
            save_dests(dests)
            kind = "📢 کانال" if dest["kind"] == "channel" else "👥 گروه"
            tg.send(uid, f"✅ اضافه شد: {kind} «{html.escape(dest['title'])}»\n"
                         f"از این به بعد خبرها آنجا هم می‌رود.{warn or ''}",
                    dests_kb(dests))
        waiting.pop(uid, None)
        return

    # پیام ناشناخته در پی‌وی مدیر
    if is_admin(settings, uid):
        tg.send(uid, "دکمه‌ها را از منوی اصلی بزن 🙂", kb([[btn("🎛 منوی اصلی", "m:main")]]))
    else:
        tg.send(uid, "🔒 این ربات شخصی است.\nاگر کد دسترسی داری، همین‌جا بفرست.")
    sync_state()



# ------------------------------------------------------------ حالت وب ---

WEBHOOK_SECRET = ""
PUBLISH_LOCK = threading.Lock()
VERSION = "v8-diag"
BOOT_TS = time.time()
LAST_ERROR_FILE = STATE_DIR / "last_error.txt"


def _safe_post_images(tg):
    try:
        post_images(tg)
    except Exception:
        import traceback
        try:
            LAST_ERROR_FILE.write_text(traceback.format_exc(), encoding="utf-8")
        except OSError:
            pass
        print("[error] post_images crash")


def _spawn_publish(tg, chat_id=None, settings=None):
    """انتشار در پس‌زمینه تا وب‌هوک سریع جواب بدهد."""
    if not PUBLISH_LOCK.acquire(blocking=False):
        if chat_id:
            tg.send(chat_id, "⏳ یک ارسال دیگر در جریان است؛ چند لحظه بعد.")
        return False

    def work():
        try:
            stats = publish_once(tg)
            if chat_id:
                if stats.get("error"):
                    tg.send(chat_id, f"❌ {stats['error']}")
                elif stats["fresh"] == 0:
                    tg.send(chat_id, "🤷 خبر تازه‌ای نبود.")
                else:
                    extra = ""
                    if stats.get("failed"):
                        extra = "\n⚠️ خطا در: " + "، ".join(stats["failed"])
                    tg.send(chat_id, f"✅ {to_digits(str(stats['sent']))} خبر به "
                                     f"{to_digits(str(stats['dests']))} مقصد فرستاده شد." + extra)
        finally:
            PUBLISH_LOCK.release()

    threading.Thread(target=work, daemon=True).start()
    return True


def due_check(tg):
    """با هر پینگ خارجی بررسی می‌کند وقت ارسال خودکار رسیده یا نه."""
    settings = load_settings()
    last = settings.get("last_auto", 0)
    if time.time() - last >= settings["interval_minutes"] * 60:
        settings["last_auto"] = int(time.time())
        save_settings(settings)
        sync_state()
        _spawn_publish(tg)
        threading.Thread(target=_safe_post_images, args=(tg,), daemon=True).start()
        return True
    threading.Thread(target=_safe_post_images, args=(tg,), daemon=True).start()
    return False


class WebHandler(BaseHTTPRequestHandler):
    tg = None

    def log_message(self, *a):
        pass

    def _out(self, code=200, body="ok"):
        raw = body.encode()
        self.send_response(code)
        self.send_header("Content-Type", "text/plain; charset=utf-8")
        self.send_header("Content-Length", str(len(raw)))
        self.end_headers()
        self.wfile.write(raw)

    def do_GET(self):
        if self.path.startswith("/tick") or self.path == "/":
            due_check(self.tg)
            self._out(200, "alive")
        elif self.path.startswith("/health"):
            self._out(200, "healthy")
        elif self.path.startswith("/diag"):
            info = {"version": VERSION, "uptime_s": int(time.time() - BOOT_TS),
                    "seed_exists": SEED_FILE.exists(),
                    "seed_n": len(load_json(SEED_FILE, [])) if SEED_FILE.exists() else 0,
                    "pool_cache": IMAGES_POOL_FILE.exists(),
                    "store": bool(STORE)}
            icfg = load_images_cfg()
            st = load_json(IMAGES_STATE, {})
            now = datetime.now(TZ_TEHRAN)
            info.update({"enabled": icfg["enabled"], "dest": icfg.get("gallery_dest"),
                         "per_day": icfg["per_day"], "hour_now": now.hour,
                         "date": st.get("date"), "posted": st.get("posted_today"),
                         "seen": len(st.get("seen", []))})
            ss = load_settings()
            info["last_auto"] = ss.get("last_auto")
            info["interval"] = ss.get("interval_minutes")
            try:
                info["last_error"] = LAST_ERROR_FILE.read_text(encoding="utf-8")[-400:]
            except OSError:
                info["last_error"] = None
            self._out(200, json.dumps(info, ensure_ascii=False))
        else:
            self._out(404, "not found")

    def do_POST(self):
        if not self.path.startswith("/webhook"):
            self._out(404, "not found")
            return
        secret = self.headers.get("X-Telegram-Bot-Api-Secret-Token", "")
        if WEBHOOK_SECRET and secret != WEBHOOK_SECRET:
            self._out(403, "forbidden")
            return
        n = int(self.headers.get("Content-Length", 0))
        try:
            up = json.loads(self.rfile.read(n) or b"{}")
        except ValueError:
            self._out(400, "bad json")
            return

        def work():
            settings = load_settings()
            waiting = WEB_WAITING
            try:
                handle_update(self.tg, up, settings, waiting)
                sync_state()
            except Exception as exc:
                print(f"[error] خطا در پردازش update: {exc}")

        threading.Thread(target=work, daemon=True).start()
        self._out(200, '{"ok":true}')


WEB_WAITING = {}


def web(tg) -> int:
    global WEBHOOK_SECRET, STORE
    STORE = STORE or init_store()
    if STORE:
        STORE.pull()
    ensure_chat_id_dest(tg)
    sync_state()

    port = int(os.environ.get("PORT", "8080"))
    url = os.environ.get("WEBHOOK_URL", "")
    if not url:
        ext = os.environ.get("RENDER_EXTERNAL_URL", "").rstrip("/")
        url = ext + "/webhook" if ext else ""

    if url:
        WEBHOOK_SECRET = os.environ.get("WEBHOOK_SECRET", "") or ("sns-" + tg.token[-10:])
        r = tg.call("setWebhook", {"url": url, "secret_token": WEBHOOK_SECRET,
                                   "drop_pending_updates": True})
        print(f"[info] setWebhook -> {url} : {r.get('ok')} {r.get('description', '')}")
    else:
        print("[warn] WEBHOOK_URL/RENDER_EXTERNAL_URL نیست؛ وب‌هوک تنظیم نشد.")

    WebHandler.tg = tg
    srv = ThreadingHTTPServer(("0.0.0.0", port), WebHandler)
    print(f"[info] حالت وب روی پورت {port} آماده است.")
    srv.serve_forever()
    return 0


# ---------------------------------------------------------------- اصلی ---


def main() -> int:
    parser = argparse.ArgumentParser(description="ربات خبری خاورمیانه")
    parser.add_argument("mode", nargs="?", choices=["serve", "web"],
                        help="serve = زندهٔ پنل‌دار | web = وب‌هوک برای میزبان ابری")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--force", action="store_true")
    parser.add_argument("--no-save", action="store_true")
    args = parser.parse_args()

    token = os.environ.get("BOT_TOKEN", "")
    if not token:
        if args.dry_run:
            token = "DRY-RUN"   # در حالت نمایش، نیازی به توکن واقعی نیست
        else:
            print("[error] متغیر BOT_TOKEN تنظیم نشده است.")
            return 1

    global STORE
    STORE = init_store()
    ensure_feeds()
    print(f"[info] همگام‌سازی حافظه با گیت‌هاب: {'فعال -> ' + STORE.repo if STORE else 'غیرفعال'}")

    tg = Tg(token)

    if args.mode == "serve":
        if STORE:
            STORE.pull()
        ensure_chat_id_dest(tg)
        return serve(tg)

    if args.mode == "web":
        ensure_chat_id_dest(tg)
        return web(tg)

    if not os.environ.get("CHAT_ID") and not load_dests():
        print("[error] مقصدی نیست: CHAT_ID بگذار یا اول در حالت serve مقصد اضافه کن.")
        return 1

    ensure_feeds()
    ensure_chat_id_dest(tg)
    stats = publish_once(tg, dry_run=args.dry_run, limit=args.limit, force=args.force)
    if stats.get("error"):
        print(f"[error] {stats['error']}")
        return 1
    post_images(tg, dry_run=args.dry_run)
    return 0


if __name__ == "__main__":
    sys.exit(main())
