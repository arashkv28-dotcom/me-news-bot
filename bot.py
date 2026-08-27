#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ربات خبری خاورمیانه -> کانال تلگرام

فیدهای RSS فارسی را می‌خواند، خبرهای تکراری را حذف می‌کند و هر خبر را
به‌صورت یک پست جداگانه در کانال تلگرام منتشر می‌کند.

بدون سرور: روی GitHub Actions هر ساعت یک‌بار اجرا می‌شود (کاملاً رایگان).

استفادهٔ محلی:
    export BOT_TOKEN="123:ABC..."
    export CHAT_ID="-1001234567890"
    python bot.py            # ارسال واقعی
    python bot.py --dry-run  # فقط نمایش، بدون ارسال
"""

from __future__ import annotations

import argparse
import html
import json
import os
import re
import sys
import time
import unicodedata
from datetime import datetime, timedelta, timezone
from pathlib import Path

import feedparser
import jdatetime
import requests

BASE = Path(__file__).resolve().parent
FEEDS_FILE = BASE / "feeds.json"
STATE_FILE = Path(os.environ.get("STATE_FILE", BASE / ".state" / "seen.json"))

TELEGRAM_API = "https://api.telegram.org/bot{token}/{method}"
USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
)

# ---------------------------------------------------------------- تنظیمات ---

TZ_TEHRAN = timezone(timedelta(hours=3, minutes=30))

MAX_PER_RUN = int(os.environ.get("MAX_PER_RUN", "6"))          # حداکثر پست در هر اجرا
MAX_AGE_HOURS = int(os.environ.get("MAX_AGE_HOURS", "24"))      # قدیمی‌تر از این ارسال نشود
SUMMARY_CHARS = int(os.environ.get("SUMMARY_CHARS", "420"))     # طول خلاصه
DELAY_SECONDS = float(os.environ.get("DELAY_SECONDS", "4"))     # فاصله بین پست‌ها (ضدفلود)
SEEN_LIMIT = int(os.environ.get("SEEN_LIMIT", "4000"))          # سقف حافظهٔ «دیده شده‌ها»
FIRST_RUN_MAX = int(os.environ.get("FIRST_RUN_MAX", "3"))       # در اولین اجرا فقط چند خبر
SKIP_NO_DATE = os.environ.get("SKIP_NO_DATE", "1") == "1"       # خبر بدون تاریخ رد شود؟

PERSIAN_RE = re.compile(r"[\u0600-\u06FF]")

# کلیدواژه‌های منطقهٔ خاورمیانه — اگر فید عمومی (مثل یورونیوز فارسی) خبری از
# کره جنوبی یا فرانسه داد، با این فهرست رد می‌شود.
# فیدهایی که در feeds.json برچسب "region": true دارند از این فیلتر معاف‌اند.
REGION_KEYWORDS = [
    # کشورها و مناطق
    "ایران", "ایرانی", "تهران", "خامن", "پزشکیان", "پاسداران", "بسیج", "مجلس شورای",
    "عراق", "بغداد", "اربیل", "کردستان عراق", "نجف", "بصره", "حشد",
    "سوریه", "دمشق", "حلب", "لاذقیه", "درعا", "ادلب",
    "لبنان", "بیروت", "حزب الله", "حزب‌الله", "ضاحیه", "نبیه بری",
    "فلسطین", "غزه", "کرانه باختری", "قدس", "بیت المقدس", "حماس", "فتح",
    "اسرائیل", "تل آویو", "نتانیاهو", " IDF", "ارتش اسرائیل",
    "یمن", "صنعا", "انصارالله", "حوثی", "حدیده", "باب المندب",
    "اردن", "عمان", "بحرین", "منامه", "کویت", "قطر", "دوحه",
    "عربستان", "ریاض", "جده", "نفت", "آرامکو", "محمد بن سلمان",
    "امارات", "دبی", "ابوظبی", "ابوظبی",
    "افغانستان", "کابل", "طالبان", "قندهار", "هرات",
    "ترکیه", "آنکارا", "استانبول", "اردوغان", "پ ک ک", "کردهای سوریه",
    "مصر", "قاهره", "سینا", "کانال سوئز", "غزه",
    "لیبی", "طرابلس", "سودان", "خارطوم", "تونس", "الجزایر", "مراکش",
    "آذربایجان", "باکو", "ارمنستان", "ایروان", "قره باغ", "قره‌باغ",
    "پاکستان", "اسلام آباد", "هند", "کشمیر",
    # نهادها و مفاهیم منطقه‌ای
    "آژانس بین المللی انرژی اتمی", "آژانس بین‌المللی انرژی اتمی", "آژانس",
    "برجام", "تحریم", "سانتریفیوژ", "غنی سازی", "غنی‌سازی", "اورانیوم", "نطنز", "فردو",
    "سپاه پاسداران", "سپاه", "نیروی قدس", "محور مقاومت", "نیابتی",
    "تنگه هرمز", "خلیج فارس", "دریای سرخ", "خاورمیانه", "خاور نزدیک",
    "اسلامی", "مسلمان", "شیعه", "سنی", "اسماعیلیه",
    "امریکا", "آمریکا", "ترامپ", "کاخ سفید", "پنتاگون", "ناو",
    "روسیه", "مسکو", "پوتین", "اوکراین", "کی یف", "کی‌یف",
    "چین", "پکن", "پوتین",
]

# الگوی کوتاه‌تر و سریع: اگر هیچ‌کدام نبود، خبر رد می‌شود
REGION_RE = re.compile("|".join(re.escape(k.strip()) for k in REGION_KEYWORDS if k.strip()))


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


def normalize(text: str) -> str:
    """تمیزکردن متن خبر: حذف HTML، نیم‌فاصله‌ها و فاصله‌های اضافه."""
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
    """تبدیل ارقام لاتین به فارسی (فقط برای زمان/تاریخ)."""
    table = str.maketrans("0123456789", "۰۱۲۳۴۵۶۷۸۹")
    return text.translate(table)


def clean_link(raw: str) -> str:
    """پارامترهای ردیابی را از لینک نمایشی پاک می‌کند."""
    if not raw:
        return ""
    raw = html.unescape(raw).strip()
    raw = re.sub(r"[?&](utm_[a-z]+|cmpid|fbclid|at_medium|at_campaign|at_bbc_team|at_ptr_name)=[^&]*", "", raw, flags=re.I)
    raw = re.sub(r"[?&]$", "", raw)
    return raw


def entry_id(entry) -> str:
    """شناسهٔ یکتا برای تشخیص خبر تکراری."""
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
    """۱۴۰۵/۰۶/۰۵ — ۱۷:۳۰ به وقت ایران"""
    local = dt.astimezone(TZ_TEHRAN)
    jd = jdatetime.datetime.fromgregorian(datetime=local)
    return f"{jd.year}/{jd.month:02d}/{jd.day:02d} — {jd.hour:02d}:{jd.minute:02d}"


# ---------------------------------------------------------------- فیدها ---

def fetch_feed(feed: dict):
    """یک فید را می‌گیرد و لیست خبرها را برمی‌گرداند."""
    name = feed["name"]
    try:
        resp = requests.get(
            feed["url"],
            timeout=25,
            headers={"User-Agent": USER_AGENT, "Accept": "*/*"},
        )
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
        is_region_feed = bool(feed.get("region", False))
        entries = fetch_feed(feed)
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

            summary_raw = (
                entry.get("summary")
                or entry.get("description")
                or (entry.get("content") or [{}])[0].get("value", "")
            )
            summary = normalize(summary_raw)
            # بعضی فیدها عنوان را در خلاصه تکرار می‌کنند
            if summary and summary[:40] == title[:40]:
                summary = summary[len(title):].lstrip(" .:-–—")
            if len(summary) > SUMMARY_CHARS:
                summary = summary[:SUMMARY_CHARS].rsplit(" ", 1)[0] + "…"

            if region_filter and not is_region_feed and not REGION_RE.search(title + " " + summary):
                dropped_region += 1
                continue

            link = clean_link(entry.get("link") or "")
            items.append(
                {
                    "id": entry_id(entry),
                    "title": title,
                    "summary": summary,
                    "link": link,
                    "source": name,
                    "published": published,
                }
            )

    if dropped_region:
        print(f"[info] {dropped_region} خبر غیرمرتبط با خاورمیانه فیلتر شد.")

    # حذف تکراری‌ها بر اساس شناسه، سپس بر اساس عنوان نزدیک به هم
    unique, by_title = [], {}
    for item in items:
        if not item["id"] or item["id"] in by_title:
            continue
        by_title[item["id"]] = item
        unique.append(item)
    unique.sort(key=lambda x: x["published"] or datetime.min.replace(tzinfo=timezone.utc), reverse=True)
    return unique


# ------------------------------------------------------------- تلگرام ---

def tg_call(token: str, method: str, payload: dict) -> dict:
    url = TELEGRAM_API.format(token=token, method=method)
    try:
        resp = requests.post(url, json=payload, timeout=30)
        data = resp.json()
    except (requests.RequestException, ValueError) as exc:
        return {"ok": False, "description": str(exc)}
    # کد وضعیت HTTP را هم در پاسخ نگه می‌داریم تا ۴۲۹ مطمئن تشخیص داده شود
    if not isinstance(data, dict):
        data = {"ok": False, "description": str(data)}
    data["http_status"] = resp.status_code
    return data


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
        href = item["link"]
        lines.append(f'🔗 <a href="{html.escape(href, quote=True)}">متن کامل خبر</a>')
    return "\n".join(lines)


def send_message(token: str, chat_id: str, text: str, dry_run: bool) -> bool:
    if dry_run:
        print("\n" + "=" * 60)
        print(text.replace("<b>", "").replace("</b>", "").replace("<i>", "").replace("</i>", ""))
        return True

    for attempt in range(3):
        result = tg_call(token, "sendMessage", {
            "chat_id": chat_id,
            "text": text,
            "parse_mode": "HTML",
            "disable_web_page_preview": False,
            "allow_sending_without_reply": True,
        })
        if result.get("ok"):
            return True

        desc = str(result.get("description", result))
        code = result.get("error_code") or result.get("http_status")
        if code == 429:  # flood limit
            wait = float(result.get("parameters", {}).get("retry_after", 5))
            print(f"[warn] محدودیت ارسال تلگرام، {wait:.0f} ثانیه صبر…")
            time.sleep(wait + 1)
            continue
        print(f"[error] ارسال ناموفق ({code}): {desc}")
        return False
    return False


# ---------------------------------------------------------------- اصلی ---

def main() -> int:
    parser = argparse.ArgumentParser(description="انتشار اخبار خاورمیانه در کانال تلگرام")
    parser.add_argument("--dry-run", action="store_true", help="فقط نمایش، بدون ارسال")
    parser.add_argument("--limit", type=int, help="حداکثر تعداد خبر در این اجرا")
    parser.add_argument("--force", action="store_true", help="نادیده‌گرفتن حافظهٔ «دیده شده» (برای تست)")
    parser.add_argument("--no-save", action="store_true", help="حافظه ذخیره نشود (برای تست)")
    args = parser.parse_args()

    token = os.environ.get("BOT_TOKEN", "")
    chat_id = os.environ.get("CHAT_ID", "")

    if not args.dry_run and (not token or not chat_id):
        print("[error] متغیرهای BOT_TOKEN و CHAT_ID تنظیم نشده‌اند.")
        return 1

    cfg = load_json(FEEDS_FILE, {"feeds": []})
    if not cfg.get("feeds"):
        print("[error] feeds.json خالی یا پیدا نشد.")
        return 1

    state = load_json(STATE_FILE, {"seen": {}})
    seen = state.get("seen", {})

    items = collect_items(cfg)
    print(f"[info] {len(items)} خبر از فیدهای فعال خوانده شد.")

    cutoff = datetime.now(timezone.utc) - timedelta(hours=MAX_AGE_HOURS)
    limit = args.limit or MAX_PER_RUN

    fresh = [
        it for it in items
        if it["published"] and it["published"] >= cutoff and (args.force or it["id"] not in seen)
    ]

    # اولین اجرا: فقط چند خبر منتشر کن و بقیه را «دیده‌شده» ثبت کن تا کانال سیل‌آسا نشود
    first_run = not seen and not args.force
    if first_run:
        for it in items:
            seen[it["id"]] = int(time.time())
        fresh = fresh[:FIRST_RUN_MAX]
        print(f"[info] اولین اجراست؛ فقط {len(fresh)} خبر منتشر و بقیه ثبت می‌شوند.")
    else:
        fresh = fresh[:limit]

    if not fresh:
        print("[info] خبر تازه‌ای نبود.")
        return 0

    print(f"[info] {len(fresh)} خبر تازه برای انتشار:")
    sent = 0
    for item in fresh:
        if send_message(token, chat_id, build_message(item), args.dry_run):
            seen[item["id"]] = int(time.time())
            sent += 1
            print(f"  ✔ {item['source']} | {item['title'][:60]}")
            if not args.dry_run:
                time.sleep(DELAY_SECONDS)
        else:
            print(f"  ✘ {item['title'][:60]}")

    # هرس حافظه: فقط SEEN_LIMIT مورد آخر نگه داشته شود
    if len(seen) > SEEN_LIMIT:
        keep = dict(sorted(seen.items(), key=lambda kv: kv[1], reverse=True)[:SEEN_LIMIT])
        seen = keep
    if args.no_save:
        print(f"[info] {sent} خبر منتشر شد (حافظه ذخیره نشد).")
    else:
        save_json(STATE_FILE, {"seen": seen, "updated": int(time.time())})
        print(f"[info] {sent} خبر منتشر شد. حافظه: {len(seen)} شناسه.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
