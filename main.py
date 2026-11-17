import os
import re
import sqlite3
import logging
import time
import random
import asyncio
import secrets
import subprocess
from collections import deque
from contextlib import contextmanager
from datetime import datetime, timedelta
import json

from aiogram import Bot, Dispatcher, types
from aiogram.types import (
    Message, CallbackQuery, InlineKeyboardMarkup, InlineKeyboardButton,
    ReplyKeyboardMarkup, KeyboardButton, InputFile
)
from aiogram.dispatcher import FSMContext
from aiogram.dispatcher.filters.state import State, StatesGroup
from aiogram.dispatcher.filters import Text
from aiogram.contrib.fsm_storage.memory import MemoryStorage
from aiogram.utils.exceptions import BadRequest, BotBlocked

try:
    from fastapi import FastAPI
    import uvicorn
    FASTAPI_AVAILABLE = True
except ImportError:
    FASTAPI_AVAILABLE = False

# =====================================================================
# CONFIGURATION
# =====================================================================
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(name)s - %(message)s"
)
logger = logging.getLogger(__name__)

BOT_TOKEN = "8975254518:AAFY94fuFTRiuq7vfmVIwUBMoqvhXCy8qk8"
if not BOT_TOKEN:
    logger.warning("BOT_TOKEN bo'sh!")

SUPER_ADMIN_ID = 8648138832
CHANNEL_ID = -1004485992940
MAIN_CHANNEL_ID = -1003877551889
ADMIN_GROUP_ID = -1002094440970
CHANNEL_USERNAME = "uzmovi_va_asl_mediya"
ADMIN_LINK = "https://t.me/ll_e_o_n_001"

bot = Bot(token=BOT_TOKEN)
storage = MemoryStorage()
dp = Dispatcher(bot, storage=storage)

BOT_START_TIME = time.time()
ERROR_COUNT = 0

_bot_username_cache = None

async def get_bot_username() -> str:
    global _bot_username_cache
    if not _bot_username_cache:
        try:
            me = await bot.get_me()
            _bot_username_cache = me.username
        except Exception as e:
            logger.error(f"Bot username olishda xatolik: {e}")
            _bot_username_cache = "Premium_kinolari_bot"
    return _bot_username_cache

GENRES_LIST = ["Jangari", "Komediya", "Drama", "Melodrama", "Detektiv", "Multfilm", "Fantastika"]
GENRE_TEMPLATES = {
    "Jangari": "🎬 Kechga ko'rish uchun ajoyib film topib qo'ydim ",
    "Komediya": "😂 Siz bu filmni aniq ko'rmagansz,ko'ring va kuling ",
    "Drama": "🎭 Dramma ishqibozlari uchun ajoyib film",
    "Melodrama": "💔 Sevgi, sadoqat va hiyonatni aks etirgan ta'sirchan film",
    "Detektiv": "🔍 Detektiv janriga nima deysiz ?",
    "Multfilm": "🎨 Beg'ubor bolalikni eslab, Ajoyib multfilm topib qo'ydim",
    "Fantastika": "🚀 Inson taffakurining qanchalar cheksiz ekanini ko'rsatuvchi film"
}

app = None
if FASTAPI_AVAILABLE:
    app = FastAPI()

    @app.get("/")
    async def index():
        return {"status": "Kino Bot v4.2.0 (aiogram 2.25.1) is running 24/7 successfully"}

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.path.join(BASE_DIR, 'database.db')
STATUS_EXPORT_PATH = os.path.join(BASE_DIR, 'status_export.json')

last_request_time = {}

# =====================================================================
# DB HELPER
# =====================================================================
@contextmanager
def db_connect():
    conn = sqlite3.connect(DB_PATH, timeout=10)
    try:
        conn.execute("PRAGMA journal_mode=WAL;")
        conn.execute("PRAGMA busy_timeout=10000;")
        cursor = conn.cursor()
        yield conn, cursor
    finally:
        conn.close()

def get_last_main_channel_code() -> int:
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT value FROM bot_settings WHERE key = 'last_main_channel_code'")
        row = cursor.fetchone()
    return int(row[0]) if row and row[0] is not None else 0

def set_last_main_channel_code(code: int):
    with db_connect() as (conn, cursor):
        cursor.execute(
            "INSERT OR REPLACE INTO bot_settings (key, value) VALUES ('last_main_channel_code', ?)",
            (str(code),)
        )
        conn.commit()

def is_code_already_posted(code: int) -> bool:
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT 1 FROM main_channel_posts WHERE code = ?", (code,))
        return cursor.fetchone() is not None

# =====================================================================
# RAM KESHLAR (write-through) — 9-band: "🧹 Keshni tozalash" shularni tozalaydi
# =====================================================================
_role_cache = {}        # user_id -> {"role", "vip_expires_at", "restricted_until"}
_settings_cache = {}    # key -> value (str)
_movie_meta_cache = {}  # code(str) -> {"secret_message_id", "is_vip"}
_movie_stats_cache = {} # code(str) -> (likes, dislikes, views_count)
_saved_cache = {}       # user_id -> set(movie_code str)
_daily_free_cache = {}  # user_id -> {"date": "YYYY-MM-DD", "count": int}

_vip_sales_log = deque(maxlen=50)   # faqat RAM: {"user_id","days","granted_at","source"}
_bot_errors_log = deque(maxlen=50)  # faqat RAM: {"text","occurred_at"}
_broadcast_log = {}                 # faqat RAM: broadcast_id -> [(user_id, message_id), ...]
_broadcast_log_order = deque(maxlen=10)
_cache_clear_in_progress = False  # "Keshni tozalash" ikki marta tez bosilishidan himoya

# ---- Oldingi bo'lim (panel)ni avtomatik yopish — fizik tugma bosilganda ----
_last_section_msg = {}  # user_id -> (chat_id, message_id) — oxirgi ochilgan "bo'lim" xabari

async def _close_previous_section(user_id: int):
    """Foydalanuvchi yangi bo'limga (fizik tugma orqali) o'tganda, avvalgi ochiq
    bo'limning inline tugmalarini olib tashlaydi — shu bilan eski va yangi tugmalar
    bir-biriga xalaqit bermaydi."""
    entry = _last_section_msg.pop(user_id, None)
    if entry:
        chat_id, msg_id = entry
        try:
            await bot.edit_message_reply_markup(chat_id=chat_id, message_id=msg_id, reply_markup=None)
        except Exception:
            pass

def _register_section_message(user_id: int, sent_msg):
    """Yangi ochilgan bo'lim xabarini (inline tugmali) keyingi safar yopish uchun eslab qoladi."""
    if sent_msg is not None:
        try:
            _last_section_msg[user_id] = (sent_msg.chat.id, sent_msg.message_id)
        except Exception:
            pass

def _record_broadcast(broadcast_id: str, entries: list):
    _broadcast_log_order.append(broadcast_id)
    _broadcast_log[broadcast_id] = entries
    current_ids = set(_broadcast_log_order)
    for bid in list(_broadcast_log.keys()):
        if bid not in current_ids:
            _broadcast_log.pop(bid, None)

def _clear_all_caches():
    _role_cache.clear()
    _settings_cache.clear()
    _movie_meta_cache.clear()
    _daily_free_cache.clear()
    _movie_stats_cache.clear()
    _saved_cache.clear()

def get_setting(key: str, default=None):
    if key in _settings_cache:
        return _settings_cache[key]
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT value FROM bot_settings WHERE key = ?", (key,))
        row = cursor.fetchone()
    val = row[0] if row and row[0] is not None else default
    _settings_cache[key] = val
    return val

def set_setting(key: str, value):
    with db_connect() as (conn, cursor):
        cursor.execute("INSERT OR REPLACE INTO bot_settings (key, value) VALUES (?, ?)", (key, str(value)))
        conn.commit()
    _settings_cache[key] = str(value)

VIP_FIXED_PRICES = [(3, "3 kun", 2000), (10, "10 kun", 5000), (30, "1 oy", 10000)]

TASHKENT_OFFSET = timedelta(hours=5)

def _tashkent_now() -> datetime:
    return datetime.utcnow() + TASHKENT_OFFSET

def _tashkent_today_str() -> str:
    return _tashkent_now().strftime("%Y-%m-%d")

def get_vip_discount_price(days: int):
    val = get_setting(f"vip_discount_{days}")
    return int(val) if val is not None else None

def get_vip_card_info():
    number = get_setting("vip_card_number", "5614 6865 0291 5765")
    holder = get_setting("vip_card_holder", "Vohobov D.")
    return number, holder

def resolve_secret_message_id(code) -> int:
    code_str = str(int(code))
    meta = _movie_meta_cache.get(code_str)
    if meta and "secret_message_id" in meta:
        return meta["secret_message_id"]
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT secret_message_id FROM main_channel_posts WHERE code = ?", (int(code),))
        row = cursor.fetchone()
    result = int(row[0]) if row and row[0] else int(code)
    _movie_meta_cache.setdefault(code_str, {})["secret_message_id"] = result
    return result

# =====================================================================
# FSM STATES
# =====================================================================
class SuperAdminState(StatesGroup):
    waiting_for_assistant_id = State()
    waiting_for_short_video = State()
    waiting_for_full_video = State()
    waiting_for_short_type = State()
    waiting_for_short_genre = State()
    waiting_for_short_vip_duration = State()
    waiting_for_short_code = State()
    waiting_for_daily_limit = State()
    waiting_for_channel_input = State()
    waiting_for_broadcast_schedule = State()
    waiting_for_status_import_file = State()

class UserState(StatesGroup):
    waiting_for_movie_code = State()
    waiting_for_vip_movie_request = State()
    waiting_for_comment_text = State()

class AdminState(StatesGroup):
    waiting_for_vip_code = State()
    waiting_for_broadcast = State()

class VipPurchaseState(StatesGroup):
    waiting_for_receipt_photo = State()

class GrantVipState(StatesGroup):
    waiting_for_user_id = State()
    waiting_for_duration = State()

class BozorAdminState(StatesGroup):
    waiting_for_card_number = State()
    waiting_for_card_holder = State()
    waiting_for_discount_price = State()

class VipGiftState(StatesGroup):
    waiting_for_gift_id = State()
    waiting_for_gift_days = State()

# =====================================================================
# DB INIT
# =====================================================================
def init_db():
    conn = sqlite3.connect(DB_PATH)
    conn.execute("PRAGMA journal_mode=WAL;")
    conn.execute("PRAGMA busy_timeout=10000;")
    cursor = conn.cursor()

    cursor.execute("""CREATE TABLE IF NOT EXISTS users (
        user_id INTEGER PRIMARY KEY, full_name TEXT, username TEXT,
        role TEXT DEFAULT 'user', restricted_until REAL DEFAULT 0,
        vip_expires_at REAL DEFAULT 0, referrals_count INTEGER DEFAULT 0,
        free_vip_views INTEGER DEFAULT 0,
        joined_date TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        last_active TIMESTAMP DEFAULT CURRENT_TIMESTAMP)""")

    for col, default in [
        ('role', "'user'"), ('restricted_until', 0), ('renewal_reminder_sent', 0),
        ('last_search_at', 0), ('last_daily_reward_at', 0),
        ('daily_free_count', 0), ('daily_free_date', "''"),
        ('pending_watch_code', 'NULL')]:
        try:
            cursor.execute(f"ALTER TABLE users ADD COLUMN {col} DEFAULT {default}")
        except sqlite3.OperationalError:
            pass

    cursor.execute("""CREATE TABLE IF NOT EXISTS vip_gift_logs (
        id INTEGER PRIMARY KEY AUTOINCREMENT, from_id INTEGER, to_id INTEGER,
        days INTEGER, created_at REAL)""")
    # vip_sales_log va bot_errors endi faqat RAM'da saqlanadi (deque), bazaga yozilmaydi.
    cursor.execute("""CREATE TABLE IF NOT EXISTS bot_settings (key TEXT PRIMARY KEY, value TEXT)""")
    cursor.execute("""CREATE TABLE IF NOT EXISTS main_channel_posts (
        code INTEGER PRIMARY KEY, genre TEXT, year INTEGER, posted_at REAL,
        video_file_id TEXT, is_vip INTEGER DEFAULT 0, vip_until REAL DEFAULT 0,
        reposted_as_free INTEGER DEFAULT 0)""")
    for col, default in [('video_file_id', 'NULL'), ('is_vip', 0), ('vip_until', 0),
                         ('reposted_as_free', 0), ('secret_message_id', 'NULL')]:
        try:
            cursor.execute(f"ALTER TABLE main_channel_posts ADD COLUMN {col} DEFAULT {default}")
        except sqlite3.OperationalError:
            pass
    cursor.execute("""CREATE TABLE IF NOT EXISTS vip_purchase_requests (
        id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, duration_label TEXT,
        duration_days INTEGER, price INTEGER, receipt_file_id TEXT,
        status TEXT DEFAULT 'pending', created_at REAL, decided_at REAL)""")
    try:
        cursor.execute("ALTER TABLE vip_purchase_requests ADD COLUMN admin_msg_id INTEGER")
    except sqlite3.OperationalError:
        pass
    # referral_logs, promo_codes, used_promos tizimlari olib tashlandi.
    cursor.execute("""CREATE TABLE IF NOT EXISTS saved_movies (
        user_id INTEGER, movie_code TEXT,
        saved_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        PRIMARY KEY(user_id, movie_code))""")
    cursor.execute("""CREATE TABLE IF NOT EXISTS movie_stats (
        code TEXT PRIMARY KEY, likes INTEGER DEFAULT 0, dislikes INTEGER DEFAULT 0,
        views_count INTEGER DEFAULT 0)""")
    cursor.execute("""CREATE TABLE IF NOT EXISTS movie_votes (
        user_id INTEGER, code TEXT, vote_count INTEGER DEFAULT 0,
        PRIMARY KEY(user_id, code))""")
    cursor.execute("""CREATE TABLE IF NOT EXISTS vip_movies (
        code TEXT PRIMARY KEY, added_date TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        vip_until REAL DEFAULT NULL)""")
    try:
        cursor.execute("ALTER TABLE vip_movies ADD COLUMN vip_until REAL DEFAULT NULL")
    except sqlite3.OperationalError:
        pass
    cursor.execute("""CREATE TABLE IF NOT EXISTS movies_meta (
        code TEXT PRIMARY KEY, genre TEXT DEFAULT 'Barchasi', is_vip BOOLEAN DEFAULT 0)""")
    cursor.execute("""CREATE TABLE IF NOT EXISTS required_channels (
        id INTEGER PRIMARY KEY AUTOINCREMENT, channel_id TEXT,
        channel_username TEXT, channel_title TEXT, invite_link TEXT)""")
    try:
        cursor.execute("ALTER TABLE required_channels ADD COLUMN invite_link TEXT")
    except sqlite3.OperationalError:
        pass
    cursor.execute("""CREATE TABLE IF NOT EXISTS channel_join_requests (
        user_id INTEGER, channel_id TEXT, requested_at REAL,
        PRIMARY KEY(user_id, channel_id))""")
    # broadcast_log endi faqat RAM'da saqlanadi (dict, eng ko'pi 10 ta broadcast).
    cursor.execute("""CREATE TABLE IF NOT EXISTS vip_requests (
        id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, movie_name TEXT,
        status TEXT DEFAULT 'pending', created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP)""")
    cursor.execute("""CREATE TABLE IF NOT EXISTS movie_comments (
        id INTEGER PRIMARY KEY AUTOINCREMENT, code TEXT, user_id INTEGER,
        full_name TEXT, comment TEXT, created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP)""")

    cursor.execute(
        "INSERT OR IGNORE INTO users (user_id, full_name, username, role) VALUES (?, 'Super Admin', 'admin', 'super_admin')",
        (SUPER_ADMIN_ID,))
    cursor.execute("UPDATE users SET role = 'super_admin' WHERE user_id = ?", (SUPER_ADMIN_ID,))
    cursor.execute("INSERT OR IGNORE INTO bot_settings (key, value) VALUES ('vip_card_number', '5614 6865 0291 5765')")
    cursor.execute("INSERT OR IGNORE INTO bot_settings (key, value) VALUES ('vip_card_holder', 'Vohobov D.')")
    cursor.execute("INSERT OR IGNORE INTO bot_settings (key, value) VALUES ('daily_free_limit', '3')")
    cursor.execute("INSERT OR IGNORE INTO bot_settings (key, value) VALUES ('content_protection', '1')")
    cursor.execute("INSERT OR IGNORE INTO bot_settings (key, value) VALUES ('auto_restart_enabled', '1')")
    conn.commit()
    conn.close()

init_db()

# =====================================================================
# CORE FUNCTIONS
# =====================================================================
def update_last_active(user_id: int):
    with db_connect() as (conn, cursor):
        cursor.execute("UPDATE users SET last_active = CURRENT_TIMESTAMP WHERE user_id = ?", (user_id,))
        conn.commit()

def _load_role_cache(user_id: int):
    with db_connect() as (conn, cursor):
        cursor.execute(
            "SELECT role, vip_expires_at, restricted_until FROM users WHERE user_id = ?", (user_id,))
        row = cursor.fetchone()
    if not row:
        return None
    role, vip_exp, restricted_until = row
    entry = {"role": role, "vip_expires_at": vip_exp or 0, "restricted_until": restricted_until or 0}
    _role_cache[user_id] = entry
    return entry

def _invalidate_role_cache(user_id: int):
    _role_cache.pop(user_id, None)

def get_user_role(user_id: int) -> str:
    entry = _role_cache.get(user_id) or _load_role_cache(user_id)
    if entry is None:
        return 'user'
    if entry["role"] == 'vip' and entry["vip_expires_at"] and entry["vip_expires_at"] < time.time():
        with db_connect() as (conn, cursor):
            cursor.execute("UPDATE users SET role = 'user', vip_expires_at = 0 WHERE user_id = ?", (user_id,))
            conn.commit()
        entry["role"] = 'user'
        entry["vip_expires_at"] = 0
        _role_cache[user_id] = entry
        return 'user'
    return entry["role"]

def is_user_restricted(user_id: int) -> bool:
    entry = _role_cache.get(user_id) or _load_role_cache(user_id)
    if entry is None:
        return False
    return bool(entry["restricted_until"] and entry["restricted_until"] > time.time())

def is_vip_movie(code: str) -> bool:
    meta = _movie_meta_cache.get(code)
    if meta and "is_vip" in meta:
        return meta["is_vip"]
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT 1 FROM vip_movies WHERE code = ?", (code,))
        res = cursor.fetchone()
    result = res is not None
    _movie_meta_cache.setdefault(code, {})["is_vip"] = result
    return result

def get_movie_stats(code: str):
    if code in _movie_stats_cache:
        return _movie_stats_cache[code]
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT likes, dislikes, views_count FROM movie_stats WHERE code = ?", (code,))
        res = cursor.fetchone()
        if not res:
            cursor.execute(
                "INSERT OR IGNORE INTO movie_stats (code, likes, dislikes, views_count) VALUES (?, 0, 0, 0)",
                (code,))
            conn.commit()
            res = (0, 0, 0)
    _movie_stats_cache[code] = res
    return res

def register_movie_view(code: str):
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT 1 FROM movie_stats WHERE code = ?", (code,))
        if cursor.fetchone():
            cursor.execute("UPDATE movie_stats SET views_count = views_count + 1 WHERE code = ?", (code,))
        else:
            cursor.execute(
                "INSERT INTO movie_stats (code, likes, dislikes, views_count) VALUES (?, 0, 0, 1)",
                (code,))
        cursor.execute("SELECT likes, dislikes, views_count FROM movie_stats WHERE code = ?", (code,))
        res = cursor.fetchone()
        conn.commit()
    _movie_stats_cache[code] = res

def mark_movie_search(user_id: int):
    with db_connect() as (conn, cursor):
        cursor.execute("UPDATE users SET last_search_at = ? WHERE user_id = ?", (time.time(), user_id))
        conn.commit()

# ---- Saqlangan kinolar keshi ----
def _load_saved_set(user_id: int) -> set:
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT movie_code FROM saved_movies WHERE user_id = ?", (user_id,))
        codes = {r[0] for r in cursor.fetchall()}
    _saved_cache[user_id] = codes
    return codes

def is_movie_saved(user_id: int, code: str) -> bool:
    codes = _saved_cache.get(user_id)
    if codes is None:
        codes = _load_saved_set(user_id)
    return code in codes

def set_movie_saved(user_id: int, code: str, saved: bool):
    with db_connect() as (conn, cursor):
        if saved:
            cursor.execute(
                "INSERT OR IGNORE INTO saved_movies (user_id, movie_code) VALUES (?, ?)", (user_id, code))
        else:
            cursor.execute(
                "DELETE FROM saved_movies WHERE user_id = ? AND movie_code = ?", (user_id, code))
        conn.commit()
    codes = _saved_cache.get(user_id)
    if codes is None:
        codes = _load_saved_set(user_id)
    elif saved:
        codes.add(code)
    else:
        codes.discard(code)

def grant_vip_to_user(user_id: int, days: int, cursor=None, source: str = "manual"):
    now = time.time()

    def _apply(cur):
        cur.execute("SELECT role, vip_expires_at FROM users WHERE user_id = ?", (user_id,))
        row = cur.fetchone()
        cur_role, cur_expiry = row if row else ('user', 0)
        base_time = cur_expiry if (cur_role == 'vip' and cur_expiry and cur_expiry > now) else now
        new_expiry = base_time + (days * 86400)
        cur.execute(
            "UPDATE users SET role = 'vip', vip_expires_at = ?, renewal_reminder_sent = 0 WHERE user_id = ?",
            (new_expiry, user_id))
        return new_expiry

    if cursor is not None:
        new_expiry = _apply(cursor)
    else:
        with db_connect() as (conn, cursor2):
            new_expiry = _apply(cursor2)
            conn.commit()

    entry = _role_cache.get(user_id, {"restricted_until": 0})
    entry["role"] = "vip"
    entry["vip_expires_at"] = new_expiry
    entry.setdefault("restricted_until", 0)
    _role_cache[user_id] = entry

    _vip_sales_log.append({"user_id": user_id, "days": days, "granted_at": now, "source": source})
    return new_expiry

def revoke_vip_grant(user_id: int, days: int):
    now = time.time()
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT role, vip_expires_at FROM users WHERE user_id = ?", (user_id,))
        row = cursor.fetchone()
        if not row:
            return
        cur_role, cur_expiry = row
        if cur_role != 'vip' or not cur_expiry:
            return
        new_expiry = cur_expiry - (days * 86400)
        if new_expiry <= now:
            cursor.execute("UPDATE users SET role = 'user', vip_expires_at = 0 WHERE user_id = ?", (user_id,))
        else:
            cursor.execute("UPDATE users SET vip_expires_at = ? WHERE user_id = ?", (new_expiry, user_id))
        conn.commit()
    _invalidate_role_cache(user_id)

# =====================================================================
# KUNDALIK BEPUL LIMIT — can_watch_now
# =====================================================================
def _get_daily_free_count_from_db(user_id: int) -> int:
    with db_connect() as (conn, cursor):
        cursor.execute(
            "SELECT daily_free_date, daily_free_count FROM users WHERE user_id = ?", (user_id,))
        row = cursor.fetchone()
    if row and row[0] == _tashkent_today_str():
        return row[1] or 0
    return 0

def _write_through_daily_free(user_id: int, count: int):
    with db_connect() as (conn, cursor):
        cursor.execute(
            "UPDATE users SET daily_free_date = ?, daily_free_count = ?, last_search_at = ? WHERE user_id = ?",
            (_tashkent_today_str(), count, time.time(), user_id))
        conn.commit()

def can_watch_now(user_id: int, role: str):
    """Markaziy ruxsat funksiyasi. Qaytaradi: (ruxsat_bor, sabab)."""
    if role in ('vip', 'assistant', 'super_admin'):
        return True, None
    today = _tashkent_today_str()
    entry = _daily_free_cache.get(user_id)
    if not entry or entry.get("date") != today:
        entry = {"date": today, "count": _get_daily_free_count_from_db(user_id)}
        _daily_free_cache[user_id] = entry
    limit = get_setting('daily_free_limit', '3')
    try:
        limit = int(limit)
    except (TypeError, ValueError):
        limit = 3
    if entry["count"] < limit:
        return True, "free"
    return False, None

def register_daily_free_usage(user_id: int):
    today = _tashkent_today_str()
    entry = _daily_free_cache.get(user_id)
    if not entry or entry.get("date") != today:
        entry = {"date": today, "count": 0}
    entry["count"] += 1
    _daily_free_cache[user_id] = entry
    _write_through_daily_free(user_id, entry["count"])

# =====================================================================
# BACKGROUND LOOPS
# =====================================================================
async def vip_purchase_loop():
    while True:
        try:
            now = time.time()
            with db_connect() as (conn, cursor):
                cursor.execute(
                    "SELECT id, user_id, duration_days, duration_label, admin_msg_id FROM vip_purchase_requests "
                    "WHERE status = 'pending' AND (? - created_at) >= 300",
                    (now,))
                rows = cursor.fetchall()

            processed = []
            for req_id, user_id, duration_days, duration_label, admin_msg_id in rows:
                try:
                    with db_connect() as (conn2, cursor2):
                        # Atomik shart: faqat hali ham 'pending' bo'lsa yutamiz — shu orqali
                        # admin aynan shu daqiqada qo'lda tasdiqlasa/rad etsa, ikkala tomon
                        # bir vaqtda VIP bermasligi (yoki ikki marta bermasligi) kafolatlanadi.
                        cursor2.execute(
                            "UPDATE vip_purchase_requests SET status = 'auto_approved', decided_at = ? "
                            "WHERE id = ? AND status = 'pending'",
                            (now, req_id))
                        won = cursor2.rowcount == 1
                        if won:
                            grant_vip_to_user(user_id, duration_days, cursor=cursor2, source="auto")
                        conn2.commit()
                    if won:
                        processed.append((req_id, user_id, duration_days, duration_label, admin_msg_id))
                except Exception as e:
                    logger.error(f"vip_purchase_loop: #{req_id} xato: {e}")

            for req_id, user_id, duration_days, duration_label, admin_msg_id in processed:
                try:
                    await bot.send_message(
                        user_id,
                        f"🎉 To'lovingiz tasdiqlandi! Sizga <b>{duration_label}</b> VIP obuna berildi.",
                        parse_mode="HTML")
                except Exception:
                    pass
                await deliver_pending_watch_if_any(user_id)
                if admin_msg_id:
                    try:
                        await bot.edit_message_reply_markup(
                            chat_id=SUPER_ADMIN_ID, message_id=admin_msg_id, reply_markup=None)
                    except Exception:
                        pass
                try:
                    cancel_kb = InlineKeyboardMarkup(inline_keyboard=[[
                        InlineKeyboardButton(text="🚫 VIPni bekor qilish",
                                             callback_data=f"cancel_autovip_{req_id}")
                    ]])
                    await bot.send_message(
                        SUPER_ADMIN_ID,
                        f"⏱ #{req_id} VIP so'rovi <b>5 daqiqa</b> ichida javobsiz qoldi — avtomatik tasdiqlandi "
                        f"(foydalanuvchi: <code>{user_id}</code>, muddat: {duration_label}).\n\n"
                        f"Agar bu xato bo'lsa, quyidagi tugma orqali bekor qilishingiz mumkin:",
                        reply_markup=cancel_kb, parse_mode="HTML")
                except Exception:
                    pass
        except Exception as e:
            logger.error(f"vip_purchase_loop xatosi: {e}")
        await asyncio.sleep(30)

def generate_status_export() -> dict:
    now = time.time()
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT user_id, role, vip_expires_at FROM users WHERE role IN ('super_admin', 'assistant', 'vip')")
        rows = cursor.fetchall()

    statuses = []
    for u_id, role, vip_exp in rows:
        vip_remaining_hours = None
        if role == 'vip' and vip_exp:
            remaining = vip_exp - now
            vip_remaining_hours = round(remaining / 3600, 2) if remaining > 0 else 0
        statuses.append({"user_id": u_id, "role": role, "vip_remaining_hours": vip_remaining_hours})

    data = {
        "generated_at": datetime.now().isoformat(),
        "super_admin_id": SUPER_ADMIN_ID,
        "statuses": statuses
    }
    try:
        with open(STATUS_EXPORT_PATH, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except Exception as e:
        logger.error(f"Status export faylini yozishda xatolik: {e}")
    return data

async def status_export_loop():
    while True:
        try:
            generate_status_export()
            logger.info("Status hisoboti avtomatik yangilandi (24 soatlik tsikl).")
        except Exception as e:
            logger.error(f"status_export_loop xatosi: {e}")
        await asyncio.sleep(86400)

async def db_backup_loop():
    while True:
        await asyncio.sleep(86400)
        backup_path = DB_PATH + ".backup_tmp"
        try:
            with db_connect() as (conn, cursor):
                cursor.execute("PRAGMA wal_checkpoint(FULL);")
            src = sqlite3.connect(DB_PATH)
            try:
                dst = sqlite3.connect(backup_path)
                try:
                    src.backup(dst)
                finally:
                    dst.close()
            finally:
                src.close()
            await bot.send_document(
                SUPER_ADMIN_ID,
                InputFile(backup_path, filename="database.db"),
                caption=f"🗄 Avtomatik zaxira nusxa ({datetime.now().strftime('%Y-%m-%d %H:%M')}).\n"
                        f"Kerak bo'lsa, Super Admin menyusi → 'Ma'lumotlarni tiklash' orqali qayta yuklang.")
        except Exception as e:
            logger.error(f"db_backup_loop xatosi: {e}")
        finally:
            try:
                if os.path.exists(backup_path):
                    os.remove(backup_path)
            except Exception:
                pass

async def check_vip_expirations():
    while True:
        try:
            now = time.time()
            expired_users = []
            ids = []
            with db_connect() as (conn, cursor):
                cursor.execute(
                    "SELECT user_id FROM users WHERE role = 'vip' AND vip_expires_at > 0 AND vip_expires_at <= ?",
                    (now,))
                expired_users = cursor.fetchall()

                if expired_users:
                    cursor.execute(
                        "UPDATE users SET role = 'user', vip_expires_at = 0 "
                        "WHERE role = 'vip' AND vip_expires_at > 0 AND vip_expires_at <= ?",
                        (now,))
                    conn.commit()

                reminder_window_end = now + 86400
                cursor.execute(
                    "SELECT user_id FROM users WHERE role = 'vip' AND vip_expires_at > ? AND vip_expires_at <= ? "
                    "AND (renewal_reminder_sent IS NULL OR renewal_reminder_sent = 0)",
                    (now, reminder_window_end))
                soon_expiring = cursor.fetchall()
                if soon_expiring:
                    ids = [u[0] for u in soon_expiring]
                    cursor.executemany(
                        "UPDATE users SET renewal_reminder_sent = 1 WHERE user_id = ?",
                        [(i,) for i in ids])
                    conn.commit()

            for (u_id,) in expired_users:
                _invalidate_role_cache(u_id)
                try:
                    await bot.send_message(
                        u_id,
                        "⚠️ Sizning VIP obunangiz vaqti tugadi. Avtomatik ravishda oddiy foydalanuvchi maqomiga o'tkazildingiz.",
                        parse_mode="HTML")
                except Exception:
                    pass

            for u_id in ids:
                try:
                    renew_kb = InlineKeyboardMarkup(inline_keyboard=[
                        [InlineKeyboardButton(text="🔄 Uzaytirish (Bozor)", callback_data="vip_shop")]
                    ])
                    await bot.send_message(
                        u_id,
                        "⏰ <b>Eslatma!</b>\n\nSizning VIP obunangiz muddati <b>24 soatdan kamroq</b> vaqt ichida tugaydi.\n"
                        "Imtiyozlaringizni yo'qotmaslik uchun hoziroq uzaytiring:",
                        reply_markup=renew_kb, parse_mode="HTML")
                except Exception:
                    pass
        except Exception as e:
            logger.error(f"Error in check_vip_expirations: {e}")
        await asyncio.sleep(10)

async def error_digest_loop():
    while True:
        await asyncio.sleep(86400)
        try:
            if _bot_errors_log:
                entries = list(_bot_errors_log)
                lines = [f"🐞 <b>So'nggi 24 soatlik xatoliklar hisoboti</b> (jami {len(entries)} ta):\n"]
                for entry in entries[-30:]:
                    t = datetime.fromtimestamp(entry["occurred_at"]).strftime('%d.%m %H:%M')
                    lines.append(f"[{t}] {entry['text']}")
                text = "\n".join(lines)
                for chunk_start in range(0, len(text), 3500):
                    await bot.send_message(
                        SUPER_ADMIN_ID, text[chunk_start:chunk_start + 3500], parse_mode="HTML")
                _bot_errors_log.clear()
        except Exception as e:
            logger.error(f"error_digest_loop xatosi: {e}")

async def daily_likes_boost_loop():
    """Har kuni Toshkent vaqti bilan 00:00da barcha kinolarga +10 like qo'shadi."""
    while True:
        now = _tashkent_now()
        tomorrow_midnight = (now + timedelta(days=1)).replace(hour=0, minute=0, second=0, microsecond=0)
        seconds_left = (tomorrow_midnight - now).total_seconds()
        await asyncio.sleep(max(1, seconds_left))
        try:
            with db_connect() as (conn, cursor):
                cursor.execute("UPDATE movie_stats SET likes = likes + 10")
                conn.commit()
                cursor.execute("SELECT code, likes, dislikes, views_count FROM movie_stats")
                rows = cursor.fetchall()
            for code, likes, dislikes, views in rows:
                if code in _movie_stats_cache:
                    _movie_stats_cache[code] = (likes, dislikes, views)
            logger.info("Kunlik +10 like barcha kinolarga muvaffaqiyatli qo'shildi.")
        except Exception as e:
            logger.error(f"daily_likes_boost_loop xatosi: {e}")

# =====================================================================
# KEYBOARDS & UI
# =====================================================================
def is_vip_or_admin(role: str) -> bool:
    return role in ('vip', 'assistant', 'super_admin')

# ---- "Oxirgi panel ustuvorligi" — panel_token (14-band) ----
def _tok(base: str, token: str) -> str:
    return f"{base}@{token}"

def _detok(data: str):
    if "@" in data:
        base, token = data.rsplit("@", 1)
        return base, token
    return data, None

async def _new_panel_token(state: FSMContext) -> str:
    token = secrets.token_hex(4)
    await state.update_data(panel_token=token)
    return token

async def _verify_panel_token(callback: CallbackQuery, state: FSMContext):
    """Shu panelga tegishli inline tugma bosilganda chaqiriladi. Mos kelmasa eskirgan xabar beradi."""
    base, token = _detok(callback.data)
    data = await state.get_data()
    current = data.get('panel_token')
    if not current or token != current:
        await callback.answer("⚠️ Bu bo'lim eskirgan, asosiy menyudan qaytadan boshlang", show_alert=True)
        return False, base
    return True, base

def get_main_keyboard(role: str):
    row2_middle = KeyboardButton(text="📤 Yuklash") if role in ['super_admin', 'assistant'] else KeyboardButton(text="🛒 Bozor")
    keyboard = [
        [KeyboardButton(text="🎬 Kino Qidirish"), KeyboardButton(text="💾 Saqlanganlar")],
        [KeyboardButton(text="📊 Profilim"), row2_middle, KeyboardButton(text="🆕 2026 Premyeralari")],
        [KeyboardButton(text="🎲 Mix Kino Xizmati"), KeyboardButton(text="🔥 Top Kinolar")],
    ]
    if role == 'vip':
        keyboard.append([KeyboardButton(text="🎁 VIP Sovg'a")])
    elif role in ['super_admin', 'assistant']:
        keyboard.append([KeyboardButton(text="👑 Super Admin & Yordamchi Menyusi")])
    return ReplyKeyboardMarkup(keyboard=keyboard, resize_keyboard=True)

def generate_movie_keyboard(code: str, likes: int, dislikes: int, is_saved_by_user: bool = False,
                            is_vip_viewer: bool = False, bot_username: str = None):
    save_text = "✅ Saqlangan" if is_saved_by_user else "💾 Saqlash"
    rows = [[
        InlineKeyboardButton(text="💬 Izohlar", callback_data=f"comments_{code}"),
        InlineKeyboardButton(text=save_text, callback_data=f"save_{code}")
    ]]
    if bot_username:
        share_url = f"https://t.me/share/url?url=https://t.me/{bot_username}?start=watch_{code}&text=Shu kinoni ko'r!"
        rows.append([InlineKeyboardButton(text="📤 Do'stlarga ulashish", url=share_url)])
    if not is_vip_viewer:
        rows.append([InlineKeyboardButton(
            text="⚡ Reklamasiz va kutishsiz tomosha qilish", callback_data="vip_shop")])
    return InlineKeyboardMarkup(inline_keyboard=rows)

def get_vip_upgrade_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="⭐ VIP bo'lish (Bozor)", callback_data="vip_shop")]
    ])

def build_vip_shop_keyboard(token: str) -> InlineKeyboardMarkup:
    rows = []
    for days, label, price in VIP_FIXED_PRICES:
        discount = get_vip_discount_price(days)
        if discount is not None:
            text = f"🏷 Chegirma: {discount:,} so'm — {label} (avvalgi narx: {price:,} so'm)"
            callback_data = _tok(f"buyvip_discount_{days}", token)
        else:
            text = f"{label} — {price:,} so'm"
            callback_data = _tok(f"buyvip_fixed_{days}", token)
        rows.append([InlineKeyboardButton(text=text, callback_data=callback_data)])
    return InlineKeyboardMarkup(inline_keyboard=rows)

def build_super_admin_keyboard(role: str, token: str) -> InlineKeyboardMarkup:
    daily_limit = get_setting('daily_free_limit', '3')
    protection_on = get_setting('content_protection', '1') == '1'
    protection_label = ("🔒 Uzatishni cheklash: Yoqilgan" if protection_on
                        else "🔓 Uzatishni cheklash: O'chirilgan")
    buttons = [
        [InlineKeyboardButton(text="👥 Yordamchilarni boshqarish (Max 3 ta)",
                              callback_data=_tok("sa_manage_assistants", token))],
        [InlineKeyboardButton(text="📢 Ommaviy xabar yuborish", callback_data=_tok("admin_broadcast", token))],
        [InlineKeyboardButton(text="📋 Bot holati (Server)", callback_data=_tok("sa_bot_health", token))],
        [InlineKeyboardButton(text="📊 Status hisoboti (Export/Import)",
                              callback_data=_tok("sa_status_report", token))],
        [InlineKeyboardButton(text="🐞 Xatoliklar hisoboti", callback_data=_tok("sa_error_report", token))],
        [InlineKeyboardButton(text=f"📊 Kunlik bepul limit: {daily_limit}",
                              callback_data=_tok("sa_daily_limit", token))],
        [InlineKeyboardButton(text=protection_label, callback_data=_tok("sa_toggle_protection", token))],
        [InlineKeyboardButton(text="🧹 Keshni tozalash", callback_data=_tok("sa_clear_cache", token))],
    ]
    if role == 'super_admin':
        autorestart_on = get_setting('auto_restart_enabled', '1') == '1'
        autorestart_label = ("🔁 Avto qayta ishga tushirish: Yoqilgan (3 marta)" if autorestart_on
                             else "⏸ Avto qayta ishga tushirish: O'chirilgan")
        buttons.append([InlineKeyboardButton(text=autorestart_label,
                                             callback_data=_tok("sa_toggle_autorestart", token))])
        buttons.append([InlineKeyboardButton(text="👤 ID orqali VIP berish", callback_data=_tok("sa_grant_vip", token))])
        buttons.append([InlineKeyboardButton(text="🛒 Bozorni boshqarish", callback_data=_tok("sa_market_menu", token))])
    return InlineKeyboardMarkup(inline_keyboard=buttons)

async def send_vip_paywall(chat_id: int, message: Message = None):
    price_lines = []
    for days, label, price in VIP_FIXED_PRICES:
        discount = get_vip_discount_price(days)
        if discount is not None:
            price_lines.append(f"🏷 {label}: <s>{price:,}</s> <b>{discount:,} so'm</b>")
        else:
            price_lines.append(f"• {label}: <b>{price:,} so'm</b>")
    text = (
        "🔒 Ushbu bot VIP a'zolik asosida ishlaydi.\n\n"
        "Barcha kinolar va imkoniyatlardan cheklovsiz, kutishsiz foydalanish uchun VIP bo'ling:\n\n"
        + "\n".join(price_lines))
    kb = get_vip_upgrade_keyboard()
    if message is not None:
        await message.answer(text, reply_markup=kb, parse_mode="HTML")
    else:
        try:
            await bot.send_message(chat_id, text, reply_markup=kb, parse_mode="HTML")
        except Exception:
            pass

async def send_vip_shop(chat_id: int, message: Message, state: FSMContext):
    token = await _new_panel_token(state)
    text = (
        "🛒 <b>Bozor — VIP obuna sotib olish</b>\n\n"
        "VIP a'zolik sizga: reklamasiz, kutishsiz va cheklovsiz barcha kinolarni tomosha qilish imkonini beradi.\n\n"
        "Muddatni tanlang:")
    kb = build_vip_shop_keyboard(token)
    if message is not None:
        sent = await message.answer(text, reply_markup=kb, parse_mode="HTML")
        _register_section_message(chat_id, sent)
    else:
        try:
            sent = await bot.send_message(chat_id, text, reply_markup=kb, parse_mode="HTML")
            _register_section_message(chat_id, sent)
        except Exception:
            pass

async def send_super_admin_panel(target, role: str, as_callback: bool, state: FSMContext):
    token = await _new_panel_token(state)
    text = f"👑 <b>Boshqaruv Paneli</b>\nDarajangiz: <b>{role.upper()}</b>"
    kb = build_super_admin_keyboard(role, token)
    if as_callback:
        user_id = target.from_user.id
        sent = await target.message.answer(text, reply_markup=kb, parse_mode="HTML")
    else:
        user_id = target.from_user.id if hasattr(target, "from_user") else None
        sent = await target.answer(text, reply_markup=kb, parse_mode="HTML")
    if user_id:
        _register_section_message(user_id, sent)

# =====================================================================
# PENDING WATCH & MOVIE DELIVERY
# =====================================================================
async def deliver_pending_watch_if_any(user_id: int):
    code = pop_pending_watch_code(user_id)
    if code:
        try:
            await deliver_movie_by_code(user_id, code)
        except Exception as e:
            logger.error(f"deliver_pending_watch_if_any xatosi: {e}")

def set_pending_watch_code(user_id: int, code: str):
    with db_connect() as (conn, cursor):
        cursor.execute("UPDATE users SET pending_watch_code = ? WHERE user_id = ?", (code, user_id))
        conn.commit()

def pop_pending_watch_code(user_id: int):
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT pending_watch_code FROM users WHERE user_id = ?", (user_id,))
        row = cursor.fetchone()
        code = row[0] if row else None
        if code:
            cursor.execute("UPDATE users SET pending_watch_code = NULL WHERE user_id = ?", (user_id,))
            conn.commit()
    return code

async def deliver_movie(chat_id: int, code: str, role: str, is_saved: bool, likes: int,
                        dislikes: int, extra_rows: list = None, skip_wait: bool = False) -> bool:
    is_vip_viewer = role in ['vip', 'assistant', 'super_admin']
    bot_username = await get_bot_username()
    keyboard = generate_movie_keyboard(code, likes, dislikes, is_saved,
                                       is_vip_viewer=is_vip_viewer, bot_username=bot_username)
    if extra_rows:
        keyboard = InlineKeyboardMarkup(
            inline_keyboard=keyboard.inline_keyboard + extra_rows)
    try:
        await bot.copy_message(
            chat_id=chat_id, from_chat_id=CHANNEL_ID,
            message_id=resolve_secret_message_id(code),
            reply_markup=keyboard, protect_content=(get_setting('content_protection', '1') == '1'))
        register_movie_view(code)
        return True
    except BadRequest:
        return False
    except Exception as e:
        logger.error(f"deliver_movie xatosi: {e}")
        return False

async def deliver_movie_by_code(user_id: int, code_text: str) -> bool:
    if not code_text.isdigit():
        return False
    code_int = int(code_text)
    role = get_user_role(user_id)
    likes, dislikes, views = get_movie_stats(str(code_int))
    with db_connect() as (conn, cursor):
        cursor.execute(
            "SELECT 1 FROM saved_movies WHERE user_id = ? AND movie_code = ?",
            (user_id, str(code_int)))
        is_saved = cursor.fetchone() is not None
    ok = await deliver_movie(user_id, str(code_int), role, is_saved, likes, dislikes)
    if not ok:
        try:
            await bot.send_message(user_id, f"❌ {code_int}-kodli kino topilmadi.")
        except Exception:
            pass
    return ok

# =====================================================================
# START & REFERRAL
# =====================================================================
@dp.message_handler(commands=['start'])
async def cmd_start(message: Message, state: FSMContext):
    if message.chat.type in ('group', 'supergroup'):
        bot_username = await get_bot_username()
        kb = InlineKeyboardMarkup(inline_keyboard=[[
            InlineKeyboardButton(text="🤖 Botni shaxsiy xabarda ochish",
                                 url=f"https://t.me/{bot_username}?start=1")
        ]])
        try:
            await message.reply(
                "👋 Salom! Kinolarni tomosha qilish, qidirish va boshqa imkoniyatlardan foydalanish uchun "
                "botni <b>shaxsiy xabarlar</b>da oching 👇",
                reply_markup=kb, parse_mode="HTML")
        except Exception as e:
            logger.error(f"cmd_start (guruh) xatosi: {e}")
        return
    await state.finish()
    user_id = message.from_user.id
    if is_user_restricted(user_id):
        await message.answer("⚠️ Sizga vaqtinchalik cheklov qo'yilgan. Bot funksiyalaridan foydalana olmaysiz.")
        return
    update_last_active(user_id)
    args = message.text.split()
    exists = None

    with db_connect() as (conn, cursor):
        cursor.execute("SELECT user_id FROM users WHERE user_id = ?", (user_id,))
        exists = cursor.fetchone()
        if not exists:
            cursor.execute(
                "INSERT INTO users (user_id, full_name, username, role) VALUES (?, ?, ?, 'user')",
                (user_id, message.from_user.full_name, message.from_user.username))
            conn.commit()
            try:
                uname_text = f"@{message.from_user.username}" if message.from_user.username else "mavjud emas"
                await bot.send_message(
                    SUPER_ADMIN_ID,
                    f"👤 <b>Yangi foydalanuvchi botga qo'shildi!</b>\n\n"
                    f"Ismi: <a href='tg://user?id={user_id}'>{message.from_user.full_name}</a>\n"
                    f"ID: <code>{user_id}</code>\nUsername: {uname_text}",
                    parse_mode="HTML")
            except Exception:
                pass

    role = get_user_role(user_id)
    payload = args[1] if len(args) > 1 else None
    if payload and payload.startswith("watch_"):
        watch_code = payload[len("watch_"):]
        if watch_code.isdigit():
            allowed, reason = can_watch_now(user_id, role)
            if not allowed:
                set_pending_watch_code(user_id, watch_code)
                if not exists:
                    await message.answer(
                        f"Assalomu alaykum, <b>{message.from_user.first_name}</b>! 🎬\n"
                        f"Kinolar botiga xush kelibsiz.",
                        reply_markup=get_main_keyboard(role), parse_mode="HTML")
                await send_vip_shop(message.chat.id, message=message, state=state)
                return
            if not exists:
                await message.answer(
                    f"Assalomu alaykum, <b>{message.from_user.first_name}</b>! 🎬\n"
                    f"Kinolar botiga xush kelibsiz.",
                    reply_markup=get_main_keyboard(role), parse_mode="HTML")
            ok = await deliver_movie_by_code(user_id, watch_code)
            if ok and reason == "free":
                register_daily_free_usage(user_id)
            return

    if is_vip_or_admin(role):
        text = (f"Assalomu alaykum, <b>{message.from_user.first_name}</b>!\n"
                f"Kinolar botiga xush kelibsiz. Quyidagi menyudan foydalaning:")
        await message.answer(text, reply_markup=get_main_keyboard(role), parse_mode="HTML")
        return

    if not exists:
        await message.answer(
            f"Assalomu alaykum, <b>{message.from_user.first_name}</b>! 🎬\n"
            f"Kinolar botiga xush kelibsiz.",
            reply_markup=get_main_keyboard(role), parse_mode="HTML")
    await send_vip_shop(message.chat.id, message=message, state=state)

# =====================================================================
# MENU HANDLERS
# =====================================================================
@dp.message_handler(Text(equals="🎬 Kino Qidirish"))
async def msg_search_btn(message: Message, state: FSMContext):
    user_id = message.from_user.id
    await _close_previous_section(user_id)
    await state.finish()
    if is_user_restricted(user_id):
        return
    update_last_active(user_id)
    role = get_user_role(user_id)
    await message.answer("🎬 Kino kodini yuboring (Masalan: 15):",
                        reply_markup=get_main_keyboard(role))
    await UserState.waiting_for_movie_code.set()

@dp.message_handler(Text(equals="📊 Profilim"))
async def msg_status_btn(message: Message, state: FSMContext):
    user_id = message.from_user.id
    await _close_previous_section(user_id)
    await state.finish()
    if is_user_restricted(user_id):
        return
    update_last_active(user_id)
    role = get_user_role(user_id)
    with db_connect() as (conn, cursor):
        cursor.execute(
            "SELECT joined_date, vip_expires_at FROM users WHERE user_id = ?",
            (user_id,))
        res = cursor.fetchone()
    joined_date, vip_expires = res
    role_names = {'user': '👤 Oddiy foydalanuvchi', 'vip': '👑 VIP a\'zo',
                  'assistant': '🛠 Yordamchi Admin', 'super_admin': '👑 Super Admin'}
    daraja_line = role_names.get(role, 'Noma`lum')
    vip_time = ""
    if role == 'vip' and vip_expires:
        left = int(vip_expires - time.time())
        if left > 0:
            days_left = left // 86400
            daraja_line = f"👑 VIP a'zo | Amal qiladi: {days_left} kun"
            vip_time = (f"\n⏳ Aniq qolgan vaqt: {days_left} kun, "
                        f"{(left % 86400) // 3600} soat, {(left % 3600) // 60} daqiqa")
    profile_kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="⭐ Bozor (VIP sotib olish)", callback_data="vip_shop")]])
    sent = await message.answer(
        f"📊 <b>Profil Ma'lumotlari:</b>\n\n"
        f"🆔 ID: <code>{user_id}</code>\n"
        f"👑 Daraja: {daraja_line}{vip_time}\n"
        f"📅 Ro'yxatdan o'tgan: {joined_date}",
        reply_markup=profile_kb, parse_mode="HTML")
    _register_section_message(user_id, sent)

@dp.message_handler(Text(equals="💾 Saqlanganlar"))
async def msg_saved_btn(message: Message, state: FSMContext):
    user_id = message.from_user.id
    await _close_previous_section(user_id)
    await state.finish()
    if is_user_restricted(user_id):
        return
    update_last_active(user_id)
    role = get_user_role(user_id)
    if not is_vip_or_admin(role):
        await send_vip_paywall(message.chat.id, message=message)
        return
    with db_connect() as (conn, cursor):
        cursor.execute(
            "SELECT movie_code FROM saved_movies WHERE user_id = ? ORDER BY saved_at DESC LIMIT 50",
            (user_id,))
        rows = cursor.fetchall()
    if not rows:
        await message.answer("Sizda saqlangan kinolar yo'q.")
        return
    buttons = [[InlineKeyboardButton(text=f"🎬 {code}-kino", callback_data=f"watch_{code}")]
               for (code,) in rows]
    sent = await message.answer("💾 Saqlangan kinolar:",
                                reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons))
    _register_section_message(user_id, sent)

def _build_top_movie_codes() -> list:
    """Avval eng ko'p ko'rilgan (so'ralgan) kinolar, so'ng qolganlari eng oxirgi
    yuklangandan boshlab teskari tartibda (67-66-65...), takrorlanishsiz."""
    with db_connect() as (conn, cursor):
        cursor.execute(
            "SELECT code FROM movie_stats WHERE views_count > 0 ORDER BY views_count DESC, code DESC")
        top_rows = [str(r[0]) for r in cursor.fetchall()]
        cursor.execute("SELECT code FROM main_channel_posts ORDER BY posted_at DESC")
        latest_rows = [str(r[0]) for r in cursor.fetchall()]
    latest_set = set(latest_rows)
    top_valid = [c for c in top_rows if c in latest_set]
    seen = set(top_valid)
    rest = [c for c in latest_rows if c not in seen]
    return (top_valid + rest)[:300]

@dp.message_handler(Text(equals="🔥 Top Kinolar"))
async def msg_top_movies_btn(message: Message, state: FSMContext):
    user_id = message.from_user.id
    await _close_previous_section(user_id)
    await state.finish()
    if is_user_restricted(user_id):
        return
    update_last_active(user_id)
    role = get_user_role(user_id)
    allowed, reason = can_watch_now(user_id, role)
    if not allowed:
        await send_vip_paywall(message.chat.id, message=message)
        return
    codes = _build_top_movie_codes()
    if not codes:
        await message.answer("🔥 Hozircha kinolar mavjud emas.")
        return
    await state.update_data(top_codes=codes)
    await _send_sequential_movie(message.chat.id, user_id, role, reason, 0, codes,
                                 "topnext_", message=message)

# =====================================================================
# MIX MOVIE
# =====================================================================
async def send_mix_movie(chat_id: int, callback: CallbackQuery = None):
    role = get_user_role(chat_id)
    allowed, reason = can_watch_now(chat_id, role)
    if not allowed:
        if callback:
            await callback.answer()
            await send_vip_paywall(chat_id, message=callback.message)
        else:
            await send_vip_paywall(chat_id)
        return
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT code FROM movie_stats")
        all_movies = [row[0] for row in cursor.fetchall()]
    if not all_movies:
        text = "Bazada yetarli kinolar mavjud emas."
        if callback:
            await callback.answer(text, show_alert=True)
        else:
            await bot.send_message(chat_id, text)
        return
    random.shuffle(all_movies)
    success = False
    for random_code in all_movies[:10]:
        likes, dislikes, views = get_movie_stats(str(random_code))
        is_saved = is_movie_saved(chat_id, str(random_code))
        if callback:
            try:
                await callback.message.delete()
            except Exception:
                pass
        success = await deliver_movie(chat_id, str(random_code), role,
                                       is_saved, likes, dislikes, skip_wait=True)
        if success:
            break
    if success and reason == "free":
        register_daily_free_usage(chat_id)
    if not success:
        err_msg = "Tasodifiy kino qidirilmoqda, ammo kanalda mavjud aktiv post topilmadi."
        if callback:
            await callback.answer(err_msg, show_alert=True)
        else:
            await bot.send_message(chat_id, err_msg)
    elif callback:
        await callback.answer()

@dp.message_handler(Text(equals="🎲 Mix Kino Xizmati"))
async def msg_mix_movie(message: Message, state: FSMContext):
    user_id = message.from_user.id
    await _close_previous_section(user_id)
    await state.finish()
    if is_user_restricted(user_id):
        return
    update_last_active(user_id)
    await send_mix_movie(message.chat.id)

# =====================================================================
# KETMA-KET KINO YUBORISH (Top Kinolar uchun umumiy yordamchi)
# =====================================================================
async def _send_sequential_movie(target_chat_id: int, user_id: int, role: str, reason: str,
                                 index: int, codes: list, callback_prefix: str,
                                 message: Message = None, callback: CallbackQuery = None):
    code = codes[index]
    likes, dislikes, views = get_movie_stats(code)
    is_saved = is_movie_saved(user_id, code)
    has_next = index + 1 < len(codes)
    extra = []
    if has_next:
        extra = [[InlineKeyboardButton(text="➡️ Keyingisi",
                                       callback_data=f"{callback_prefix}{index + 1}")]]
    ok = await deliver_movie(target_chat_id, code, role, is_saved, likes, dislikes, extra_rows=extra)
    if ok and reason == "free":
        register_daily_free_usage(user_id)
    if not ok:
        if callback:
            await callback.answer("Kino topilmadi.", show_alert=True)
        elif message:
            await message.answer("❌ Kino topilmadi.")
    elif not has_next:
        try:
            if callback:
                await callback.message.answer("📭 Ro'yxat tugadi.")
            elif message:
                await message.answer("📭 Ro'yxat tugadi.")
        except Exception:
            pass
    return ok

@dp.callback_query_handler(lambda c: c.data and c.data.startswith("topnext_"))
async def cb_top_next(callback: CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    role = get_user_role(user_id)
    allowed, reason = can_watch_now(user_id, role)
    if not allowed:
        await callback.answer()
        await send_vip_paywall(user_id, message=callback.message)
        return
    data = await state.get_data()
    codes = data.get('top_codes')
    if not codes:
        await callback.answer("Sessiya eskirgan, qaytadan boshlang.", show_alert=True)
        return
    index = int(callback.data.split("_", 1)[1])
    if index >= len(codes):
        await callback.answer("Ro'yxat tugadi.", show_alert=True)
        return
    await callback.answer()
    await _send_sequential_movie(user_id, user_id, role, reason, index, codes,
                                 "topnext_", callback=callback)

# =====================================================================
# 2026 PREMYERALARI — oxirgi 15 ta kino, shaffof panelda (3x5 panjara)
# =====================================================================
@dp.message_handler(Text(equals="🆕 2026 Premyeralari"))
async def msg_latest_movies_btn(message: Message, state: FSMContext):
    user_id = message.from_user.id
    await _close_previous_section(user_id)
    await state.finish()
    if is_user_restricted(user_id):
        return
    update_last_active(user_id)
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT code FROM main_channel_posts ORDER BY posted_at DESC LIMIT 15")
        codes = [str(r[0]) for r in cursor.fetchall()]
    if not codes:
        await message.answer("🆕 Hozircha kinolar mavjud emas.")
        return
    rows = []
    row = []
    for code in codes:
        row.append(InlineKeyboardButton(text=f"🎬 {code}", callback_data=f"watch_{code}"))
        if len(row) == 3:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    sent = await message.answer(
        "🆕 <b>2026 Premyeralari</b>\n\nEng so'nggi qo'shilgan kinolar — kerakligini tanlang 👇",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=rows), parse_mode="HTML")
    _register_section_message(user_id, sent)

# =====================================================================
# VIP GIFT
# =====================================================================
@dp.message_handler(Text(equals="🎁 VIP Sovg'a"))
async def msg_vip_gift_start(message: Message, state: FSMContext):
    user_id = message.from_user.id
    await _close_previous_section(user_id)
    await state.finish()
    if is_user_restricted(user_id):
        return
    update_last_active(user_id)
    role = get_user_role(user_id)
    if role != 'vip':
        await message.answer("Bu funksiya faqat VIP foydalanuvchilar uchun.")
        return
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT vip_expires_at FROM users WHERE user_id = ?", (user_id,))
        res = cursor.fetchone()
    remaining_days = 0
    if res and res[0]:
        remaining_days = int((res[0] - time.time()) // 86400)
    if remaining_days < 2:
        await message.answer(
            f"⚠️ Sovg'a qilish uchun sizda kamida 2 kunlik VIP bo'lishi kerak "
            f"(o'zingizda kamida 1 kun qolishi shart). Sizda: {remaining_days} kun qoldi.")
        return
    await state.update_data(max_gift_days=remaining_days - 1)
    await message.answer(
        f"🎁 <b>VIP Sovg'a</b>\n\nSizda <b>{remaining_days} kun</b> VIP qoldi, shundan "
        f"<b>{remaining_days - 1} kunigacha</b> boshqa foydalanuvchiga sovg'a qilishingiz mumkin "
        f"(o'zingizda kamida 1 kun qolishi shart).\n\n"
        f"Sovg'a qilmoqchi bo'lgan foydalanuvchining ID raqamini yuboring:",
        parse_mode="HTML")
    await VipGiftState.waiting_for_gift_id.set()

@dp.message_handler(state=VipGiftState.waiting_for_gift_id)
async def process_vip_gift_id(message: Message, state: FSMContext):
    if not message.text.strip().isdigit():
        await message.answer("❌ Faqat raqamli ID kiriting.")
        return
    target_id = int(message.text.strip())
    if target_id == message.from_user.id:
        await message.answer("❌ O'zingizga sovg'a qila olmaysiz.")
        return
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT 1 FROM users WHERE user_id = ?", (target_id,))
        exists = cursor.fetchone()
    if not exists:
        await message.answer("❌ Bunday ID li foydalanuvchi topilmadi.")
        return
    data = await state.get_data()
    await state.update_data(gift_target_id=target_id)
    await message.answer(f"Nechta kun sovg'a qilmoqchisiz? (Maksimal: {data.get('max_gift_days')} kun)")
    await VipGiftState.waiting_for_gift_days.set()

@dp.message_handler(state=VipGiftState.waiting_for_gift_days)
async def process_vip_gift_days(message: Message, state: FSMContext):
    if not message.text.strip().isdigit():
        await message.answer("❌ Faqat raqam kiriting.")
        return
    days = int(message.text.strip())
    data = await state.get_data()
    max_days = data.get('max_gift_days', 0)
    target_id = data.get('gift_target_id')
    user_id = message.from_user.id
    if not target_id:
        await message.answer("❌ Sessiya eskirgan, qaytadan '🎁 VIP Sovg'a' tugmasini bosing.",
                             reply_markup=get_main_keyboard(get_user_role(user_id)))
        await state.finish()
        return
    if days < 1 or days > max_days:
        await message.answer(f"❌ 1 dan {max_days} gachagina kun sovg'a qilishingiz mumkin.")
        return
    # Sovg'a bosqichlari orasida yuboruvchining VIP holati tugab qolgan bo'lishi mumkin —
    # amalga oshirishdan oldin qayta tekshiramiz, xato / noto'g'ri hisob-kitobning oldini olish uchun.
    sender_role = get_user_role(user_id)
    if sender_role != 'vip':
        await message.answer("❌ VIP obunangiz tugagan, shuning uchun sovg'a qilib bo'lmaydi.",
                             reply_markup=get_main_keyboard(sender_role))
        await state.finish()
        return
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT vip_expires_at FROM users WHERE user_id = ?", (user_id,))
        sender_row = cursor.fetchone()
        my_exp = (sender_row[0] if sender_row else 0) or time.time()
        remaining_now = int((my_exp - time.time()) // 86400)
        if days > remaining_now - 1:
            await message.answer(
                f"❌ Hozirgi qolgan VIP vaqtingiz o'zgargan. Sovg'a qilish mumkin bo'lgan "
                f"maksimal: {max(0, remaining_now - 1)} kun.")
            await state.finish()
            return
        cursor.execute(
            "UPDATE users SET vip_expires_at = vip_expires_at - ? WHERE user_id = ?",
            (days * 86400, user_id))
        cursor.execute("SELECT role, vip_expires_at FROM users WHERE user_id = ?", (target_id,))
        target_row = cursor.fetchone()
        if not target_row:
            conn.rollback()
            await message.answer("❌ Qabul qiluvchi foydalanuvchi topilmadi, sovg'a bekor qilindi.",
                                 reply_markup=get_main_keyboard(sender_role))
            await state.finish()
            return
        t_role, t_exp = target_row
        base_time = t_exp if (t_role == 'vip' and t_exp and t_exp > time.time()) else time.time()
        new_expiry = base_time + (days * 86400)
        cursor.execute(
            "UPDATE users SET role = 'vip', vip_expires_at = ?, renewal_reminder_sent = 0 WHERE user_id = ?",
            (new_expiry, target_id))
        cursor.execute(
            "INSERT INTO vip_gift_logs (from_id, to_id, days, created_at) VALUES (?, ?, ?, ?)",
            (user_id, target_id, days, time.time()))
        conn.commit()
    _invalidate_role_cache(user_id)
    _invalidate_role_cache(target_id)
    role = get_user_role(user_id)
    await message.answer(f"✅ {days} kunlik VIP muvaffaqiyatli sovg'a qilindi!",
                         reply_markup=get_main_keyboard(role))
    try:
        await bot.send_message(
            target_id,
            f"🎁 Sizga <a href='tg://user?id={user_id}'>bir foydalanuvchi</a> tomonidan "
            f"<b>{days} kunlik VIP</b> sovg'a qilindi!", parse_mode="HTML")
    except Exception:
        pass
    await deliver_pending_watch_if_any(target_id)
    await state.finish()

# =====================================================================
# SUPER ADMIN PANEL
# =====================================================================
@dp.callback_query_handler(lambda c: c.data == "sa_menu")
async def cb_sa_menu(callback: CallbackQuery, state: FSMContext):
    await _close_previous_section(callback.from_user.id)
    await state.finish()
    role = get_user_role(callback.from_user.id)
    if role not in ['super_admin', 'assistant']:
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    await callback.answer()
    await send_super_admin_panel(callback, role, as_callback=True, state=state)

@dp.message_handler(Text(equals="👑 Super Admin & Yordamchi Menyusi"))
async def msg_super_admin_menu(message: Message, state: FSMContext):
    await _close_previous_section(message.from_user.id)
    await state.finish()
    role = get_user_role(message.from_user.id)
    if role not in ['super_admin', 'assistant']:
        return
    await send_super_admin_panel(message, role, as_callback=False, state=state)

@dp.callback_query_handler(lambda c: _detok(c.data)[0] == "sa_bot_health")
async def cb_bot_health(callback: CallbackQuery, state: FSMContext):
    valid, base = await _verify_panel_token(callback, state)
    if not valid:
        return
    if get_user_role(callback.from_user.id) not in ['super_admin', 'assistant']:
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    uptime_sec = int(time.time() - BOT_START_TIME)
    days = uptime_sec // 86400
    hours = (uptime_sec % 86400) // 3600
    minutes = (uptime_sec % 3600) // 60
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT COUNT(*) FROM users")
        total_users = cursor.fetchone()[0]
        cursor.execute("SELECT COUNT(*) FROM users WHERE role = 'vip'")
        total_vip = cursor.fetchone()[0]
    await callback.message.answer(
        f"📋 <b>Bot Holati</b>\n\n"
        f"🟢 Holat: <b>Ishlamoqda</b>\n"
        f"⏱ Ishga tushganiga: <b>{days} kun {hours} soat {minutes} daqiqa</b>\n"
        f"⚠️ Ushbu ishga tushishdan beri xatoliklar soni: <b>{ERROR_COUNT}</b>\n\n"
        f"👥 Jami foydalanuvchilar: <b>{total_users}</b> ta\n"
        f"👑 Faol VIP'lar: <b>{total_vip}</b> ta",
        parse_mode="HTML")
    await callback.answer()

# =====================================================================
# STATUS REPORT
# =====================================================================
@dp.callback_query_handler(lambda c: _detok(c.data)[0] == "sa_status_report")
async def cb_status_report_menu(callback: CallbackQuery, state: FSMContext):
    valid, base = await _verify_panel_token(callback, state)
    if not valid:
        return
    await state.finish()
    if get_user_role(callback.from_user.id) not in ['super_admin', 'assistant']:
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="⬇️ Yuklab olish", callback_data="status_download")],
        [InlineKeyboardButton(text="⬆️ Yuklab berish (Import)", callback_data="status_import")]
    ])
    await callback.message.answer(
        "📊 <b>Status hisoboti</b>\n\n"
        "Bu yerda barcha Super Admin, Yordamchi va VIP foydalanuvchilarning "
        "maqomi va qolgan VIP vaqti saqlanadi. Hisobot har 24 soatda avtomatik yangilanadi.",
        reply_markup=kb, parse_mode="HTML")
    await callback.answer()

@dp.callback_query_handler(lambda c: c.data == "status_download")
async def cb_status_download(callback: CallbackQuery):
    if get_user_role(callback.from_user.id) not in ['super_admin', 'assistant']:
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    generate_status_export()
    try:
        await callback.message.answer_document(
            InputFile(STATUS_EXPORT_PATH, filename="status_export.json"),
            caption="📊 Joriy status hisoboti (Super Admin/Yordamchi/VIP ro'yxati).")
    except Exception as e:
        await callback.message.answer(f"❌ Faylni yuborishda xatolik: {e}")
    await callback.answer()

@dp.callback_query_handler(lambda c: c.data == "status_import")
async def cb_status_import_mode(callback: CallbackQuery):
    if get_user_role(callback.from_user.id) not in ['super_admin', 'assistant']:
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="➕ Qo'shish (mavjudga qo'shiladi)", callback_data="status_mode_merge")],
        [InlineKeyboardButton(text="🔁 Almashtirish (mavjudni o'chirib, yangisi yoziladi)",
                             callback_data="status_mode_replace")],
    ])
    await callback.message.answer("Faylni qanday rejimda yuklaymiz?", reply_markup=kb)
    await callback.answer()

@dp.callback_query_handler(lambda c: c.data and c.data.startswith("status_mode_"))
async def cb_status_import_mode_selected(callback: CallbackQuery, state: FSMContext):
    if get_user_role(callback.from_user.id) not in ['super_admin', 'assistant']:
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    mode = callback.data.split("_", 2)[2]
    await state.update_data(status_import_mode=mode)
    await callback.message.answer("📎 Endi status_export.json faylini (hujjat sifatida) yuboring:")
    await SuperAdminState.waiting_for_status_import_file.set()
    await callback.answer()

@dp.message_handler(state=SuperAdminState.waiting_for_status_import_file, content_types=['document'])
async def process_status_import_file(message: Message, state: FSMContext):
    data = await state.get_data()
    mode = data.get('status_import_mode', 'merge')
    try:
        tg_file = await bot.get_file(message.document.file_id)
        file_bytes = await bot.download_file(tg_file.file_path)
        parsed = json.loads(file_bytes.read().decode("utf-8"))
        statuses = parsed.get("statuses", [])
    except Exception as e:
        await message.answer(f"❌ Faylni o'qishda xatolik: {e}")
        return
    now = time.time()
    applied = 0
    with db_connect() as (conn, cursor):
        if mode == 'replace':
            cursor.execute(
                "UPDATE users SET role = 'user', vip_expires_at = 0 "
                "WHERE role IN ('vip', 'assistant') AND user_id != ?", (SUPER_ADMIN_ID,))
            conn.commit()
        for entry in statuses:
            u_id = entry.get("user_id")
            role = entry.get("role")
            vip_hours = entry.get("vip_remaining_hours")
            if not u_id or not role or u_id == SUPER_ADMIN_ID:
                continue
            vip_expires_at = now + (vip_hours * 3600) if (role == 'vip' and vip_hours) else 0
            cursor.execute("SELECT 1 FROM users WHERE user_id = ?", (u_id,))
            if not cursor.fetchone():
                cursor.execute(
                    "INSERT INTO users (user_id, full_name, username, role, vip_expires_at) "
                    "VALUES (?, ?, ?, ?, ?)",
                    (u_id, "Import orqali qo'shilgan", "", role, vip_expires_at))
            else:
                cursor.execute(
                    "UPDATE users SET role = ?, vip_expires_at = ?, renewal_reminder_sent = 0 "
                    "WHERE user_id = ?", (role, vip_expires_at, u_id))
            applied += 1
        conn.commit()
    _role_cache.clear()
    role = get_user_role(message.from_user.id)
    mode_text = "Almashtirish" if mode == 'replace' else "Qo'shish"
    await message.answer(
        f"✅ Status hisoboti import qilindi!\n\n"
        f"🔧 Rejim: <b>{mode_text}</b>\n"
        f"👥 Yangilangan/qo'shilgan yozuvlar: <b>{applied}</b> ta",
        reply_markup=get_main_keyboard(role), parse_mode="HTML")
    await state.finish()

# =====================================================================
# GENRE MANAGEMENT
# =====================================================================
# =====================================================================
# ASSISTANTS
# =====================================================================
@dp.callback_query_handler(lambda c: _detok(c.data)[0] == "sa_manage_assistants")
async def cb_manage_assistants(callback: CallbackQuery, state: FSMContext):
    valid, base = await _verify_panel_token(callback, state)
    if not valid:
        return
    await state.finish()
    if get_user_role(callback.from_user.id) != 'super_admin':
        await callback.answer("Bu funksiya faqat Super Admin uchun!", show_alert=True)
        return
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT user_id, full_name, username FROM users WHERE role = 'assistant'")
        assistants = cursor.fetchall()
    text = "👥 <b>Hozirgi Yordamchilar (Maksimal 3 ta):</b>\n\n"
    for u_id, name, uname in assistants:
        clean_name = name.replace("<", "&lt;").replace(">", "&gt;") if name else "Yordamchi"
        text += f"• <a href='tg://user?id={u_id}'>{clean_name}</a> (@{uname}, <code>{u_id}</code>)\n"
    if not assistants:
        text += "Hozircha yordamchilar tayinlanmagan.\n"
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="➕ Yordamchi qo'shish", callback_data="sa_add_assistant")],
        [InlineKeyboardButton(text="➖ Yordamchini o'chirish", callback_data="sa_remove_assistant")]
    ])
    await callback.message.answer(text, reply_markup=kb, parse_mode="HTML")
    await callback.answer()

@dp.callback_query_handler(lambda c: c.data == "sa_add_assistant")
async def cb_add_assistant(callback: CallbackQuery, state: FSMContext):
    await state.finish()
    if get_user_role(callback.from_user.id) != 'super_admin':
        return
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT COUNT(*) FROM users WHERE role = 'assistant'")
        count = cursor.fetchone()[0]
    if count >= 3:
        await callback.answer("Maksimal 3 ta yordamchi tayinlash mumkin!", show_alert=True)
        return
    await callback.message.answer("Yordamchi qilmoqchi bo'lgan foydalanuvchining ID raqamini kiriting:")
    await SuperAdminState.waiting_for_assistant_id.set()
    await state.update_data(action="add")
    await callback.answer()

@dp.callback_query_handler(lambda c: c.data == "sa_remove_assistant")
async def cb_remove_assistant(callback: CallbackQuery, state: FSMContext):
    await state.finish()
    if get_user_role(callback.from_user.id) != 'super_admin':
        return
    await callback.message.answer("Yordamchilik huquqini olib tashlamoqchi bo'lgan foydalanuvchining ID raqamini kiriting:")
    await SuperAdminState.waiting_for_assistant_id.set()
    await state.update_data(action="remove")
    await callback.answer()

@dp.message_handler(state=SuperAdminState.waiting_for_assistant_id)
async def process_assistant_id(message: Message, state: FSMContext):
    if not message.text.isdigit():
        await message.answer("Faqat raqamli ID kiriting!")
        return
    target_id = int(message.text)
    data = await state.get_data()
    action = data.get('action')
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT 1 FROM users WHERE user_id = ?", (target_id,))
        if not cursor.fetchone():
            await message.answer("Bunday foydalanuvchi topilmadi.")
            return
        if action == "add":
            cursor.execute("UPDATE users SET role = 'assistant' WHERE user_id = ?", (target_id,))
            conn.commit()
            await message.answer(
                f"✅ <a href='tg://user?id={target_id}'>{target_id}</a> ID raqamli foydalanuvchi yordamchi qilib tayinlandi!",
                parse_mode="HTML")
            try:
                await bot.send_message(
                    target_id,
                    "🎉 Tabriklaymiz! Sizga Super Admin tomonidan yordamchi huquqi berildi.",
                    parse_mode="HTML")
            except Exception:
                pass
        else:
            cursor.execute("UPDATE users SET role = 'user' WHERE user_id = ?", (target_id,))
            conn.commit()
            await message.answer(
                f"✅ <a href='tg://user?id={target_id}'>{target_id}</a> ID raqamli foydalanuvchidan yordamchi huquqi olib tashlandi.",
                parse_mode="HTML")
    _invalidate_role_cache(target_id)
    role = get_user_role(message.from_user.id)
    await message.answer("Bosh menyu:", reply_markup=get_main_keyboard(role))
    await state.finish()

# =====================================================================
# BROADCAST
# =====================================================================
@dp.callback_query_handler(lambda c: _detok(c.data)[0] == "admin_broadcast")
async def cb_admin_broadcast(callback: CallbackQuery, state: FSMContext):
    valid, base = await _verify_panel_token(callback, state)
    if not valid:
        return
    await state.finish()
    user_id = callback.from_user.id
    if get_user_role(user_id) not in ['super_admin', 'assistant']:
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="👥 Hammaga", callback_data="bcast_target_all")],
        [InlineKeyboardButton(text="👑 Faqat VIP'larga", callback_data="bcast_target_vip")],
        [InlineKeyboardButton(text="👤 Faqat Oddiy foydalanuvchilarga", callback_data="bcast_target_user")],
        [InlineKeyboardButton(text="🟢 Faqat Faollarga (so'nggi 7 kun)", callback_data="bcast_target_active")],
    ])
    await callback.message.answer("📢 Xabar kimlarga yuborilsin?", reply_markup=kb)
    await callback.answer()

@dp.callback_query_handler(lambda c: c.data and c.data.startswith("bcast_target_"))
async def cb_bcast_target(callback: CallbackQuery, state: FSMContext):
    if get_user_role(callback.from_user.id) not in ['super_admin', 'assistant']:
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    target = callback.data.split("_", 2)[2]
    await state.update_data(bcast_target=target)
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🚀 Hozir yuborish", callback_data="bcast_when_now")],
        [InlineKeyboardButton(text="⏱ Rejalashtirish", callback_data="bcast_when_later")],
    ])
    await callback.message.answer("Xabar qachon yuborilsin?", reply_markup=kb)
    await callback.answer()

@dp.callback_query_handler(lambda c: c.data == "bcast_when_now")
async def cb_bcast_when_now(callback: CallbackQuery, state: FSMContext):
    await state.update_data(bcast_delay_minutes=0)
    await callback.message.answer("📢 Yubormoqchi bo'lgan xabaringiz matnini kiriting:")
    await AdminState.waiting_for_broadcast.set()
    await callback.answer()

@dp.callback_query_handler(lambda c: c.data == "bcast_when_later")
async def cb_bcast_when_later(callback: CallbackQuery, state: FSMContext):
    await callback.message.answer("⏱ Necha daqiqadan keyin yuborilsin? Raqam kiriting (masalan: 60):")
    await SuperAdminState.waiting_for_broadcast_schedule.set()
    await callback.answer()

@dp.message_handler(state=SuperAdminState.waiting_for_broadcast_schedule)
async def process_bcast_schedule(message: Message, state: FSMContext):
    if not message.text.isdigit():
        await message.answer("Faqat raqam kiriting!")
        return
    await state.update_data(bcast_delay_minutes=int(message.text))
    await message.answer("📢 Yubormoqchi bo'lgan xabaringiz matnini kiriting:")
    await AdminState.waiting_for_broadcast.set()

def get_broadcast_target_users(target: str):
    with db_connect() as (conn, cursor):
        if target == 'vip':
            cursor.execute("SELECT user_id FROM users WHERE role = 'vip'")
        elif target == 'user':
            cursor.execute("SELECT user_id FROM users WHERE role = 'user'")
        elif target == 'active':
            cursor.execute("SELECT user_id FROM users WHERE last_active >= datetime('now', '-7 days')")
        else:
            cursor.execute("SELECT user_id FROM users")
        return [r[0] for r in cursor.fetchall()]

async def execute_broadcast(admin_chat_id: int, target: str, broadcast_msg: str):
    users = get_broadcast_target_users(target)
    broadcast_id = f"bc_{int(time.time())}_{random.randint(1000, 9999)}"
    success, blocked = 0, 0
    sent_log = []
    for u_id in users:
        try:
            sent = await bot.send_message(u_id, broadcast_msg, parse_mode="HTML")
            sent_log.append((u_id, sent.message_id))
            success += 1
            await asyncio.sleep(0.05)
        except BotBlocked:
            blocked += 1
        except Exception:
            pass
    if sent_log:
        _record_broadcast(broadcast_id, sent_log)
    target_names = {'all': 'Hammaga', 'vip': 'VIP\'larga', 'user': 'Oddiy foydalanuvchilarga', 'active': 'Faollarga'}
    report_kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🗑 Ushbu xabarni hammadan o'chirish",
                              callback_data=f"delbcast_{broadcast_id}")]])
    try:
        await bot.send_message(
            admin_chat_id,
            f"✅ <b>Ommaviy xabar yuborish yakunlandi!</b>\n\n"
            f"🎯 Auditoriya: {target_names.get(target, target)}\n"
            f"✔️ Muvaffaqiyatli yetib bordi: {success} ta\n"
            f"❌ Botni bloklaganlar: {blocked} ta",
            reply_markup=report_kb, parse_mode="HTML")
    except Exception:
        pass

@dp.message_handler(state=AdminState.waiting_for_broadcast)
async def process_admin_broadcast(message: Message, state: FSMContext):
    broadcast_msg = message.text
    data = await state.get_data()
    target = data.get('bcast_target', 'all')
    delay_minutes = data.get('bcast_delay_minutes', 0)
    admin_chat_id = message.chat.id
    role = get_user_role(message.from_user.id)
    if delay_minutes and delay_minutes > 0:
        await message.answer(
            f"⏱ Xabar <b>{delay_minutes} daqiqadan</b> so'ng yuborilishi rejalashtirildi.",
            reply_markup=get_main_keyboard(role), parse_mode="HTML")

        async def scheduled_task():
            await asyncio.sleep(delay_minutes * 60)
            await execute_broadcast(admin_chat_id, target, broadcast_msg)

        asyncio.ensure_future(scheduled_task())
    else:
        status_msg = await message.answer("📢 Ommaviy xabar yuborish boshlandi...")
        await execute_broadcast(admin_chat_id, target, broadcast_msg)
        try:
            await status_msg.delete()
        except Exception:
            pass
        await message.answer("Bosh menyu:", reply_markup=get_main_keyboard(role))
    await state.finish()

@dp.callback_query_handler(lambda c: c.data and c.data.startswith("delbcast_"))
async def cb_delete_broadcast(callback: CallbackQuery):
    if get_user_role(callback.from_user.id) not in ['super_admin', 'assistant']:
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    broadcast_id = callback.data.split("delbcast_", 1)[1]
    entries = _broadcast_log.get(broadcast_id, [])
    deleted = 0
    for u_id, msg_id in entries:
        try:
            await bot.delete_message(chat_id=u_id, message_id=msg_id)
            deleted += 1
        except Exception:
            pass
    _broadcast_log.pop(broadcast_id, None)
    try:
        _broadcast_log_order.remove(broadcast_id)
    except ValueError:
        pass
    try:
        await callback.message.edit_text(
            callback.message.text + f"\n\n🗑 <b>O'chirildi:</b> {deleted}/{len(entries)} ta foydalanuvchidan",
            parse_mode="HTML")
    except Exception:
        pass
    await callback.answer("Xabar o'chirildi.")

# =====================================================================
# GRANT VIP
# =====================================================================
@dp.callback_query_handler(lambda c: _detok(c.data)[0] == "sa_grant_vip")
async def cb_sa_grant_vip(callback: CallbackQuery, state: FSMContext):
    valid, base = await _verify_panel_token(callback, state)
    if not valid:
        return
    await state.finish()
    if get_user_role(callback.from_user.id) != 'super_admin':
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    await callback.message.answer("👤 VIP bermoqchi bo'lgan foydalanuvchining ID raqamini kiriting:")
    await GrantVipState.waiting_for_user_id.set()
    await callback.answer()

@dp.message_handler(state=GrantVipState.waiting_for_user_id)
async def process_grant_vip_user_id(message: Message, state: FSMContext):
    text = message.text.strip() if message.text else ""
    if not text.isdigit():
        # ID kiritilmasa (bo'sh yoki noto'g'ri) — qaytadan so'ramasdan, bekor qilib
        # bosh menyuga qaytariladi.
        role = get_user_role(message.from_user.id)
        await message.answer(
            "❌ ID kiritilmadi, VIP berish bekor qilindi.",
            reply_markup=get_main_keyboard(role))
        await state.finish()
        return
    await state.update_data(grant_vip_user_id=int(text))
    await message.answer("Necha kunlik VIP berilsin? (Masalan: 7):")
    await GrantVipState.waiting_for_duration.set()

@dp.message_handler(state=GrantVipState.waiting_for_duration)
async def process_grant_vip_duration(message: Message, state: FSMContext):
    if not message.text or not message.text.strip().isdigit():
        role = get_user_role(message.from_user.id)
        await message.answer(
            "❌ Kun soni kiritilmadi, VIP berish bekor qilindi.",
            reply_markup=get_main_keyboard(role))
        await state.finish()
        return
    days = int(message.text.strip())
    data = await state.get_data()
    target_id = data.get("grant_vip_user_id")
    new_expiry = grant_vip_to_user(target_id, days)
    role = get_user_role(message.from_user.id)
    await message.answer(
        f"✅ <a href='tg://user?id={target_id}'>{target_id}</a> ga <b>{days} kunlik VIP</b> berildi!\n"
        f"Amal qilish muddati: {datetime.fromtimestamp(new_expiry).strftime('%d.%m.%Y %H:%M')} gacha "
        f"(real vaqtda hisoblanadi, tugagach avtomatik uziladi).",
        reply_markup=get_main_keyboard(role), parse_mode="HTML")
    try:
        await bot.send_message(
            target_id,
            f"🎉 Tabriklaymiz! Sizga <b>{days} kunlik VIP status</b> berildi!",
            parse_mode="HTML")
    except Exception:
        pass
    await deliver_pending_watch_if_any(target_id)
    await state.finish()

# =====================================================================
# KUNLIK BEPUL LIMIT SOZLASH (7-band)
# =====================================================================
@dp.callback_query_handler(lambda c: _detok(c.data)[0] == "sa_daily_limit")
async def cb_sa_daily_limit(callback: CallbackQuery, state: FSMContext):
    valid, base = await _verify_panel_token(callback, state)
    if not valid:
        return
    if get_user_role(callback.from_user.id) not in ['super_admin', 'assistant']:
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    await callback.answer()
    current = get_setting('daily_free_limit', '3')
    await callback.message.answer(
        f"📊 Joriy kunlik bepul limit: <b>{current}</b> ta.\nYangi qiymatni kiriting (masalan: 3):",
        parse_mode="HTML")
    await SuperAdminState.waiting_for_daily_limit.set()

@dp.message_handler(state=SuperAdminState.waiting_for_daily_limit)
async def process_daily_limit(message: Message, state: FSMContext):
    if not message.text.strip().isdigit():
        await message.answer("❌ Faqat raqam kiriting!")
        return
    value = int(message.text.strip())
    set_setting('daily_free_limit', value)
    role = get_user_role(message.from_user.id)
    await message.answer(f"✅ Kunlik bepul limit <b>{value}</b> ta qilib belgilandi!",
                         reply_markup=get_main_keyboard(role), parse_mode="HTML")
    await state.finish()

# =====================================================================
# UZATISHNI CHEKLASH (content protection) TOGGLE (15-band)
# =====================================================================
@dp.callback_query_handler(lambda c: _detok(c.data)[0] == "sa_toggle_protection")
async def cb_toggle_protection(callback: CallbackQuery, state: FSMContext):
    valid, base = await _verify_panel_token(callback, state)
    if not valid:
        return
    if get_user_role(callback.from_user.id) not in ['super_admin', 'assistant']:
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    current = get_setting('content_protection', '1')
    set_setting('content_protection', '0' if current == '1' else '1')
    role = get_user_role(callback.from_user.id)
    new_token = await _new_panel_token(state)
    try:
        await callback.message.edit_reply_markup(
            reply_markup=build_super_admin_keyboard(role, new_token))
    except Exception:
        pass
    await callback.answer("✅ Holat yangilandi.")

@dp.callback_query_handler(lambda c: _detok(c.data)[0] == "sa_toggle_autorestart")
async def cb_toggle_autorestart(callback: CallbackQuery, state: FSMContext):
    valid, base = await _verify_panel_token(callback, state)
    if not valid:
        return
    if get_user_role(callback.from_user.id) != 'super_admin':
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    current = get_setting('auto_restart_enabled', '1')
    set_setting('auto_restart_enabled', '0' if current == '1' else '1')
    role = get_user_role(callback.from_user.id)
    new_token = await _new_panel_token(state)
    try:
        await callback.message.edit_reply_markup(
            reply_markup=build_super_admin_keyboard(role, new_token))
    except Exception:
        pass
    await callback.answer("✅ Holat yangilandi.")

# =====================================================================
# KESHNI TOZALASH (9-band)
# =====================================================================
@dp.callback_query_handler(lambda c: _detok(c.data)[0] == "sa_clear_cache")
async def cb_clear_cache(callback: CallbackQuery, state: FSMContext):
    valid, base = await _verify_panel_token(callback, state)
    if not valid:
        return
    if get_user_role(callback.from_user.id) != 'super_admin':
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    global _cache_clear_in_progress
    if _cache_clear_in_progress:
        await callback.answer("🧹 Tozalash allaqachon davom etmoqda, biroz kuting...", show_alert=True)
        return
    _cache_clear_in_progress = True
    try:
        await callback.answer()
        status_msg = await callback.message.answer("🧹 Tozalanmoqda... 5")
        for i in range(4, -1, -1):
            await asyncio.sleep(1)
            try:
                await status_msg.edit_text(f"🧹 Tozalanmoqda... {i}")
            except Exception:
                pass
        _clear_all_caches()

        battery_info = "Noma'lum (termux-api kerak)"
        try:
            loop = asyncio.get_event_loop()
            result = await loop.run_in_executor(
                None,
                lambda: subprocess.run(["termux-battery-status"], capture_output=True, text=True, timeout=5)
            )
            if result.returncode == 0:
                bat = json.loads(result.stdout)
                battery_info = f"{bat.get('percentage', '?')}% | {bat.get('temperature', '?')}°C | {bat.get('status', '?')}"
        except Exception:
            pass

        ram_info = "Noma'lum"
        try:
            meminfo = {}
            with open('/proc/meminfo', 'r') as f:
                for line in f:
                    key, _, value = line.partition(':')
                    meminfo[key.strip()] = value.strip()
            total_kb = int(meminfo.get('MemTotal', '0 kB').split()[0])
            avail_kb = int(meminfo.get('MemAvailable', '0 kB').split()[0])
            ram_info = f"{avail_kb / 1024 / 1024:.2f} GB bo'sh / {total_kb / 1024 / 1024:.2f} GB jami"
        except Exception:
            pass

        final_text = (
            f"✅ Kesh muvaffaqiyatli tozalandi!\n\n"
            f"🔋 Batareya: {battery_info}\n"
            f"💾 RAM: {ram_info}")
        try:
            await status_msg.edit_text(final_text)
        except Exception:
            await callback.message.answer(final_text)
    finally:
        _cache_clear_in_progress = False

# =====================================================================
# COMMENTS
# =====================================================================
@dp.callback_query_handler(lambda c: c.data and c.data.startswith("comments_"))
async def cb_show_comments(callback: CallbackQuery):
    code = callback.data.split("_")[1]
    with db_connect() as (conn, cursor):
        cursor.execute(
            "SELECT user_id, full_name, comment, created_at FROM movie_comments "
            "WHERE code = ? ORDER BY id DESC LIMIT 10", (code,))
        rows = cursor.fetchall()
    text = f"💬 <b>{code}-kodli kino uchun izohlar:</b>\n\n"
    if not rows:
        text += "Hozircha izohlar yo'q. Birinchi bo'lib izoh qoldiring!"
    else:
        for u_id, name, com, date in rows:
            clean_name = name.replace("<", "&lt;").replace(">", "&gt;") if name else "Foydalanuvchi"
            text += f"👤 <a href='tg://user?id={u_id}'>{clean_name}</a>: {com}\n<i>({date})</i>\n\n"
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✍️ Izoh yozish", callback_data=f"writecom_{code}")],
        [InlineKeyboardButton(text="🔙 Kinoga qaytish", callback_data=f"watch_{code}")]
    ])
    try:
        await callback.message.edit_text(text, reply_markup=kb, parse_mode="HTML")
    except Exception:
        await callback.message.answer(text, reply_markup=kb, parse_mode="HTML")
    await callback.answer()

@dp.callback_query_handler(lambda c: c.data and c.data.startswith("writecom_"))
async def cb_write_comment_prompt(callback: CallbackQuery, state: FSMContext):
    await state.finish()
    code = callback.data.split("_")[1]
    await state.update_data(comment_code=code)
    await callback.message.answer("✍️ Ushbu kino haqida o'z fikringiz va izohingizni yuboring:")
    await UserState.waiting_for_comment_text.set()
    await callback.answer()

@dp.message_handler(state=UserState.waiting_for_comment_text)
async def process_user_comment(message: Message, state: FSMContext):
    data = await state.get_data()
    code = data.get('comment_code')
    if not code:
        await state.finish()
        return
    comment_text = message.text.strip()
    user_id = message.from_user.id
    full_name = message.from_user.full_name
    with db_connect() as (conn, cursor):
        cursor.execute(
            "INSERT INTO movie_comments (code, user_id, full_name, comment) VALUES (?, ?, ?, ?)",
            (code, user_id, full_name, comment_text))
        conn.commit()
    await state.finish()
    role = get_user_role(user_id)
    await message.answer("✅ Izohingiz muvaffaqiyatli qo'shildi!",
                         reply_markup=get_main_keyboard(role))

# =====================================================================
# ADMIN GROUP CODE — aniq kod aniqlash tizimi
# =====================================================================
# Matndagi raqamli tokenlarni topadi: "234", "45-kino", "234, 456 va 789" va h.k.
# Juda uzun raqamlar (telefon, ID, sana kabi) kodga aralashmasligi uchun uzunlik
# chegaralanadi — bitta kod odatda 1-6 xonali bo'ladi.
_CODE_TOKEN_PATTERN = re.compile(r'\d{1,6}')

def extract_candidate_codes(text: str) -> list:
    """Xabar matnidan mumkin bo'lgan kod-nomzodlarni (unikal, tartib bo'yicha) ajratib oladi."""
    if not text:
        return []
    found = []
    for token in _CODE_TOKEN_PATTERN.findall(text):
        num = int(token)
        if num > 0 and num not in found:
            found.append(num)
    return found[:20]

@dp.message_handler(lambda m: m.chat.id == ADMIN_GROUP_ID and m.text, content_types=['text'])
async def process_admin_group_code(message: Message):
    candidates = extract_candidate_codes(message.text)
    if not candidates:
        return
    # Faqat bazada haqiqatan mavjud bo'lgan kodlargina "kod" deb hisoblanadi —
    # shu orqali sana, ID yoki boshqa tasodifiy raqamlar chalkashtirilmaydi.
    matched = [c for c in candidates if is_code_already_posted(c)]
    if not matched:
        return
    bot_username = await get_bot_username()
    try:
        if len(matched) == 1:
            code_int = matched[0]
            watch_url = f"https://t.me/{bot_username}?start=watch_{code_int}"
            await message.reply(
                f"🎬 Kino KODI: <b>{code_int}</b>\n\nKinoni ko'rish uchun pastdagi tugmani bosing 👇",
                parse_mode="HTML",
                reply_markup=InlineKeyboardMarkup(
                    inline_keyboard=[[InlineKeyboardButton(text="🔒 Vip Tomosha", url=watch_url)]]))
        else:
            rows = [[InlineKeyboardButton(
                text=f"🔒 {code_int}-kino",
                url=f"https://t.me/{bot_username}?start=watch_{code_int}")] for code_int in matched]
            await message.reply(
                f"🎬 Xabarda <b>{len(matched)} ta</b> kino kodi topildi. Kerakli kinoni tanlang 👇",
                parse_mode="HTML",
                reply_markup=InlineKeyboardMarkup(inline_keyboard=rows))
    except Exception as e:
        logger.error(f"process_admin_group_code xatosi: {e}")

# =====================================================================
# MOVIE SEARCH
# =====================================================================
@dp.message_handler(state=UserState.waiting_for_movie_code)
async def process_movie_code_fsm(message: Message, state: FSMContext):
    await handle_movie_search(message.text.strip(), message, state)

@dp.message_handler(lambda m: m.chat.type == 'private' and m.text and m.text.isdigit(), state=None)
async def process_direct_number(message: Message, state: FSMContext):
    await state.finish()
    if is_user_restricted(message.from_user.id):
        return
    await handle_movie_search(message.text.strip(), message, state)

async def handle_movie_search(code_text: str, message: Message, state: FSMContext = None):
    user_id = message.from_user.id
    update_last_active(user_id)
    role = get_user_role(user_id)
    allowed, reason = can_watch_now(user_id, role)
    if not allowed:
        if state:
            await state.finish()
        await send_vip_paywall(message.chat.id, message=message)
        return
    mark_movie_search(user_id)
    if not code_text.isdigit():
        await message.answer("❌ Noto'g'ri format! Faqat raqamli kino kodini kiriting.")
        if state:
            await state.finish()
        return
    code_int = int(code_text)
    likes, dislikes, views = get_movie_stats(str(code_int))
    is_saved = is_movie_saved(user_id, str(code_int))
    ok = await deliver_movie(user_id, str(code_int), role, is_saved, likes, dislikes)
    if ok:
        if reason == "free":
            register_daily_free_usage(user_id)
        if state:
            await state.finish()
        return
    found_code = None
    for direction_codes in (
        [code_int + i for i in range(1, 6)],
        [code_int - i for i in range(1, 6) if code_int - i > 0],
    ):
        for candidate in direction_codes:
            candidate_str = str(candidate)
            c_likes, c_dislikes, c_views = get_movie_stats(candidate_str)
            c_is_saved = is_movie_saved(user_id, candidate_str)
            if await deliver_movie(user_id, candidate_str, role, c_is_saved,
                                    c_likes, c_dislikes, skip_wait=True):
                found_code = candidate
                break
        if found_code:
            break
    if state:
        await state.finish()
    if found_code:
        if reason == "free":
            register_daily_free_usage(user_id)
        try:
            await bot.send_message(
                user_id,
                f"ℹ️ {code_int}-kod topilmadi, shunga yaqin <b>{found_code}</b>-kodli kino topildi va yuborildi.",
                parse_mode="HTML")
        except Exception:
            pass
    else:
        await message.answer(f"❌ {code_int}-kodli kino topilmadi yoki maxfiy kanalda bunday post mavjud emas.")

@dp.callback_query_handler(lambda c: c.data and c.data.startswith("watch_"))
async def cb_watch(callback: CallbackQuery, state: FSMContext):
    await state.finish()
    user_id = callback.from_user.id
    role = get_user_role(user_id)
    allowed, reason = can_watch_now(user_id, role)
    if not allowed:
        await callback.answer()
        await send_vip_paywall(user_id, message=callback.message)
        return
    code = callback.data.split("_")[1]
    likes, dislikes, views = get_movie_stats(code)
    is_saved = is_movie_saved(user_id, code)
    if callback.message.chat.id != MAIN_CHANNEL_ID and callback.message.chat.id != CHANNEL_ID:
        try:
            await callback.message.delete()
        except Exception:
            pass
    ok = await deliver_movie(user_id, code, role, is_saved, likes, dislikes)
    if ok and reason == "free":
        register_daily_free_usage(user_id)
    if not ok:
        await callback.answer("Kino topilmadi.", show_alert=True)
    await callback.answer()

@dp.callback_query_handler(lambda c: c.data and c.data.startswith("save_"))
async def cb_save_movie(callback: CallbackQuery):
    user_id = callback.from_user.id
    code = callback.data.split("_")[1]
    if not is_vip_or_admin(get_user_role(user_id)):
        await callback.answer("Bu funksiya faqat VIP a'zolar uchun!", show_alert=True)
        return
    new_state = not is_movie_saved(user_id, code)
    set_movie_saved(user_id, code, new_state)
    msg = "Kino saqlanganlarga qo'shildi!" if new_state else "Kino saqlanganlardan o'chirildi!"
    likes, dislikes, views = get_movie_stats(code)
    role = get_user_role(user_id)
    try:
        bot_username = await get_bot_username()
        await bot.edit_message_reply_markup(
            chat_id=callback.message.chat.id,
            message_id=callback.message.message_id,
            reply_markup=generate_movie_keyboard(
                code, likes, dislikes, new_state,
                is_vip_viewer=role in ['vip', 'assistant', 'super_admin'],
                bot_username=bot_username))
    except Exception:
        pass
    await callback.answer(msg, show_alert=True)

# =====================================================================
# UPLOAD MOVIE
# =====================================================================
@dp.callback_query_handler(lambda c: c.data == "sa_upload_short")
async def sa_upload_short_start(callback: CallbackQuery, state: FSMContext):
    await callback.answer()
    await _ask_genre(callback.message, state)

@dp.message_handler(Text(equals="📤 Yuklash"))
async def msg_upload_short_start(message: Message, state: FSMContext):
    user_id = message.from_user.id
    await _close_previous_section(user_id)
    await state.finish()
    role = get_user_role(user_id)
    if role not in ['super_admin', 'assistant']:
        return
    await _ask_genre(message, state)

async def _ask_genre(message: Message, state: FSMContext):
    rows = []
    pairs = list(enumerate(GENRES_LIST))
    for j in range(0, len(pairs), 2):
        row = [InlineKeyboardButton(text=g, callback_data=f"sa_short_genre_{idx}")
               for idx, g in pairs[j:j + 2]]
        rows.append(row)
    rows.append([InlineKeyboardButton(text="◀️ Bekor qilish", callback_data="sa_menu")])
    genres_kb = InlineKeyboardMarkup(inline_keyboard=rows)
    await message.answer("📂 <b>Janrni tanlang:</b>", reply_markup=genres_kb, parse_mode="HTML")
    await SuperAdminState.waiting_for_short_genre.set()

@dp.callback_query_handler(lambda c: c.data and c.data.startswith("sa_short_genre_"),
                            state=SuperAdminState.waiting_for_short_genre)
async def sa_short_genre_selected(callback: CallbackQuery, state: FSMContext):
    genre_idx = int(callback.data.split("_")[-1])
    genre = GENRES_LIST[genre_idx]
    await state.update_data(genre=genre)
    await callback.answer()
    await callback.message.edit_text(
        f"✅ Janr: <b>{genre}</b>\n\n📹 Endi kinoning <b>qisqa treyler videosini</b> yuboring "
        f"(bu — asosiy kanalga reklama sifatida joylanadi):",
        parse_mode="HTML")
    await SuperAdminState.waiting_for_short_video.set()

def _extract_video_file(message: Message):
    """Video ham 'video', ham 'document' (siqilmagan fayl) sifatida yuborilishi mumkin —
    avvalgi versiya faqat content_types=['video']ni qabul qilgani uchun, ko'pchilik filmlar
    sifatni saqlash maqsadida 'fayl' sifatida yuborilganda bot ularni umuman payqamay,
    yuklash rejimi 'ishlamayapti' degan taassurot qoldirgan. Endi ikkalasi ham qo'llab-quvvatlanadi.
    Qaytaradi: (file_id, send_kind) yoki (None, None)."""
    if message.video:
        return message.video.file_id, "video"
    if message.document:
        return message.document.file_id, "document"
    return None, None

@dp.message_handler(state=SuperAdminState.waiting_for_short_video,
                     content_types=['video', 'document'])
async def sa_short_video_received(message: Message, state: FSMContext):
    file_id, kind = _extract_video_file(message)
    if not file_id:
        await message.answer("❌ Iltimos, qisqa treyler videosini «video» yoki «fayl» sifatida yuboring.")
        return
    await state.update_data(short_video_file_id=file_id, short_video_kind=kind)
    await message.answer(
        "✅ Qisqa video qabul qilindi.\n\n"
        "🎞 Endi kinoning <b>to'liq (uzun) videosini</b> yuboring "
        "(bu — maxfiy kanalga joylanadi, foydalanuvchilar shundan ko'radi):",
        parse_mode="HTML")
    await SuperAdminState.waiting_for_full_video.set()

@dp.message_handler(state=SuperAdminState.waiting_for_short_video)
async def sa_short_video_missing(message: Message, state: FSMContext):
    await message.answer("❌ Iltimos, qisqa treyler videosini «video» yoki «fayl» sifatida yuboring.")

@dp.message_handler(state=SuperAdminState.waiting_for_full_video,
                     content_types=['video', 'document'])
async def sa_full_video_received(message: Message, state: FSMContext):
    file_id, kind = _extract_video_file(message)
    if not file_id:
        await message.answer("❌ Iltimos, to'liq kino videosini «video» yoki «fayl» sifatida yuboring.")
        return
    await state.update_data(full_video_file_id=file_id, full_video_kind=kind)
    last_code = get_last_main_channel_code()
    if last_code == 0:
        await message.answer(
            "🆕 Bu — birinchi video. Kino uchun <b>boshlang'ich KODI</b>ni kiriting (Masalan: 27).\n"
            "Bundan keyingi barcha videolar uchun kod <b>avtomatik +1</b> qilib boriladi.",
            parse_mode="HTML")
        await SuperAdminState.waiting_for_short_code.set()
        return
    code = last_code + 1
    await state.update_data(pending_code=code)
    await _show_short_upload_confirmation(message, state)

@dp.message_handler(state=SuperAdminState.waiting_for_full_video)
async def sa_full_video_missing(message: Message, state: FSMContext):
    await message.answer("❌ Iltimos, to'liq kino videosini «video» yoki «fayl» sifatida yuboring.")

@dp.message_handler(state=SuperAdminState.waiting_for_short_code)
async def sa_short_code_received(message: Message, state: FSMContext):
    code_text = message.text.strip()
    if not code_text.isdigit():
        await message.answer("❌ Kod faqat raqamlardan iborat bo'lishi kerak!")
        return
    code = int(code_text)
    if is_code_already_posted(code):
        await message.answer(f"❌ Bu kod ({code}) allaqachon ishlatilgan! Boshqa kodni kiriting:")
        return
    await state.update_data(pending_code=code)
    await _show_short_upload_confirmation(message, state)

async def _show_short_upload_confirmation(message: Message, state: FSMContext):
    data = await state.get_data()
    genre = data.get("genre")
    code = data.get("pending_code")
    year = random.randint(2017, 2026)
    await state.update_data(pending_year=year)
    text = (
        f"🎬 Janr: <b>{genre}</b>\n"
        f"📅 Yil: <b>{year}</b> (tasodifiy)\n"
        f"🔛 Kod: <b>{code}</b>\n\n"
        "Shu ma'lumotlar bilan ikkala kanalga (asosiy + maxfiy) joylashni tasdiqlaysizmi?")
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Tasdiqlash", callback_data="sa_short_confirm"),
         InlineKeyboardButton(text="✏️ Kodni tahrirlash", callback_data="sa_short_edit_code")],
        [InlineKeyboardButton(text="◀️ Bekor qilish", callback_data="sa_menu")]
    ])
    await message.answer(text, reply_markup=kb, parse_mode="HTML")

@dp.callback_query_handler(lambda c: c.data == "sa_short_edit_code")
async def sa_short_edit_code(callback: CallbackQuery, state: FSMContext):
    await callback.answer()
    await callback.message.edit_text("✏️ Yangi kodni kiriting:")
    await SuperAdminState.waiting_for_short_code.set()

@dp.callback_query_handler(lambda c: c.data == "sa_short_confirm")
async def sa_short_confirm(callback: CallbackQuery, state: FSMContext):
    await callback.answer()
    data = await state.get_data()
    short_video_file_id = data.get("short_video_file_id")
    full_video_file_id = data.get("full_video_file_id")
    short_video_kind = data.get("short_video_kind", "video")
    full_video_kind = data.get("full_video_kind", "video")
    genre = data.get("genre")
    code = data.get("pending_code")
    year = data.get("pending_year")
    genre_desc = GENRE_TEMPLATES.get(genre, "Bugun ko'rish uchun qiziqarli film!")
    try:
        secret_caption = f"🎬 {genre} {year} | Kod: {code}"
        # Telegram file_id'si qaysi turda yuborilgan bo'lsa (video yoki document/fayl),
        # kanalga joylashda ham aynan o'sha metodni ishlatish kerak — aks holda
        # "wrong file identifier" xatosi bilan yuklash butunlay to'xtab qolardi.
        if full_video_kind == "document":
            secret_msg = await bot.send_document(
                chat_id=CHANNEL_ID, document=full_video_file_id, caption=secret_caption)
        else:
            secret_msg = await bot.send_video(
                chat_id=CHANNEL_ID, video=full_video_file_id, caption=secret_caption)
        bot_username = await get_bot_username()
        watch_url = f"https://t.me/{bot_username}?start=watch_{code}"
        main_caption = (
            f"🎬 Kino janri: <b>{genre}</b> {year}\n"
            f"🔛 Kino KODI : {code} ✅\n\n"
            f"Kinoni to'ligini pastagi tugma orqali yuklab oling\n\n"
            f"🔐 {genre_desc}\n\n"
            f"🖇 Bot manzili: @Premium_kinolari_bot")
        watch_kb = InlineKeyboardMarkup(
            inline_keyboard=[[InlineKeyboardButton(text="🎬 Tomosha qilish", url=watch_url)]])
        if short_video_kind == "document":
            await bot.send_document(
                chat_id=MAIN_CHANNEL_ID, document=short_video_file_id,
                caption=main_caption, parse_mode="HTML", reply_markup=watch_kb)
        else:
            await bot.send_video(
                chat_id=MAIN_CHANNEL_ID, video=short_video_file_id,
                caption=main_caption, parse_mode="HTML", reply_markup=watch_kb)
        with db_connect() as (conn, cursor):
            cursor.execute(
                "INSERT INTO main_channel_posts "
                "(code, genre, year, posted_at, video_file_id, is_vip, vip_until, secret_message_id) "
                "VALUES (?, ?, ?, ?, ?, 0, 0, ?)",
                (code, genre, year, time.time(), short_video_file_id, secret_msg.message_id))
            conn.commit()
        set_last_main_channel_code(code)
        await callback.message.edit_text(
            f"✅ <b>Kino ikkala kanalga ham joylandi!</b>\n\n"
            f"📌 Janr: {genre} | 📅 Yil: {year} | 🔛 Kod: {code}",
            reply_markup=InlineKeyboardMarkup(
                inline_keyboard=[[InlineKeyboardButton(text="🔙 Asosiy Menu", callback_data="sa_menu")]]),
            parse_mode="HTML")
    except Exception as e:
        await callback.message.edit_text(
            f"❌ Xatolik yuz berdi:\n{str(e)}\n\n"
            "MAIN_CHANNEL_ID va CHANNEL_ID to'g'ri kiritilganligini, bot ikkala kanalga ham admin qilib qo'yilganini tekshiring.",
            reply_markup=InlineKeyboardMarkup(
                inline_keyboard=[[InlineKeyboardButton(text="🔙 Orqaga", callback_data="sa_menu")]]))
    await state.finish()

# =====================================================================
# BOZOR — VIP OBUNA
# =====================================================================
@dp.message_handler(Text(equals="🛒 Bozor"))
async def msg_vip_shop(message: Message, state: FSMContext):
    user_id = message.from_user.id
    await _close_previous_section(user_id)
    await state.finish()
    if is_user_restricted(user_id):
        return
    update_last_active(user_id)
    await send_vip_shop(message.chat.id, message=message, state=state)

@dp.callback_query_handler(lambda c: c.data == "vip_shop")
async def cb_vip_shop(callback: CallbackQuery, state: FSMContext):
    await state.finish()
    await callback.answer()
    await send_vip_shop(callback.message.chat.id, message=callback.message, state=state)

@dp.callback_query_handler(lambda c: c.data and c.data.startswith("buyvip_"))
async def cb_buy_vip_selected(callback: CallbackQuery, state: FSMContext):
    valid, base = await _verify_panel_token(callback, state)
    if not valid:
        return
    _, kind, days_str = base.split("_")
    days = int(days_str)
    label = next(l for d, l, p in VIP_FIXED_PRICES if d == days)
    if kind == "discount":
        price = get_vip_discount_price(days)
    else:
        price = next(p for d, l, p in VIP_FIXED_PRICES if d == days)
    await state.update_data(vip_buy_days=days, vip_buy_price=price, vip_buy_label=label)
    await VipPurchaseState.waiting_for_receipt_photo.set()
    await callback.answer()
    card_number, card_holder = get_vip_card_info()
    holder_line = f" ({card_holder})" if card_holder else ""
    await callback.message.answer(
        f"💳 <b>To'lov</b>\n\n"
        f"Tanlandi: <b>{label}</b> — <b>{price:,} so'm</b>\n\n"
        f"Quyidagi karta raqamiga to'lovni amalga oshiring:\n"
        f"<code>{card_number}</code>{holder_line}\n\n"
        f"To'lovdan so'ng screenshot yuboring, tez orada tekshiriladi.",
        parse_mode="HTML")

    user_id = callback.from_user.id

    async def _payment_reminder():
        await asyncio.sleep(600)
        try:
            current_state = await state.get_state()
            if current_state == VipPurchaseState.waiting_for_receipt_photo.state:
                await bot.send_message(user_id, "⏳ To'lovingizni yakunlamadingiz, davom etasizmi?")
        except Exception:
            pass

    asyncio.ensure_future(_payment_reminder())

@dp.message_handler(state=VipPurchaseState.waiting_for_receipt_photo, content_types=['photo'])
async def process_vip_payment_screenshot(message: Message, state: FSMContext):
    data = await state.get_data()
    days = data.get("vip_buy_days")
    price = data.get("vip_buy_price")
    label = data.get("vip_buy_label")
    user_id = message.from_user.id
    now = time.time()
    req_id = None
    with db_connect() as (conn, cursor):
        cursor.execute(
            "INSERT INTO vip_purchase_requests "
            "(user_id, duration_label, duration_days, price, receipt_file_id, status, created_at) "
            "VALUES (?, ?, ?, ?, ?, 'pending', ?)",
            (user_id, label, days, price, message.photo[-1].file_id, now))
        req_id = cursor.lastrowid
        conn.commit()
    await message.answer(
        "✅ To'lov screenshoti qabul qilindi! Tez orada tekshiriladi, so'ng VIP statusingiz faollashadi.",
        parse_mode="HTML")
    await state.finish()
    try:
        kb = InlineKeyboardMarkup(inline_keyboard=[[
            InlineKeyboardButton(text="✅ Tasdiqlash", callback_data=f"vipreq_ok_{req_id}"),
            InlineKeyboardButton(text="❌ Bekor qilish", callback_data=f"vipreq_no_{req_id}")
        ]])
        sent = await bot.send_photo(
            SUPER_ADMIN_ID, message.photo[-1].file_id,
            caption=f"🛒 <b>Yangi VIP xarid so'rovi #{req_id}</b>\n\n"
                    f"Foydalanuvchi: <code>{user_id}</code>\nMuddat: {label}\nNarx: {price:,} so'm",
            reply_markup=kb, parse_mode="HTML")
        with db_connect() as (conn, cursor):
            cursor.execute(
                "UPDATE vip_purchase_requests SET admin_msg_id = ? WHERE id = ?",
                (sent.message_id, req_id))
            conn.commit()
    except Exception:
        pass

@dp.message_handler(state=VipPurchaseState.waiting_for_receipt_photo)
async def process_vip_payment_screenshot_missing(message: Message, state: FSMContext):
    await message.answer("❌ Iltimos, to'lov screenshotini <b>rasm</b> sifatida yuboring.",
                         parse_mode="HTML")

async def _mark_request_message(message: Message, note: str):
    """VIP so'rov xabari rasm (caption) yoki oddiy matn bo'lishidan qat'iy nazar,
    xabarni xavfsiz yangilaydi. Avvalgi versiyada faqat 'caption' bor deb taxmin
    qilingani uchun, matnli xabarlarda (masalan, 'Kutilayotgan so'rovlar' ro'yxatida)
    tugma bosilganda vizual o'zgarish umuman ko'rinmay qolgan — shu yerda tuzatildi."""
    try:
        if getattr(message, "photo", None):
            new_caption = (message.caption or "") + f"\n\n{note}"
            await message.edit_caption(caption=new_caption, parse_mode="HTML")
        else:
            base_text = message.html_text or message.text or ""
            await message.edit_text(base_text + f"\n\n{note}", parse_mode="HTML")
    except Exception:
        pass

@dp.callback_query_handler(lambda c: c.data and c.data.startswith("vipreq_ok_"))
async def cb_vip_request_approve(callback: CallbackQuery):
    if get_user_role(callback.from_user.id) != 'super_admin':
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    req_id = int(callback.data.split("_")[-1])
    now = time.time()
    with db_connect() as (conn, cursor):
        # Atomik shart: faqat hali ham 'pending' bo'lsa yutamiz — auto-approve loop yoki
        # ikkinchi bosish bilan ikki marta VIP berilishining oldi shu tarzda olinadi.
        cursor.execute(
            "UPDATE vip_purchase_requests SET status = 'approved', decided_at = ? "
            "WHERE id = ? AND status = 'pending'",
            (now, req_id))
        won = cursor.rowcount == 1
        if won:
            cursor.execute(
                "SELECT user_id, duration_days, duration_label FROM vip_purchase_requests WHERE id = ?",
                (req_id,))
            row = cursor.fetchone()
        conn.commit()
    if not won:
        await callback.answer("Bu so'rov allaqachon ko'rib chiqilgan.", show_alert=True)
        return
    user_id, days, label = row
    grant_vip_to_user(user_id, days)
    await callback.answer("✅ Tasdiqlandi!")
    await _mark_request_message(callback.message, "✅ TASDIQLANDI")
    try:
        await bot.send_message(
            user_id,
            f"🎉 To'lovingiz tasdiqlandi! Sizga <b>{label}</b> VIP obuna berildi.",
            parse_mode="HTML")
    except Exception:
        pass
    await deliver_pending_watch_if_any(user_id)

@dp.callback_query_handler(lambda c: c.data and c.data.startswith("vipreq_no_"))
async def cb_vip_request_reject(callback: CallbackQuery):
    if get_user_role(callback.from_user.id) != 'super_admin':
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    req_id = int(callback.data.split("_")[-1])
    now = time.time()
    with db_connect() as (conn, cursor):
        cursor.execute(
            "UPDATE vip_purchase_requests SET status = 'rejected', decided_at = ? "
            "WHERE id = ? AND status = 'pending'",
            (now, req_id))
        won = cursor.rowcount == 1
        if won:
            cursor.execute("SELECT user_id FROM vip_purchase_requests WHERE id = ?", (req_id,))
            row = cursor.fetchone()
        conn.commit()
    if not won:
        await callback.answer("Bu so'rov allaqachon ko'rib chiqilgan.", show_alert=True)
        return
    user_id = row[0]
    await callback.answer("❌ Bekor qilindi")
    await _mark_request_message(callback.message, "❌ BEKOR QILINDI")
    try:
        await bot.send_message(
            user_id, "❌ To'lovingiz tasdiqlanmadi. Savol bo'lsa, admin bilan bog'laning.")
    except Exception:
        pass

@dp.callback_query_handler(lambda c: c.data and c.data.startswith("cancel_autovip_"))
async def cb_cancel_auto_vip(callback: CallbackQuery):
    if get_user_role(callback.from_user.id) != 'super_admin':
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    req_id = int(callback.data.split("_")[-1])
    with db_connect() as (conn, cursor):
        cursor.execute(
            "SELECT user_id, duration_days, status, decided_at FROM vip_purchase_requests WHERE id = ?",
            (req_id,))
        row = cursor.fetchone()
        if not row or row[2] != 'auto_approved':
            await callback.answer("Bu so'rovni bekor qilib bo'lmaydi (holati o'zgargan).",
                                   show_alert=True)
            return
        user_id, days, _, decided_at = row
        if decided_at and (time.time() - decided_at) > 86400:
            await callback.answer("⏱ Bekor qilish muddati tugagan (24 soat)", show_alert=True)
            return
        cursor.execute(
            "UPDATE vip_purchase_requests SET status = 'auto_approved_cancelled', decided_at = ? WHERE id = ?",
            (time.time(), req_id))
        conn.commit()
    revoke_vip_grant(user_id, days)
    await callback.answer("🚫 VIP bekor qilindi.")
    await _mark_request_message(callback.message, "🚫 <b>ADMIN TOMONIDAN BEKOR QILINDI</b>")
    try:
        await bot.send_message(
            user_id,
            "⚠️ VIP obunangiz admin tomonidan bekor qilindi. Savol bo'lsa, admin bilan bog'laning.")
    except Exception:
        pass

# =====================================================================
# BOZORNI BOSHQARISH
# =====================================================================
@dp.callback_query_handler(lambda c: _detok(c.data)[0] == "sa_market_menu")
async def cb_sa_market_menu(callback: CallbackQuery, state: FSMContext):
    valid, base = await _verify_panel_token(callback, state)
    if not valid:
        return
    await state.finish()
    if get_user_role(callback.from_user.id) != 'super_admin':
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    await callback.answer()
    card_number, card_holder = get_vip_card_info()
    lines = [f"💳 Karta: <code>{card_number}</code> ({card_holder or '—'})\n", "🏷 Chegirma narxlar:"]
    for days, label, price in VIP_FIXED_PRICES:
        discount = get_vip_discount_price(days)
        if discount is not None:
            lines.append(f"  • {label}: qat'iy {price:,} so'm | chegirma {discount:,} so'm")
        else:
            lines.append(f"  • {label}: qat'iy {price:,} so'm | chegirma — sozlanmagan")
    with db_connect() as (conn, cursor):
        cursor.execute("SELECT COUNT(*) FROM vip_purchase_requests WHERE status = 'pending'")
        pending_count = cursor.fetchone()[0]
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💳 Karta raqamini sozlash", callback_data="sa_set_card")],
        [InlineKeyboardButton(text="🏷 Chegirma narxlarni sozlash", callback_data="sa_set_discount")],
        [InlineKeyboardButton(text=f"📋 Kutilayotgan so'rovlar ({pending_count})",
                              callback_data="sa_pending_vip")],
        [InlineKeyboardButton(text="◀️ Orqaga", callback_data="sa_menu")]
    ])
    await callback.message.answer(
        "🛒 <b>Bozorni boshqarish</b>\n\n" + "\n".join(lines),
        reply_markup=kb, parse_mode="HTML")

@dp.callback_query_handler(lambda c: c.data == "sa_set_card")
async def cb_sa_set_card_start(callback: CallbackQuery, state: FSMContext):
    if get_user_role(callback.from_user.id) != 'super_admin':
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    await callback.answer()
    await callback.message.answer(
        "💳 Yangi karta raqamini kiriting (masalan: 8600 1234 5678 9012):")
    await BozorAdminState.waiting_for_card_number.set()

@dp.message_handler(state=BozorAdminState.waiting_for_card_number)
async def process_set_card_number(message: Message, state: FSMContext):
    set_setting("vip_card_number", message.text.strip())
    await message.answer(
        "✅ Karta raqami saqlandi. Endi karta egasining ismini kiriting "
        "(yoki '-' agar kerak bo'lmasa):")
    await BozorAdminState.waiting_for_card_holder.set()

@dp.message_handler(state=BozorAdminState.waiting_for_card_holder)
async def process_set_card_holder(message: Message, state: FSMContext):
    holder = message.text.strip()
    set_setting("vip_card_holder", "" if holder == "-" else holder)
    role = get_user_role(message.from_user.id)
    await message.answer("✅ Karta ma'lumotlari saqlandi.",
                         reply_markup=get_main_keyboard(role))
    await state.finish()

@dp.callback_query_handler(lambda c: c.data == "sa_set_discount")
async def cb_sa_set_discount_start(callback: CallbackQuery, state: FSMContext):
    if get_user_role(callback.from_user.id) != 'super_admin':
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    await callback.answer()
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=label, callback_data=f"setdisc_{days}")]
        for days, label, price in VIP_FIXED_PRICES
    ] + [[InlineKeyboardButton(text="◀️ Orqaga", callback_data="sa_market_menu")]])
    await callback.message.answer(
        "🏷 Qaysi muddat uchun chegirma narx belgilaysiz?", reply_markup=kb)


@dp.callback_query_handler(lambda c: c.data and c.data.startswith("setdisc_"))
async def cb_set_discount_duration(callback: CallbackQuery, state: FSMContext):
    days = int(callback.data.split("_")[1])
    await state.update_data(discount_days=days)
    await callback.answer()
    label = next((l for d, l, p in VIP_FIXED_PRICES if d == days), f"{days} kun")
    await callback.message.answer(
        f"🏷 <b>{label}</b> uchun yangi chegirma narxini so'mda kiriting (masalan: 7000):",
        parse_mode="HTML")
    await BozorAdminState.waiting_for_discount_price.set()

@dp.message_handler(state=BozorAdminState.waiting_for_discount_price)
async def process_set_discount_price(message: Message, state: FSMContext):
    if not message.text.strip().isdigit():
        await message.answer("❌ Faqat raqam kiriting!")
        return
    price = int(message.text.strip())
    data = await state.get_data()
    days = data.get('discount_days')
    if not days:
        await message.answer("❌ Sessiya eskirgan, qaytadan urinib ko'ring.")
        await state.finish()
        return
    set_setting(f"vip_discount_{days}", price)
    role = get_user_role(message.from_user.id)
    label = next((l for d, l, p in VIP_FIXED_PRICES if d == days), f"{days} kun")
    await message.answer(
        f"✅ <b>{label}</b> uchun chegirma narx <b>{price:,} so'm</b> qilib saqlandi!",
        reply_markup=get_main_keyboard(role), parse_mode="HTML")
    await state.finish()

@dp.callback_query_handler(lambda c: c.data == "sa_pending_vip")
async def cb_sa_pending_vip(callback: CallbackQuery):
    if get_user_role(callback.from_user.id) != 'super_admin':
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    with db_connect() as (conn, cursor):
        cursor.execute(
            "SELECT id, user_id, duration_label, price, created_at FROM vip_purchase_requests "
            "WHERE status = 'pending' ORDER BY created_at ASC")
        rows = cursor.fetchall()
    if not rows:
        await callback.answer("Kutilayotgan so'rovlar yo'q.", show_alert=True)
        return
    await callback.answer()
    for req_id, user_id, label, price, created_at in rows:
        left_min = max(0, int(3600 - (time.time() - created_at)) // 60)
        kb = InlineKeyboardMarkup(inline_keyboard=[[
            InlineKeyboardButton(text="✅ Tasdiqlash", callback_data=f"vipreq_ok_{req_id}"),
            InlineKeyboardButton(text="❌ Bekor qilish", callback_data=f"vipreq_no_{req_id}")
        ]])
        await callback.message.answer(
            f"🛒 <b>So'rov #{req_id}</b>\nFoydalanuvchi: <code>{user_id}</code>\n"
            f"Muddat: {label}\nNarx: {price:,} so'm\n⏱ Avto-tasdiqgacha: ~{left_min} daqiqa",
            reply_markup=kb, parse_mode="HTML")

# =====================================================================
# XATOLIKLAR HISOBOTI (QO'LDA)
# =====================================================================
@dp.callback_query_handler(lambda c: _detok(c.data)[0] == "sa_error_report")
async def cb_sa_error_report(callback: CallbackQuery, state: FSMContext):
    valid, base = await _verify_panel_token(callback, state)
    if not valid:
        return
    if get_user_role(callback.from_user.id) not in ['super_admin', 'assistant']:
        await callback.answer("Sizda bu huquq yo'q!", show_alert=True)
        return
    rows = list(_bot_errors_log)[-30:]
    await callback.answer()
    if not rows:
        await callback.message.answer("🐞 Hozircha yangi xatoliklar qayd etilmagan.")
        return
    lines = [f"🐞 <b>So'nggi xatoliklar</b> ({len(rows)} ta):\n"]
    for entry in reversed(rows):
        t = datetime.fromtimestamp(entry["occurred_at"]).strftime('%d.%m %H:%M')
        lines.append(f"[{t}] {entry['text']}")
    text = "\n".join(lines)
    for chunk_start in range(0, len(text), 3500):
        await callback.message.answer(text[chunk_start:chunk_start + 3500], parse_mode="HTML")

# =====================================================================
# GLOBAL ERROR HANDLER
# =====================================================================
_last_error_text = None  # ketma-ket bir xil xatolikni qayta-qayta yubormaslik uchun

@dp.errors_handler()
async def global_error_handler(update, exception):
    global ERROR_COUNT, _last_error_text
    ERROR_COUNT += 1
    err_text = f"{type(exception).__name__}: {exception}"
    logger.error(f"Global xatolik: {err_text}")
    _bot_errors_log.append({"text": err_text, "occurred_at": time.time()})
    # Har safar YANGI (avvalgisidan farqli) xatolik yuzaga kelsa — saqlamasdan,
    # darhol Super Adminga yuboriladi. Faqat xuddi o'sha xatolik ketma-ket
    # takrorlansa, spam bo'lmasligi uchun qayta yuborilmaydi.
    if err_text != _last_error_text:
        _last_error_text = err_text
        try:
            await bot.send_message(
                SUPER_ADMIN_ID,
                f"🐞 <b>Yangi xatolik aniqlandi:</b>\n<code>{err_text}</code>",
                parse_mode="HTML")
        except Exception:
            pass
    return True

# =====================================================================
# ON STARTUP — FON JARAYONLARNI ISHGA TUSHIRISH
# =====================================================================
async def on_startup(dispatcher):
    asyncio.ensure_future(vip_purchase_loop())
    asyncio.ensure_future(check_vip_expirations())
    asyncio.ensure_future(status_export_loop())
    asyncio.ensure_future(db_backup_loop())
    asyncio.ensure_future(error_digest_loop())
    asyncio.ensure_future(daily_likes_boost_loop())
    logger.info("✅ Bot ishga tushdi: VIP tekshiruv, avto-tasdiqlash, zaxira, xatolik hisobotlari va kunlik like bonusi faollashtirildi.")

# =====================================================================
# AVTO QAYTA ISHGA TUSHIRISH (watchdog, 3 marta, Super Admin orqali yoqish/o'chirish)
# =====================================================================
RESTART_COUNT_PATH = os.path.join(BASE_DIR, 'restart_count.txt')
MAX_AUTO_RESTARTS = 3

def _read_restart_count() -> int:
    try:
        with open(RESTART_COUNT_PATH, 'r') as f:
            return int((f.read() or '0').strip())
    except Exception:
        return 0

def _write_restart_count(n: int):
    try:
        with open(RESTART_COUNT_PATH, 'w') as f:
            f.write(str(n))
    except Exception:
        pass

if __name__ == '__main__':
    from aiogram import executor
    import asyncio
    import sys
    try:
        asyncio.get_event_loop()
    except RuntimeError:
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)

    async def _reset_restart_count_after_stable_run():
        # Bot 5 daqiqa uzluksiz ishlasa — demak, qayta tushish muvaffaqiyatli bo'ldi,
        # shuning uchun "3 marta" hisoblagichi yangi hodisa uchun nolga tushiriladi.
        await asyncio.sleep(300)
        _write_restart_count(0)

    async def _on_startup_with_watchdog(dispatcher):
        await on_startup(dispatcher)
        asyncio.ensure_future(_reset_restart_count_after_stable_run())

    try:
        executor.start_polling(dp, skip_updates=True, on_startup=_on_startup_with_watchdog)
    except (KeyboardInterrupt, SystemExit):
        raise
    except Exception as crash_exc:
        logger.error(f"Bot kutilmaganda to'xtadi: {crash_exc}")
        auto_restart_on = get_setting('auto_restart_enabled', '1') == '1'
        attempts = _read_restart_count()
        if auto_restart_on and attempts < MAX_AUTO_RESTARTS:
            _write_restart_count(attempts + 1)
            logger.error(f"🔁 Avto qayta ishga tushirish: {attempts + 1}/{MAX_AUTO_RESTARTS}-urinish.")
            os.execv(sys.executable, [sys.executable] + sys.argv)
        else:
            logger.error(
                "⏸ Avto qayta ishga tushirish chegarasiga yetildi (3 marta) yoki Super Admin "
                "tomonidan o'chirilgan — bot to'xtatildi.")
