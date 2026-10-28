# -*- coding: utf-8 -*-
"""
برنامج إدارة مؤسسة تعليمية
===========================
التشغيل:   python school_app.py
ثم يفتح المتصفح تلقائياً على  http://127.0.0.1:8000
المستخدم الافتراضي:  admin   كلمة المرور:  admin   (غيّرها من صفحة الإعدادات)
لتجربة سريعة ببيانات جاهزة:   python school_app.py --demo

لا يحتاج إلى تثبيت أي مكتبة: بايثون فقط.
البيانات تُحفظ في ملف school_data.db بجانب البرنامج (انسخه للنسخ الاحتياطي).

طريقة الحساب (حسب نموذج المؤسسة):
  معدل المادة = (الامتحان1×1 + الامتحان2×2 + الامتحان3×3 + معدل الاختبارات×3) ÷ مجموع أوزان ما أُدخل
  المجموع = معدل المادة × الضارب
  المعدل العام = مجموع المجاميع ÷ مجموع الضوارب
"""
import base64
import hashlib
import html
import math
import os
import random
import secrets
import sqlite3
import sys
import threading
import webbrowser
from datetime import date
from decimal import Decimal, ROUND_HALF_UP
from email.parser import BytesParser
from email.policy import default as email_default
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlencode, urlparse

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DB_FILE = os.environ.get("SCHOOL_DB", os.path.join(BASE_DIR, "school_data.db"))
DB_VERSION = 3
HOST, PORT = "127.0.0.1", 8000

SCALE = 20                                   # الدرجة العظمى دائماً 20
MAX_QUIZZES = 6                              # أقصى عدد اختبارات صغيرة لكل مادة
EXAMS = [("e1", "الامتحان الأول"), ("e2", "الامتحان الثاني"), ("e3", "الامتحان النهائي")]
EXAM_LEVEL = {"e1": 1, "e2": 2, "e3": 3}
WEIGHTS = {"e1": 1, "e2": 2, "e3": 3, "q": 3}
STAGES = [("C1", "C1 — COLLEGE1"), ("C2", "C2 — COLLEGE2")]
STATUSES = [("", "—"), ("abs", "غائب بدون عذر (0)"), ("exc", "غائب بعذر (10)")]
DECISIONS = [("", "—"), ("pass", "متجاوز إلى القسم الأعلى"), ("repeat", "مرخص له في إعادة السنة"),
             ("excluded", "مطرود نهائياً")]
ABS_VALUE = {"abs": 0.0, "exc": 10.0}

# حقول ترويسة الكشف: (المفتاح، العنوان، القيمة الافتراضية، اتجاه الكتابة)
HEADER_FIELDS = [
    ("country_ar", "الدولة (عربي)", "الجمهورية الإسلامية الموريتانية", "rtl"),
    ("country_fr", "الدولة (فرنسي)", "République Islamique de Mauritanie", "ltr"),
    ("motto_ar", "الشعار النصي (عربي)", "شرف - إخاء - عدل", "rtl"),
    ("motto_fr", "الشعار النصي (فرنسي)", "Honneur - Fraternité - Justice", "ltr"),
    ("ministry_ar", "الوزارة (عربي)", "وزارة التهذيب الوطني والتكوين المهني", "rtl"),
    ("ministry_fr", "الوزارة (فرنسي)",
     "Ministère de l'Education Nationale et de la Formation Professionnelle", "ltr"),
    ("region_ar", "الولاية (عربي)", "نواكشوط الغربية", "rtl"),
    ("region_fr", "الولاية (فرنسي)", "Nouakchott Ouest", "ltr"),
    ("school_name_ar", "اسم المؤسسة (عربي)", "الإعدادية العربية - المدرسة الإعدادية", "rtl"),
    ("school_name_fr", "اسم المؤسسة (فرنسي)", "Collège Arabe - Collège", "ltr"),
    ("phone", "الهاتف", "", "ltr"),
    ("email", "البريد الإلكتروني", "", "ltr"),
    ("school_year", "السنة الدراسية", "2024 - 2025", "ltr"),
]
DEFAULT_SETTINGS = {k: v for k, _, v, _ in HEADER_FIELDS}
DEFAULT_SETTINGS["logo"] = ""

AR_DIGITS = str.maketrans("٠١٢٣٤٥٦٧٨٩۰۱۲۳۴۵۶۷۸۹", "01234567890123456789")


# ======================================================================
#                          قاعدة البيانات
# ======================================================================
SCHEMA = """
CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS users(
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    username TEXT NOT NULL UNIQUE,
    salt TEXT NOT NULL,
    pw_hash TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS classes(
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT NOT NULL UNIQUE,
    stage TEXT NOT NULL DEFAULT 'C1' CHECK(stage IN ('C1','C2'))
);
CREATE TABLE IF NOT EXISTS students(
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT NOT NULL,
    class_id INTEGER NOT NULL REFERENCES classes(id),
    nni TEXT DEFAULT '',
    school_no TEXT DEFAULT '',
    sex TEXT DEFAULT '',
    birth_date TEXT DEFAULT '',
    birth_place TEXT DEFAULT '',
    guardian TEXT DEFAULT '',
    phone TEXT DEFAULT '',
    photo TEXT DEFAULT '',
    decision TEXT NOT NULL DEFAULT '' CHECK(decision IN ('','pass','repeat','excluded')),
    director_note TEXT DEFAULT ''
);
CREATE TABLE IF NOT EXISTS subjects(
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name_ar TEXT NOT NULL UNIQUE,
    name_fr TEXT NOT NULL DEFAULT '',
    sort_order INTEGER NOT NULL DEFAULT 0
);
CREATE TABLE IF NOT EXISTS coefficients(
    stage TEXT NOT NULL CHECK(stage IN ('C1','C2')),
    subject_id INTEGER NOT NULL REFERENCES subjects(id) ON DELETE CASCADE,
    coef REAL NOT NULL CHECK(coef > 0),
    PRIMARY KEY(stage, subject_id)
);
CREATE TABLE IF NOT EXISTS teachers(
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT NOT NULL,
    phone TEXT DEFAULT '',
    subject_id INTEGER REFERENCES subjects(id) ON DELETE SET NULL
);
CREATE TABLE IF NOT EXISTS grades(
    student_id INTEGER NOT NULL REFERENCES students(id) ON DELETE CASCADE,
    subject_id INTEGER NOT NULL REFERENCES subjects(id) ON DELETE CASCADE,
    kind TEXT NOT NULL CHECK(kind IN ('e1','e2','e3','q')),
    score REAL,
    status TEXT NOT NULL DEFAULT '' CHECK(status IN ('','abs','exc')),
    PRIMARY KEY(student_id, subject_id, kind),
    CHECK(score IS NOT NULL OR status <> '')
);
CREATE TABLE IF NOT EXISTS quizzes(
    student_id INTEGER NOT NULL REFERENCES students(id) ON DELETE CASCADE,
    subject_id INTEGER NOT NULL REFERENCES subjects(id) ON DELETE CASCADE,
    idx INTEGER NOT NULL,
    score REAL NOT NULL,
    PRIMARY KEY(student_id, subject_id, idx)
);
CREATE TABLE IF NOT EXISTS absences(
    student_id INTEGER NOT NULL REFERENCES students(id) ON DELETE CASCADE,
    day TEXT NOT NULL,
    hours REAL NOT NULL CHECK(hours > 0),
    PRIMARY KEY(student_id, day)
);
"""


def connect():
    db = sqlite3.connect(DB_FILE)
    db.row_factory = sqlite3.Row
    db.execute("PRAGMA foreign_keys = ON")
    return db


def hash_password(password, salt):
    return hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"),
                               bytes.fromhex(salt), 200_000).hex()


def set_password(db, username, password):
    salt = secrets.token_hex(16)
    db.execute("""INSERT INTO users(username, salt, pw_hash) VALUES(?,?,?)
                  ON CONFLICT(username) DO UPDATE SET salt=excluded.salt, pw_hash=excluded.pw_hash""",
               (username, salt, hash_password(password, salt)))


def check_password(db, username, password):
    row = db.execute("SELECT salt, pw_hash FROM users WHERE username=?", (username,)).fetchone()
    if row is None:
        hash_password(password, secrets.token_hex(16))      # توحيد زمن الاستجابة
        return False
    return secrets.compare_digest(hash_password(password, row["salt"]), row["pw_hash"])


def _backup_old_db():
    """ملف بيانات من نسخة أقدم بهيكل مختلف: نحفظه باسم آخر ونبدأ بملف نظيف (لا نحذف شيئاً)."""
    if not os.path.exists(DB_FILE):
        return
    db = sqlite3.connect(DB_FILE)
    try:
        version = db.execute("PRAGMA user_version").fetchone()[0]
        tables = db.execute("SELECT COUNT(*) FROM sqlite_master WHERE type='table'").fetchone()[0]
    finally:
        db.close()
    if tables and version < DB_VERSION:
        backup = f"{DB_FILE}.old_{date.today().isoformat()}.bak"
        n = 1
        while os.path.exists(backup):
            n += 1
            backup = f"{DB_FILE}.old_{date.today().isoformat()}_{n}.bak"
        os.replace(DB_FILE, backup)
        print("تنبيه: وُجد ملف بيانات من نسخة أقدم؛ حُفظ كما هو باسم", os.path.basename(backup))


def init_db():
    _backup_old_db()
    db = connect()
    db.executescript(SCHEMA)
    db.execute(f"PRAGMA user_version = {DB_VERSION}")
    for k, v in DEFAULT_SETTINGS.items():
        db.execute("INSERT OR IGNORE INTO settings(key, value) VALUES(?,?)", (k, v))
    if db.execute("SELECT COUNT(*) FROM users").fetchone()[0] == 0:
        set_password(db, "admin", "admin")
    db.commit()
    db.close()


def get_settings(db):
    return {r["key"]: r["value"] for r in db.execute("SELECT key, value FROM settings")}


# ======================================================================
#                       الحسابات: المعدلات والترتيب
# ======================================================================
def effective(score, status):
    """قيمة الامتحان: الدرجة نفسها، أو 0 للغياب بدون عذر، أو 10 للغياب بعذر."""
    return ABS_VALUE[status] if status in ABS_VALUE else score


def subject_average(entries, quizzes, direct_q, level):
    """
    entries: {'e1': (score,status), ...}   quizzes: [scores]   direct_q: معدل اختبارات مُدخل مباشرة
    يرجع (قيم الامتحانات الثلاثة للعرض، معدل الاختبارات، معدل المادة، عدد الخانات الناقصة)
    """
    shown, parts, missing = [None, None, None], [], 0
    for i, kind in enumerate(("e1", "e2", "e3"), start=1):
        if i > level:
            continue
        item = entries.get(kind)
        if item is None:
            missing += 1
            continue
        value = effective(*item)
        shown[i - 1] = value
        parts.append((WEIGHTS[kind], value))
    q = sum(quizzes) / len(quizzes) if quizzes else direct_q
    if q is None:
        missing += 1
    else:
        parts.append((WEIGHTS["q"], q))
    weight_sum = sum(w for w, _ in parts)
    avg = sum(w * v for w, v in parts) / weight_sum if weight_sum else None
    return shown, q, avg, missing


def class_results(db, class_id, level):
    """نتائج جميع طلاب الفصل حتى الامتحان رقم level (1 أو 2 أو 3)."""
    cls = db.execute("SELECT * FROM classes WHERE id=?", (class_id,)).fetchone()
    if cls is None:
        raise ValueError("الفصل غير موجود")
    subjects = db.execute("""
        SELECT s.id, s.name_ar, s.name_fr, c.coef FROM coefficients c JOIN subjects s ON s.id = c.subject_id
        WHERE c.stage = ? ORDER BY s.sort_order, s.id""", (cls["stage"],)).fetchall()
    students = db.execute("SELECT * FROM students WHERE class_id=? ORDER BY name", (class_id,)).fetchall()

    grades, quizzes = {}, {}
    for g in db.execute("""SELECT g.* FROM grades g JOIN students s ON s.id=g.student_id
                           WHERE s.class_id=?""", (class_id,)):
        grades.setdefault((g["student_id"], g["subject_id"]), {})[g["kind"]] = (g["score"], g["status"])
    for z in db.execute("""SELECT z.* FROM quizzes z JOIN students s ON s.id=z.student_id
                           WHERE s.class_id=? ORDER BY z.idx""", (class_id,)):
        quizzes.setdefault((z["student_id"], z["subject_id"]), []).append(z["score"])
    hours = {}
    for a in db.execute("""SELECT a.student_id, SUM(a.hours) h FROM absences a
                           JOIN students s ON s.id=a.student_id
                           WHERE s.class_id=? GROUP BY a.student_id""", (class_id,)):
        hours[a["student_id"]] = a["h"]

    results = []
    for st in students:
        rows, total, coef_sum, missing = [], 0.0, 0.0, 0
        for sub in subjects:
            entries = grades.get((st["id"], sub["id"]), {})
            direct = entries["q"][0] if "q" in entries else None
            shown, q, avg, miss = subject_average(entries, quizzes.get((st["id"], sub["id"]), []), direct, level)
            missing += miss
            sub_total = avg * sub["coef"] if avg is not None else None
            if sub_total is not None:
                total += sub_total
                coef_sum += sub["coef"]
            rows.append({"subject": sub, "exams": shown, "q": q, "avg": avg, "total": sub_total})
        general = total / coef_sum if coef_sum > 0 else None
        results.append({"student": st, "rows": rows, "total": total, "coef_sum": coef_sum,
                        "avg": general, "rank": None, "missing": missing, "hours": hours.get(st["id"], 0.0)})
    ranked = [r for r in results if r["avg"] is not None]
    for r in ranked:
        r["rank"] = 1 + sum(1 for o in ranked if o["avg"] > r["avg"] + 1e-9)
    return {"class": cls, "subjects": subjects, "results": results, "ranked_count": len(ranked)}


# ======================================================================
#                           أدوات صغيرة
# ======================================================================
def esc(v):
    return html.escape("" if v is None else str(v), quote=True)


def parse_num(text):
    """يقبل الأرقام العربية والفاصلة العشرية. يرجع None إذا كان الحقل فارغاً."""
    t = ("" if text is None else str(text)).strip().translate(AR_DIGITS)
    t = t.replace("٫", ".").replace("،", ".").replace(",", ".")
    if t == "":
        return None
    try:
        v = float(t)
    except ValueError:
        raise ValueError(f"قيمة غير صحيحة: {text}")
    if not math.isfinite(v):
        raise ValueError(f"قيمة غير صحيحة: {text}")
    return v


def parse_score(text):
    """درجة من 0 إلى 20 بمنزلتين عشريتين على الأكثر."""
    v = parse_num(text)
    if v is None:
        return None
    if not 0 <= v <= SCALE:
        raise ValueError(f"الدرجة يجب أن تكون بين 0 و {SCALE}")
    if abs(round(v, 2) - v) > 1e-9:
        raise ValueError("الدرجة لها منزلتان عشريتان فقط")
    return round(v, 2)


def r2(x):
    return Decimal(repr(float(x))).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)


def f2(x):
    """رقم بمنزلتين عشريتين وفاصلة عربية كما في نموذج الكشف: 12,17"""
    return "" if x is None else str(r2(x)).replace(".", ",")


def fmt(x, d=2):
    """رقم للعرض في الصفحات والحقول (بدون أصفار زائدة)."""
    if x is None:
        return ""
    s = f"{x:.{d}f}".rstrip("0").rstrip(".")
    return s or "0"


# تحويل بسيط للاسم العربي إلى أحرف لاتينية لعرضه في الجانب الفرنسي من الكشف
_AR2LAT = {
    "ا": "a", "أ": "a", "إ": "i", "آ": "a", "ء": "", "ؤ": "u", "ئ": "i",
    "ب": "b", "ت": "t", "ث": "th", "ج": "j", "ح": "h", "خ": "kh",
    "د": "d", "ذ": "dh", "ر": "r", "ز": "z", "س": "s", "ش": "sh",
    "ص": "s", "ض": "d", "ط": "t", "ظ": "z", "ع": "a", "غ": "gh",
    "ف": "f", "ق": "q", "ك": "k", "ل": "l", "م": "m", "ن": "n",
    "ه": "h", "ة": "a", "و": "ou", "ي": "i", "ى": "a", "لا": "la",
    " ": " ", "-": "-", "'": "'",
}
# أسماء شائعة تُكتب بشكل أفضل يدوياً
_NAME_FIX = {
    "محمد": "Mohamed", "أحمد": "Ahmed", "عبدالله": "Abdallah", "عبد الله": "Abdallah",
    "فاطمة": "Fatima", "مريم": "Mariam", "خديجة": "Khadija", "عائشة": "Aicha",
    "سيدي": "Sidi", "الشيخ": "Cheikh", "زينب": "Zeineb", "يحيى": "Yahya",
    "آمنة": "Amina", "أمين": "Amine", "إبراهيم": "Ibrahim", "اسماعيل": "Ismail",
    "عثمان": "Othman", "عمر": "Omar", "علي": "Ali", "حسن": "Hassan", "حسين": "Hussein",
    "يوسف": "Youssef", "يعقوب": "Yacoub", "موسى": "Moussa", "عيسى": "Issa",
    "صالح": "Saleh", "سعد": "Saad", "سعيد": "Said", "سالم": "Salem",
    "ولد": "Ould", "بنت": "Mint", "منت": "Mint", "اباه": "Abah",
    "المختار": "Mokhtar", "مختار": "Mokhtar",
}


def name_fr(name):
    """يحوّل الاسم العربي تقريباً إلى كتابة لاتينية لجانب الكشف الفرنسي."""
    if not name:
        return ""
    s = str(name).strip()
    # استبدال الأسماء الشائعة أولاً (أطول تطابق)
    for ar, lat in sorted(_NAME_FIX.items(), key=lambda x: -len(x[0])):
        s = s.replace(ar, lat)
    out = []
    i = 0
    while i < len(s):
        if s[i:i+2] == "لا":
            out.append("la")
            i += 2
            continue
        ch = s[i]
        if ch in _AR2LAT:
            out.append(_AR2LAT[ch])
        elif ch.isascii():
            out.append(ch)
        i += 1
    # تنظيف المسافات وتكبير أول حرف من كل كلمة
    parts = "".join(out).split()
    return " ".join(p[:1].upper() + p[1:] if p else "" for p in parts)


def options(rows, selected=None, empty=None, label="name", value="id"):
    out = [f"<option value=''>{esc(empty)}</option>"] if empty is not None else []
    for r in rows:
        if isinstance(r, tuple):
            v, text = r
        else:
            v, text = r[value], r[label]
        sel = " selected" if selected is not None and str(selected) == str(v) else ""
        out.append(f"<option value='{esc(v)}'{sel}>{esc(text)}</option>")
    return "".join(out)


def today():
    return date.today().isoformat()


def today_fr():
    return date.today().strftime("%d/%m/%Y")


def image_data_uri(data, max_bytes=1_000_000):
    """يتحقق أن الملف صورة حقيقية (PNG/JPG/GIF/WEBP) ويحوّله إلى نص يُحفظ في القاعدة."""
    if not data:
        return None
    if len(data) > max_bytes:
        raise ValueError(f"حجم الصورة كبير (الحد الأقصى {max_bytes // 1000} كيلوبايت)")
    mime = None
    for sig, m in ((b"\x89PNG\r\n\x1a\n", "image/png"), (b"\xff\xd8\xff", "image/jpeg"),
                   (b"GIF87a", "image/gif"), (b"GIF89a", "image/gif")):
        if data.startswith(sig):
            mime = m
    if mime is None and data[:4] == b"RIFF" and data[8:12] == b"WEBP":
        mime = "image/webp"
    if mime is None:
        raise ValueError("صيغة الصورة غير مدعومة (استخدم PNG أو JPG أو GIF أو WEBP)")
    return f"data:{mime};base64," + base64.b64encode(data).decode("ascii")


def parse_multipart(content_type, body):
    """يقرأ نموذجاً فيه رفع ملفات. يرجع (الحقول النصية، الملفات)."""
    raw = b"Content-Type: " + content_type.encode("latin-1", "replace") + b"\r\nMIME-Version: 1.0\r\n\r\n" + body
    msg = BytesParser(policy=email_default).parsebytes(raw)
    fields, files = {}, {}
    for part in msg.iter_parts():
        name = part.get_param("name", header="content-disposition")
        if not name:
            continue
        payload = part.get_payload(decode=True) or b""
        if part.get_filename() is not None:
            files[name] = (part.get_filename(), payload)
        else:
            fields.setdefault(name, []).append(payload.decode("utf-8", "replace"))
    return fields, files


# ======================================================================
#                          القالب العام (RTL)
# ======================================================================
CSS = """
:root{--bg:#f3f5f9;--card:#fff;--ink:#1b2430;--muted:#667085;--line:#d9dee7;--brand:#1f5fbf;--brand-d:#174a96;--ok:#127a3d;--bad:#b42318}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--ink);font-family:"Segoe UI",Tahoma,Arial,sans-serif;font-size:16px;direction:rtl;text-align:right}
header.top{background:var(--brand);color:#fff;padding:12px 24px;display:flex;justify-content:space-between;align-items:center;gap:12px;flex-wrap:wrap}
header.top a{color:#fff;text-decoration:none;font-weight:600}
header.top .t{font-size:18px;font-weight:700}
main{max-width:1150px;margin:22px auto;padding:0 16px}
h1{font-size:22px;margin:0 0 14px}
.card{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:16px;margin-bottom:16px}
.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(210px,1fr));gap:14px}
.tile{display:block;background:var(--card);border:1px solid var(--line);border-radius:12px;padding:22px 14px;text-align:center;text-decoration:none;color:var(--ink);font-size:18px;font-weight:600;transition:.15s}
.tile:hover{border-color:var(--brand);box-shadow:0 2px 10px #1f5fbf22;transform:translateY(-2px)}
.tile small{display:block;color:var(--muted);font-weight:400;font-size:13px;margin-top:6px}
table{width:100%;border-collapse:collapse;background:#fff}
th,td{border:1px solid var(--line);padding:7px 9px;text-align:right;vertical-align:middle}
th{background:#eef2f8;font-weight:700}
tr:nth-child(even) td{background:#fafbfd}
input,select,textarea{font:inherit;padding:7px 9px;border:1px solid #b9c2d0;border-radius:7px;background:#fff;direction:rtl;max-width:100%}
input[dir=ltr]{direction:ltr;text-align:left}
input.num{width:84px;text-align:center}
input:focus,select:focus,textarea:focus{outline:2px solid #1f5fbf55;border-color:var(--brand)}
label{display:inline-block;margin:0 0 4px;font-weight:600;font-size:14px;color:#344054}
.form-row{display:flex;flex-wrap:wrap;gap:12px;align-items:flex-end}
.form-row>div{display:flex;flex-direction:column}
button,.btn{font:inherit;padding:8px 16px;border:0;border-radius:7px;background:var(--brand);color:#fff;cursor:pointer;text-decoration:none;display:inline-block}
button:hover,.btn:hover{background:var(--brand-d)}
button.danger{background:var(--bad)}
button.light,.btn.light{background:#e7ecf4;color:var(--ink)}
.msg{padding:10px 14px;border-radius:8px;margin-bottom:14px;font-weight:600}
.msg.ok{background:#e6f6ec;color:var(--ok);border:1px solid #b6e3c6}
.msg.err{background:#fdeceb;color:var(--bad);border:1px solid #f4b8b3}
.muted{color:var(--muted)}
.warn{background:#fff6e0;border:1px solid #f0d58a;padding:10px 14px;border-radius:8px;margin-bottom:14px}
.inline{display:inline}
.actions{white-space:nowrap}
.login{max-width:380px;margin:9vh auto}
.login input{width:100%}
.login .card{padding:26px}
.badge{display:inline-block;padding:2px 9px;border-radius:99px;font-size:13px;background:#eef2f8}
.stat{font-weight:700}
.low{color:var(--bad);font-weight:700}
.thumb{width:70px;height:84px;object-fit:cover;border:1px solid var(--line);border-radius:6px}
.logo-prev{max-height:80px;border:1px solid var(--line);border-radius:6px;padding:4px;background:#fff}
fieldset{border:1px solid var(--line);border-radius:10px;margin:0 0 14px;padding:12px 14px}
legend{font-weight:700;padding:0 6px}
.cols2{display:grid;grid-template-columns:repeat(auto-fill,minmax(300px,1fr));gap:12px}
.cols2>div{display:flex;flex-direction:column}
.cols2 input{width:100%}
@media(max-width:640px){.form-row>div{width:100%}input,select{width:100%}}
"""


def layout(title, body, school="", msg=None, ok=True, show_nav=True):
    nav = ""
    if show_nav:
        nav = (f"<header class='top'><span class='t'>{esc(school)}</span><span>"
               f"<a href='/'>القائمة الرئيسية</a>  |  <a href='/logout'>تسجيل الخروج</a></span></header>")
    flash = f"<div class='msg {'ok' if ok else 'err'}'>{esc(msg)}</div>" if msg else ""
    heading = f"<h1>{esc(title)}</h1>" if show_nav else ""
    return (f"<!DOCTYPE html><html lang='ar' dir='rtl'><head><meta charset='utf-8'>"
            f"<meta name='viewport' content='width=device-width,initial-scale=1'>"
            f"<title>{esc(title)}</title><style>{CSS}</style></head><body>{nav}"
            f"<main>{heading}{flash}{body}</main></body></html>")


# ======================================================================
#              كشف الدرجات (A4 أفقي) — مطابق لنموذج المؤسسة
# ======================================================================
SHEET_CSS = """
@page{size:A4 landscape;margin:5mm}
*{box-sizing:border-box}
body{margin:0;font-family:Arial,Tahoma,"Segoe UI",sans-serif;color:#000;background:#e9ecf1;
     -webkit-print-color-adjust:exact;print-color-adjust:exact}
.toolbar{position:sticky;top:0;z-index:5;background:#1f5fbf;color:#fff;padding:8px 16px;display:flex;gap:12px;align-items:center;direction:rtl}
.toolbar button{font:inherit;padding:6px 14px;border:0;border-radius:6px;background:#fff;color:#1f5fbf;cursor:pointer}
.toolbar-note{font-size:13px}
.sheet{--fs:12px;--rh:6.6mm;--pw:22mm;--ph:25mm;--hs:10.5px;--lh:1.3;--sr:5.6mm;
       width:287mm;height:199mm;margin:10px auto;padding:3mm 5mm;background:#fff;overflow:hidden;
       border:1px solid #bbb;font-size:var(--fs);line-height:var(--lh)}
.sheet.m{--fs:11px;--rh:5.3mm;--pw:19mm;--ph:22mm;--hs:9.5px;--lh:1.2;--sr:5.1mm}
.sheet.x{--fs:9.5px;--rh:4.3mm;--pw:16mm;--ph:18mm;--hs:8.5px;--lh:1.18;--sr:4.4mm}
.in{height:100%;display:flex;flex-direction:column}
.hd{display:grid;grid-template-columns:1fr 34mm 1fr;align-items:start;gap:4mm}
.hd .ar{direction:rtl;text-align:right}
.hd .fr{direction:ltr;text-align:left}
.hd .mid{text-align:center}
.hd .mid img{max-height:var(--ph);max-width:30mm}
.hd .mid .ct{font-size:9px;direction:ltr;margin-top:.8mm;line-height:1.2}
.hd .s{font-size:var(--hs)}
.hd .big{font-size:calc(var(--hs) + 3px);font-weight:700}
.hd .gap{margin-top:1.6mm}
.info{display:grid;grid-template-columns:1fr 34mm 1fr;align-items:start;gap:4mm;margin-top:3mm}
.info .ar{direction:rtl;text-align:right;line-height:calc(var(--lh) + .3);font-size:calc(var(--fs) + 1px)}
.info .fr{direction:ltr;text-align:left;line-height:calc(var(--lh) + .3);font-size:calc(var(--fs) + 1px);
          font-family:Georgia,"Times New Roman",serif}
.info .title{font-size:calc(var(--fs) + 5px);font-weight:700;margin-bottom:.8mm}
.info .v{font-weight:700}
.photo{width:var(--pw);height:var(--ph);border:1px solid #444;margin:0 auto;overflow:hidden;background:#fff}
.photo img{width:100%;height:100%;object-fit:cover;display:block}
.photo svg{width:100%;height:100%;fill:#222;display:block}
.cls{text-align:center;font-size:calc(var(--fs) + 1px);margin-top:.8mm;white-space:nowrap}
table.t{width:100%;border-collapse:collapse;table-layout:fixed;margin-top:1.5mm;direction:rtl}
table.t th,table.t td{border:1px solid #000;padding:0 3px;text-align:center;overflow:hidden;font-size:var(--fs)}
table.t th{background:#e2e2e2;line-height:1.2;padding:1px 3px}
table.t td{height:var(--rh)}
table.t td.ar{text-align:right;font-weight:600;line-height:1.15}
table.t td.fr{text-align:left;direction:ltr;line-height:1.15}
table.t th .f{display:block;white-space:nowrap;direction:ltr}
.ft{display:flex;direction:ltr;justify-content:space-between;align-items:flex-start;gap:5mm;margin-top:3.5mm;padding-top:1mm}
.sum{width:122mm;border-collapse:collapse;table-layout:fixed}
.sum td{border:1px solid #000;padding:0 5px;height:var(--sr);font-size:calc(var(--fs) - .5px);overflow:hidden;white-space:nowrap}
.sum td.fr{text-align:left;direction:ltr;font-weight:600}.sum td.ar{text-align:right;direction:rtl;font-weight:600}
.sum td.c{text-align:center;font-weight:700}
.sum .dec{text-align:center;font-weight:700;background:#f2f2f2}
.radio{display:inline-block;width:11px;height:11px;border:1.5px solid #000;border-radius:50%;position:relative;vertical-align:middle}
.radio.on::after{content:"";position:absolute;left:2px;top:2px;right:2px;bottom:2px;background:#000;border-radius:50%}
.mid2{flex:1;text-align:center;direction:rtl}
.mid2 .box{border:1px solid #000;display:inline-block;padding:1px 20px;margin-bottom:2mm;font-weight:700}
.mid2 .dt{direction:ltr;font-weight:700}
.mid2 .sign{margin-top:3mm;font-weight:700}
.mid2 .sign small{display:block;font-weight:700;margin-top:.8mm;font-size:calc(var(--fs) - 1.5px)}
.dir{width:82mm;direction:rtl;text-align:right}
.dir .h{display:flex;justify-content:space-between;font-weight:700;margin-bottom:.5mm;direction:ltr}
.dir .l{border-bottom:1.5px dotted #000;height:calc(var(--sr) + .5mm);font-size:calc(var(--fs) - 1px);overflow:hidden;white-space:nowrap}
@media print{
  body{background:#fff}.toolbar{display:none}
  .sheet{margin:0;border:0;width:287mm;height:199mm;page-break-after:always;break-after:page}
  .sheet:last-child{page-break-after:auto;break-after:auto}
}
"""

# حماية: إذا زاد المحتوى عن الصفحة لأي سبب (مواد كثيرة جداً) تُصغَّر الأبعاد تلقائياً حتى يستقر في صفحة واحدة
SHEET_JS = """
window.addEventListener('load',function(){
 document.querySelectorAll('.sheet').forEach(function(s){
  var inner=s.querySelector('.in'),rh=parseFloat(getComputedStyle(s).getPropertyValue('--rh')),
      fs=parseFloat(getComputedStyle(s).getPropertyValue('--fs')),k=0;
  while(inner.scrollHeight>inner.clientHeight+1&&k<60){
   rh=Math.max(rh-0.15,2.2);fs=Math.max(fs-0.12,6);
   s.style.setProperty('--rh',rh+'mm');s.style.setProperty('--fs',fs+'px');k++;}
 });
});
"""

PHOTO_PLACEHOLDER = ("<svg viewBox='0 0 100 100' xmlns='http://www.w3.org/2000/svg'><circle cx='50' cy='36' r='18'/>"
                     "<path d='M10 100c2-28 20-40 40-40s38 12 40 40z'/><path d='M22 22l28-14 28 14-28 12z'/></svg>")


def sheet_html(res, cls, exam, S):
    """صفحة كشف واحدة لطالب واحد."""
    st = res["student"]
    exam_name = dict(EXAMS)[exam]
    n = len(res["rows"])
    density = "" if n <= 10 else (" m" if n <= 14 else " x")
    trs = []
    for r in res["rows"]:
        sub = r["subject"]
        exams = "".join(f"<td>{f2(v)}</td>" for v in r["exams"])
        coef = fmt(sub["coef"]).replace(".", ",")
        trs.append(f"<tr><td class='ar'>{esc(sub['name_ar'])}</td><td class='fr'>{esc(sub['name_fr'])}</td>{exams}"
                   f"<td>{f2(r['q'])}</td><td>{f2(r['avg'])}</td><td>{coef}</td><td>{f2(r['total'])}</td><td></td></tr>")
    annual = exam == "e3"
    fr_suffix = {"e1": " — 1er Examen", "e2": " — 2ème Examen", "e3": ""}[exam]
    logo = f"<img src='{esc(S['logo'])}' alt=''>" if S.get("logo") else ""
    photo = f"<img src='{esc(st['photo'])}' alt=''>" if st["photo"] else PHOTO_PLACEHOLDER
    parts = []
    if S["phone"]:
        parts.append(f"Tél. : {esc(S['phone'])}")
    if S["email"]:
        parts.append(f"Email : {esc(S['email'])}")
    contact = "   ".join(parts)
    has_any = res["avg"] is not None

    decision = ""
    if annual:
        rows = ""
        for key, fr, ar in (("pass", "Passe en classe supérieure", "متجاوز إلى القسم الأعلى"),
                            ("repeat", "Redoublement autorisé", "مرخص له في إعادة السنة"),
                            ("excluded", "Exclusion définitive", "مطرود نهائياً")):
            on = " on" if st["decision"] == key else ""
            rows += (f"<tr><td class='fr'>{fr}</td><td class='c' colspan='2'><span class='radio{on}'></span></td>"
                     f"<td class='ar'>{ar}</td></tr>")
        decision = f"<tr><td colspan='4' class='dec'>Decision - القرار</td></tr>{rows}"
    avg_fr = "Moyenne Générale Annuelle:" if annual else "Moyenne Générale:"
    avg_ar = "المعدل السنوي العام:" if annual else "المعدل العام:"
    lines = f"<div class='l'>{esc(st['director_note'])}</div>" + "<div class='l'></div>" * 2
    hours = fmt(res["hours"]).replace(".", ",") or "0"
    total_txt = f2(res["total"]) if has_any else ""
    coef_txt = fmt(res["coef_sum"]).replace(".", ",") if has_any else ""

    return f"""
<section class="sheet{density}"><div class="in">
  <div class="hd">
    <div class="ar">
      <div class="big">{esc(S['country_ar'])}</div><div class="s">{esc(S['motto_ar'])}</div>
      <div class="s"><b>{esc(S['ministry_ar'])}</b></div><div class="s">{esc(S['region_ar'])}</div>
      <div class="big gap">{esc(S['school_name_ar'])}</div>
    </div>
    <div class="mid">{logo}<div class="ct">{contact}</div></div>
    <div class="fr">
      <div class="big">{esc(S['country_fr'])}</div><div class="s">{esc(S['motto_fr'])}</div>
      <div class="s"><b>{esc(S['ministry_fr'])}</b></div><div class="s">{esc(S['region_fr'])}</div>
      <div class="big gap">{esc(S['school_name_fr'])}</div>
    </div>
  </div>
  <div style="border-top:1.5px solid #000;margin:1.5mm 0 0.5mm 0"></div>
  <div class="info">
    <div class="ar">
      <div class="title">كشف درجات {esc(exam_name)}</div>
      <div>السنة الدراسية : <span class="v">{esc(S['school_year'])}</span></div>
      <div>اسم التلميذ الرسمي : <span class="v">{esc(st['name'])}</span></div>
      <div>الرقم الوطني : <span class="v">{esc(st['nni'])}</span>    الرقم المدرسي : <span class="v">{esc(st['school_no'])}</span></div>
    </div>
    <div><div class="photo">{photo}</div>
      <div class="cls" dir="ltr"><span>Classe :</span> <b>{esc(cls['name'])}</b> <span dir="rtl">: القسم</span></div></div>
    <div class="fr">
      <div class="title">Bulletin de Notes{fr_suffix}</div>
      <div>Année Scolaire : <span class="v">{esc(S['school_year'])}</span></div>
      <div>Nom et Prénom : <span class="v">{esc(name_fr(st['name']))}</span></div>
      <div>Numéro National : <span class="v">{esc(st['nni'])}</span></div>
    </div>
  </div>
  <table class="t">
    <colgroup><col style="width:13%"><col style="width:13%"><col style="width:8.5%"><col style="width:8.5%">
      <col style="width:8.5%"><col style="width:9.5%"><col style="width:9%"><col style="width:6%">
      <col style="width:8%"><col style="width:16%"></colgroup>
    <thead><tr><th>المواد</th><th><span class="f" style="text-align:left">Matières</span></th>
      <th>الامتحان الأول<span class="f">1er_Compos</span></th><th>الامتحان الثاني<span class="f">2eme_Compo</span></th>
      <th>الامتحان الثالث<span class="f">3eme_Compos</span></th>
      <th>معدل الاختبارات<span class="f">Moy. Interrog</span></th><th>معدل المادة<span class="f">Moy. Discipl</span></th>
      <th>الضارب<span class="f">Coeff</span></th><th>المجموع<span class="f">Total</span></th>
      <th>ملاحظات الأستاذة<span class="f">Observations Professeurs</span></th></tr></thead>
    <tbody>{''.join(trs)}</tbody>
  </table>
  <div class="ft">
    <table class="sum">
      <colgroup><col style="width:44%"><col style="width:17%"><col style="width:10%"><col style="width:29%"></colgroup>
      <tr><td class="fr">Total Général</td><td class="c">{total_txt}</td><td class="c">{coef_txt}</td><td class="ar">المجموع العام</td></tr>
      <tr><td class="fr">{avg_fr}</td><td class="c" colspan="2">{f2(res['avg'])}</td><td class="ar">{avg_ar}</td></tr>
      <tr><td class="fr">Rang:</td><td class="c" colspan="2">{res['rank'] or ''}</td><td class="ar">الرتبة:</td></tr>
      {decision}
    </table>
    <div class="mid2">
      <div class="box">عدد ساعات الغياب :   {hours}   ساعة</div>
      <div class="dt"><span>Date : {today_fr()}</span> <span dir="rtl">: التاريخ</span></div>
      <div class="sign">توقيع وختم مدير المؤسسة<small>Signature et cachet du Directeur de l'Etablissement</small></div>
    </div>
    <div class="dir"><div class="h"><span>Observations du Directeur</span><span style="direction:rtl">ملاحظات المدير</span></div>{lines}</div>
  </div>
</div></section>"""


# ======================================================================
#                         الطلبات والمسارات
# ======================================================================
SESSIONS = {}           # token -> username
ROUTES = {}


def route(path, method="GET", public=False):
    def deco(fn):
        ROUTES[(method, path)] = (fn, public)
        return fn
    return deco


class Req:
    def __init__(self, db, params, user, files=None):
        self.db, self.params, self.user, self.files = db, params, user, files or {}
        self.settings = get_settings(db)

    def get(self, key, default=""):
        v = self.params.get(key)
        return v[0].strip() if v else default

    def int(self, key):
        v = self.get(key)
        return int(v) if v.isdigit() else None

    def page(self, title, body):
        return ("html", layout(title, body, self.settings["school_name_ar"], self.get("msg") or None,
                               self.get("ok") == "1"))


def redirect(url, msg=None, ok=True):
    if msg:
        parts = urlparse(url)
        q = {k: v for k, v in parse_qs(parts.query).items() if k not in ("msg", "ok")}
        flat = [(k, x) for k, vs in q.items() for x in vs] + [("msg", msg), ("ok", "1" if ok else "0")]
        url = parts.path + "?" + urlencode(flat)
    return ("redirect", url)


def need_choice(items, what):
    if not items:
        return f"<div class='warn'>لا يوجد {what} بعد. أضفها أولاً من القائمة الرئيسية.</div>"
    return ""


def stage_select(name, selected=None):
    return f"<select name='{name}'>{options(STAGES, selected)}</select>"


def get_class(db, class_id):
    return db.execute("SELECT * FROM classes WHERE id=?", (class_id,)).fetchone() if class_id else None


# ---------------------------- الدخول ----------------------------
@route("/login", public=True)
def login_page(r):
    err = f"<div class='msg err'>{esc(r.get('msg'))}</div>" if r.get("msg") else ""
    body = f"""<div class="login"><div class="card">
      <h1 style="text-align:center">{esc(r.settings['school_name_ar'])}</h1>
      <p class="muted" style="text-align:center;margin-top:-6px">تسجيل الدخول</p>{err}
      <form method="post" action="/login">
        <p><label>اسم المستخدم</label><br><input name="username" autofocus required autocomplete="username"></p>
        <p><label>كلمة المرور</label><br><input name="password" type="password" required autocomplete="current-password"></p>
        <p><button style="width:100%">دخول</button></p>
      </form></div></div>"""
    return ("html", layout("تسجيل الدخول", body, show_nav=False))


@route("/login", "POST", public=True)
def login_post(r):
    user, pw = r.get("username"), r.params.get("password", [""])[0]
    if check_password(r.db, user, pw):
        token = secrets.token_urlsafe(32)
        SESSIONS[token] = user
        return ("redirect", "/", token)
    return redirect("/login", "اسم المستخدم أو كلمة المرور غير صحيحة", ok=False)


@route("/logout", public=True)
def logout(r):
    return ("redirect", "/login", "")


# ---------------------------- الرئيسية ----------------------------
@route("/")
def home(r):
    warn = ""
    if check_password(r.db, r.user, "admin"):
        warn = ("<div class='warn'>تنبيه: كلمة المرور ما تزال الافتراضية (admin). "
                "غيّرها من <a href='/settings'>الإعدادات</a>.</div>")
    tiles = [
        ("/classes", "إضافة الفصول", "الفصول الدراسية ومرحلة كل فصل"),
        ("/students", "بيانات الطلاب", "تسجيل وتعديل الطلاب"),
        ("/subjects", "جدول المواد", "المواد بالعربية والفرنسية"),
        ("/coefficients", "جدول الضوارب", "ضوارب كل مرحلة (C1 / C2)"),
        ("/teachers", "جدول الأساتذة", "الأساتذة ومواد تدريسهم"),
        ("/grades", "إدخال درجات الطلاب", "الامتحانات والاختبارات"),
        ("/absences", "تسجيل الغياب", "ساعات الغياب"),
        ("/transcripts", "كشوف الدرجات", "عرض وطباعة (صفحة واحدة)"),
        ("/settings", "الإعدادات", "الترويسة والشعار وكلمة المرور"),
    ]
    cards = "".join(f"<a class='tile' href='{u}'>{t}<small>{s}</small></a>" for u, t, s in tiles)
    return r.page("القائمة الرئيسية", f"{warn}<div class='grid'>{cards}</div>")


# ---------------------------- الفصول ----------------------------
@route("/classes")
def classes_page(r):
    rows = r.db.execute("""SELECT c.*, (SELECT COUNT(*) FROM students s WHERE s.class_id=c.id) AS n
                           FROM classes c ORDER BY c.name""").fetchall()
    trs = "".join(f"""<tr><td colspan="2">
        <form method="post" action="/classes/update" class="form-row">
          <input type="hidden" name="id" value="{c['id']}">
          <div><input name="name" value="{esc(c['name'])}" required></div>
          <div>{stage_select('stage', c['stage'])}</div>
          <button class="light">حفظ</button>
          <button class="danger" formaction="/classes/delete" onclick="return confirm('حذف هذا الفصل؟')">حذف</button>
        </form></td><td>{c['n']}</td></tr>""" for c in rows)
    body = f"""<div class="card"><form method="post" action="/classes/add" class="form-row">
        <div><label>اسم الفصل</label><input name="name" required placeholder="مثال: 1AS1" dir="ltr"></div>
        <div><label>المرحلة</label>{stage_select('stage')}</div>
        <button>إضافة</button></form></div>
        <div class="card"><table><tr><th colspan="2">الفصل والمرحلة</th><th>عدد الطلاب</th></tr>{trs or
        "<tr><td colspan=3 class='muted'>لا توجد فصول بعد</td></tr>"}</table>
        <p class="muted">المرحلة تحدد جدول الضوارب المعتمد للفصل: C1 للسنتين الأولى والثانية، C2 للثالثة والرابعة.</p></div>"""
    return r.page("إضافة الفصول", body)


def valid_stage(v):
    if v not in dict(STAGES):
        raise ValueError("اختر المرحلة")
    return v


@route("/classes/add", "POST")
def classes_add(r):
    if not r.get("name"):
        raise ValueError("اسم الفصل مطلوب")
    r.db.execute("INSERT INTO classes(name, stage) VALUES(?,?)", (r.get("name"), valid_stage(r.get("stage"))))
    return redirect("/classes", "تمت إضافة الفصل")


@route("/classes/update", "POST")
def classes_update(r):
    if not r.get("name"):
        raise ValueError("اسم الفصل مطلوب")
    r.db.execute("UPDATE classes SET name=?, stage=? WHERE id=?",
                 (r.get("name"), valid_stage(r.get("stage")), r.int("id")))
    return redirect("/classes", "تم الحفظ")


@route("/classes/delete", "POST")
def classes_delete(r):
    cid = r.int("id")
    if r.db.execute("SELECT COUNT(*) FROM students WHERE class_id=?", (cid,)).fetchone()[0]:
        raise ValueError("لا يمكن حذف فصل فيه طلاب. انقل الطلاب أو احذفهم أولاً")
    r.db.execute("DELETE FROM classes WHERE id=?", (cid,))
    return redirect("/classes", "تم حذف الفصل")


# ---------------------------- الطلاب ----------------------------
def student_form(r, classes, st=None):
    def f(k):
        return esc(st[k]) if st is not None else ""
    sexes = options([("ذكر", "ذكر"), ("أنثى", "أنثى")], st["sex"] if st is not None else None)
    cls = options(classes, st["class_id"] if st is not None else r.int("class_id"))
    hid = f"<input type='hidden' name='id' value='{st['id']}'>" if st is not None else ""
    photo_now = ""
    if st is not None and st["photo"]:
        photo_now = (f"<div><label>الصورة الحالية</label><img class='thumb' src='{esc(st['photo'])}' alt=''>"
                     f"<label style='font-weight:400'><input type='checkbox' name='remove_photo' value='1'> حذف الصورة</label></div>")
    return f"""<form method="post" action="/students/save" enctype="multipart/form-data" class="form-row">{hid}
        <div><label>الفصل</label><select name="class_id" required>{cls}</select></div>
        <div><label>الاسم الرسمي للتلميذ</label><input name="name" value="{f('name')}" required></div>
        <div><label>الرقم الوطني</label><input name="nni" value="{f('nni')}" dir="ltr" required></div>
        <div><label>الرقم المدرسي</label><input name="school_no" value="{f('school_no')}" dir="ltr" required></div>
        <div><label>الجنس</label><select name="sex">{sexes}</select></div>
        <div><label>تاريخ الميلاد</label><input name="birth_date" value="{f('birth_date')}" placeholder="2012-05-30" dir="ltr"></div>
        <div><label>مكان الميلاد</label><input name="birth_place" value="{f('birth_place')}"></div>
        <div><label>ولي الأمر</label><input name="guardian" value="{f('guardian')}"></div>
        <div><label>هاتف ولي الأمر</label><input name="phone" value="{f('phone')}" dir="ltr"></div>
        {photo_now}
        <div><label>صورة التلميذ (اختياري)</label><input type="file" name="photo" accept="image/*"></div>
        <button>{'حفظ التعديل' if st is not None else 'إضافة الطالب'}</button></form>"""


@route("/students")
def students_page(r):
    classes = r.db.execute("SELECT * FROM classes ORDER BY name").fetchall()
    cid = r.int("class_id")
    sql, args = ("SELECT s.*, c.name AS cname FROM students s JOIN classes c ON c.id=s.class_id WHERE 1=1", [])
    if cid:
        sql += " AND s.class_id=?"
        args.append(cid)
    rows = r.db.execute(sql + " ORDER BY c.name, s.name", args).fetchall()
    trs = "".join(f"""<tr class="stu-row" data-search="{esc(s['name'])} {esc(s['nni'])} {esc(s['school_no'])} {esc(s['cname'])}">
        <td>{esc(s['name'])}</td><td>{esc(s['cname'])}</td><td dir="ltr">{esc(s['nni'])}</td>
        <td dir="ltr">{esc(s['school_no'])}</td><td>{esc(s['birth_date'])}</td>
        <td dir="ltr">{esc(s['phone'])}</td>
        <td class="actions"><a class="btn light" href="/students/edit?id={s['id']}">تعديل</a>
        <form method="post" action="/students/delete" class="inline" onsubmit="return confirm('حذف الطالب مع جميع درجاته وغياباته؟')">
        <input type="hidden" name="id" value="{s['id']}"><input type="hidden" name="class_id" value="{cid or ''}">
        <button class="danger">حذف</button></form></td></tr>""" for s in rows)
    print_links = ""
    if cid:
        print_links = f"""<a class="btn light" target="_blank" href="/students/print?class_id={cid}">طباعة قائمة الفصل</a> """
    print_links += """<a class="btn light" target="_blank" href="/students/print">طباعة كل الفصول</a>"""
    body = need_choice(classes, "فصول") + f"""
      <div class="card"><b>طالب جديد</b><br><br>{student_form(r, classes)}</div>
      <p><a class="btn light" href="/students/import">استيراد قائمة طلاب من إكسل</a> {print_links}</p>
      <div class="card"><form method="get" class="form-row" id="stu-filter-form" onsubmit="return false;">
        <div><label>الفصل</label><select name="class_id" onchange="this.form.submit()">{options(classes, cid, 'كل الفصول')}</select></div>
        <div><label>بحث (الاسم / الرقم الوطني / الرقم المدرسي)</label>
          <input id="stu-search" name="q" placeholder="اكتب للبحث..." autocomplete="off" style="min-width:220px"></div>
        <button type="button" class="light" id="stu-clear" title="مسح البحث">مسح</button>
      </form></div>
      <div class="card"><div class="muted" style="margin-bottom:8px">العدد: <span id="stu-count">{len(rows)}</span></div>
      <table id="stu-table"><thead><tr><th>الاسم</th><th>الفصل</th><th>الرقم الوطني</th><th>الرقم المدرسي</th>
      <th>تاريخ الميلاد</th><th>هاتف ولي الأمر</th><th></th></tr></thead>
      <tbody>
      {trs or "<tr><td colspan=7 class='muted'>لا يوجد طلاب</td></tr>"}
      </tbody></table></div>
      <script>
      (function(){{
        var inp=document.getElementById('stu-search'), clear=document.getElementById('stu-clear'),
            rows=document.querySelectorAll('#stu-table .stu-row'), cnt=document.getElementById('stu-count');
        function filter(){{
          var q=(inp.value||'').trim().toLowerCase(), n=0;
          rows.forEach(function(tr){{
            var show=!q || (tr.getAttribute('data-search')||'').toLowerCase().indexOf(q)>=0;
            tr.style.display=show?'':'none';
            if(show) n++;
          }});
          cnt.textContent=n;
        }}
        inp.addEventListener('input', filter);
        clear.addEventListener('click', function(){{ inp.value=''; filter(); inp.focus(); }});
      }})();
      </script>"""
    return r.page("بيانات الطلاب", body)


@route("/students/print")
def students_print(r):
    cid = r.int("class_id")
    sql, args = ("SELECT s.*, c.name AS cname FROM students s JOIN classes c ON c.id=s.class_id WHERE 1=1", [])
    title = "قائمة كل الطلاب"
    if cid:
        cls = get_class(r.db, cid)
        if not cls:
            return redirect("/students", "الفصل غير موجود", ok=False)
        sql += " AND s.class_id=?"
        args.append(cid)
        title = f"قائمة طلاب الفصل: {cls['name']}"
    rows = r.db.execute(sql + " ORDER BY c.name, s.name", args).fetchall()
    trs = "".join(f"<tr><td>{i}</td><td>{esc(s['name'])}</td><td>{esc(s['cname'])}</td>"
                  f"<td dir='ltr'>{esc(s['nni'])}</td><td dir='ltr'>{esc(s['school_no'])}</td>"
                  f"<td>{esc(s['birth_date'])}</td>"
                  f"<td dir='ltr'>{esc(s['phone'])}</td></tr>"
                  for i, s in enumerate(rows, 1))
    school = r.settings.get("school_name_ar", "")
    page = f"""<!DOCTYPE html><html lang="ar" dir="rtl"><head><meta charset="utf-8">
<title>{esc(title)}</title>
<style>
body{{font-family:Tahoma,Arial,sans-serif;margin:16px;color:#222}}
h1{{font-size:18px;margin:0 0 4px}}
.meta{{color:#555;margin-bottom:14px;font-size:13px}}
table{{width:100%;border-collapse:collapse;font-size:13px}}
th,td{{padding:8px 10px;text-align:right;border:none}}
th{{background:#1f5fbf;color:#fff;font-weight:700}}
tbody tr:nth-child(even){{background:#f0f4fa}}
tbody tr:nth-child(odd){{background:#fff}}
tbody tr:hover{{background:#e4ecf8}}
@media print{{
  .toolbar{{display:none}}
  body{{margin:8mm}}
  tbody tr:nth-child(even){{background:#f0f4fa !important;-webkit-print-color-adjust:exact;print-color-adjust:exact}}
  th{{background:#1f5fbf !important;color:#fff !important;-webkit-print-color-adjust:exact;print-color-adjust:exact}}
}}
.toolbar{{margin-bottom:12px}}
.toolbar button{{font:inherit;padding:6px 14px;cursor:pointer}}
</style></head><body>
<div class="toolbar"><button onclick="window.print()">طباعة</button>
<button onclick="window.close()">إغلاق</button></div>
<h1>{esc(school)}</h1>
<div class="meta">{esc(title)} — السنة الدراسية: {esc(r.settings.get('school_year',''))} — التاريخ: {today_fr()} — العدد: {len(rows)}</div>
<table><thead><tr><th>#</th><th>الاسم</th><th>الفصل</th><th>الرقم الوطني</th><th>الرقم المدرسي</th>
<th>تاريخ الميلاد</th><th>هاتف ولي الأمر</th></tr></thead>
<tbody>{trs or '<tr><td colspan="7">لا يوجد طلاب</td></tr>'}</tbody></table>
</body></html>"""
    return ("html", page)


@route("/students/edit")
def students_edit(r):
    st = r.db.execute("SELECT * FROM students WHERE id=?", (r.int("id"),)).fetchone()
    if st is None:
        return redirect("/students", "الطالب غير موجود", ok=False)
    classes = r.db.execute("SELECT * FROM classes ORDER BY name").fetchall()
    return r.page("تعديل بيانات طالب", f"<div class='card'>{student_form(r, classes, st)}</div>"
                                       f"<a class='btn light' href='/students'>رجوع</a>")


STUDENT_TEXT = ["name", "nni", "school_no", "sex", "birth_date", "birth_place", "guardian", "phone"]


@route("/students/save", "POST")
def students_save(r):
    if not r.get("name") or not get_class(r.db, r.int("class_id")):
        raise ValueError("اسم الطالب والفصل مطلوبان")
    if not r.get("nni") or not r.get("school_no"):
        raise ValueError("الرقم الوطني والرقم المدرسي مطلوبان")
    vals = [r.get(k) for k in STUDENT_TEXT]
    photo = image_data_uri(r.files.get("photo", ("", b""))[1], 1_000_000)
    sid = r.int("id")
    if sid:
        r.db.execute("""UPDATE students SET name=?, nni=?, school_no=?, sex=?, birth_date=?, birth_place=?,
                        guardian=?, phone=?, class_id=? WHERE id=?""", vals + [r.int("class_id"), sid])
        if photo:
            r.db.execute("UPDATE students SET photo=? WHERE id=?", (photo, sid))
        elif r.get("remove_photo") == "1":
            r.db.execute("UPDATE students SET photo='' WHERE id=?", (sid,))
        return redirect("/students", "تم حفظ التعديل")
    r.db.execute("""INSERT INTO students(name, nni, school_no, sex, birth_date, birth_place, guardian, phone,
                    class_id, photo) VALUES(?,?,?,?,?,?,?,?,?,?)""", vals + [r.int("class_id"), photo or ""])
    return redirect(f"/students?class_id={r.int('class_id')}", "تمت إضافة الطالب")


@route("/students/delete", "POST")
def students_delete(r):
    r.db.execute("DELETE FROM students WHERE id=?", (r.int("id"),))
    return redirect("/students" + (f"?class_id={r.get('class_id')}" if r.get("class_id") else ""), "تم حذف الطالب")


# ---------------------- استيراد الطلاب من إكسل / CSV ----------------------
import csv
import io
import re
import zipfile
import xml.etree.ElementTree as ET
from datetime import timedelta

IMPORT_MAX_ROWS = 5000


def norm_head(s):
    """توحيد عنوان العمود: حذف التشكيل والمسافات والرموز وتوحيد الألف والياء."""
    s = str(s or "").strip().lower()
    s = re.sub(r"[ً-ٟـ]", "", s)
    s = s.translate(str.maketrans("أإآىةؤئ", "ااايهوي"))
    s = s.translate(str.maketrans("éèêëàâçôîïûù", "eeeeaacoiiuu"))
    return re.sub(r"[^0-9a-zء-ي]", "", s)


# المفتاح الداخلي ← العناوين المقبولة (بعد التوحيد)
HEADER_ALIASES = {
    "name": ["الاسم", "اسم", "اسمالتلميذ", "اسمالطالب", "الاسمالكامل", "الاسمالرسمي", "التلميذ", "الطالب",
             "nom", "nomprenom", "nometprenom", "nomcomplet", "name", "fullname", "eleve", "student"],
    "given": ["prenom", "prenoms", "firstname", "givenname", "الاسمالشخصي", "الاسمالاول"],
    "surname": ["اللقب", "لقب", "العائله", "اسمالعائله", "surname", "lastname", "familyname"],
    "class": ["الفصل", "القسم", "فصل", "قسم", "الصف", "classe", "class", "classname", "groupe"],
    "nni": ["الرقمالوطني", "رقموطني", "الرقمالوطنيللتلميذ", "نني", "nni", "numerodidentification", "idnational",
            "nationalid", "numeronational", "nnie"],
    "school_no": ["الرقمالمدرسي", "رقممدرسي", "رقمالتسجيل", "رقمالتلميذ", "matricule", "numeroscolaire",
                  "schoolno", "schoolnumber", "studentid", "idscolaire"],
    "sex": ["الجنس", "النوع", "sexe", "sex", "gender", "genre"],
    "birth_date": ["تاريخالميلاد", "تاريخالازدياد", "الميلاد", "datenaissance", "datedenaissance", "birthdate",
                   "dateofbirth", "dob", "naissance"],
    "birth_place": ["مكانالميلاد", "مكانالازدياد", "lieunaissance", "lieudenaissance", "birthplace",
                    "placeofbirth"],
    "guardian": ["وليالامر", "الولي", "ولي", "اسموليالامر", "الاب", "اسمالاب", "tuteur", "parent", "guardian"],
    "phone": ["هاتفوليالامر", "هاتف", "الهاتف", "رقمالهاتف", "رقمهاتفوليالامر", "جوال", "تلفون", "telephone", "tel",
              "phone", "mobile", "telparent", "contact"],
}
ALIAS_LOOKUP = {a: k for k, al in HEADER_ALIASES.items() for a in al}
IMPORT_LABELS = {"name": "الاسم", "surname": "اللقب", "given": "الاسم الشخصي", "class": "الفصل", "nni": "الرقم الوطني",
                 "school_no": "الرقم المدرسي", "sex": "الجنس", "birth_date": "تاريخ الميلاد",
                 "birth_place": "مكان الميلاد", "guardian": "ولي الأمر", "phone": "هاتف ولي الأمر"}


def _col_index(ref):
    n = 0
    for ch in re.match(r"[A-Z]+", ref).group(0):
        n = n * 26 + ord(ch) - 64
    return n - 1


def read_xlsx(data):
    """يقرأ أول ورقة من ملف xlsx بدون أي مكتبة خارجية. يرجع قائمة صفوف (قوائم نصوص/أرقام)."""
    try:
        zf = zipfile.ZipFile(io.BytesIO(data))
    except zipfile.BadZipFile:
        raise ValueError("الملف ليس ملف إكسل (xlsx) صالحاً. احفظه بصيغة .xlsx أو .csv")
    if sum(i.file_size for i in zf.infolist()) > 60_000_000:
        raise ValueError("الملف كبير جداً بعد فك الضغط")
    ns = {"m": "http://schemas.openxmlformats.org/spreadsheetml/2006/main",
          "r": "http://schemas.openxmlformats.org/officeDocument/2006/relationships"}
    names = set(zf.namelist())
    if "xl/workbook.xml" not in names:
        raise ValueError("الملف لا يبدو ملف إكسل (xlsx)")
    shared = []
    if "xl/sharedStrings.xml" in names:
        for si in ET.fromstring(zf.read("xl/sharedStrings.xml")).findall("m:si", ns):
            shared.append("".join(t.text or "" for t in si.iter("{%s}t" % ns["m"])))
    # أول ورقة ظاهرة في المصنف
    wb = ET.fromstring(zf.read("xl/workbook.xml"))
    sheet_path = None
    first = wb.find("m:sheets/m:sheet", ns)
    if first is not None and "xl/_rels/workbook.xml.rels" in names:
        rid = first.get("{%s}id" % ns["r"])
        for rel in ET.fromstring(zf.read("xl/_rels/workbook.xml.rels")):
            if rel.get("Id") == rid:
                t = rel.get("Target").lstrip("/")
                sheet_path = t if t.startswith("xl/") else "xl/" + t
    if sheet_path not in names:
        sheet_path = "xl/worksheets/sheet1.xml"
        if sheet_path not in names:
            raise ValueError("لم أجد أي ورقة بيانات في الملف")
    # هل التنسيق تاريخ؟
    date_styles = set()
    if "xl/styles.xml" in names:
        st = ET.fromstring(zf.read("xl/styles.xml"))
        custom = {}
        for nf in st.findall("m:numFmts/m:numFmt", ns):
            custom[int(nf.get("numFmtId"))] = nf.get("formatCode", "").lower()
        for i, xf in enumerate(st.findall("m:cellXfs/m:xf", ns)):
            fid = int(xf.get("numFmtId", 0))
            code = custom.get(fid, "")
            if 14 <= fid <= 22 or 45 <= fid <= 47 or re.search(r"[dmy]{1,4}", re.sub(r'"[^"]*"|\[[^\]]*\]', "", code)):
                date_styles.add(i)
    rows = []
    for row in ET.fromstring(zf.read(sheet_path)).iter("{%s}row" % ns["m"]):
        rn = int(row.get("r") or len(rows) + 1)
        while len(rows) < rn - 1:
            rows.append([])               # صفوف فارغة محذوفة من الملف: نحفظ ترقيم الصفوف
        cells = {}
        for c in row.findall("m:c", ns):
            ref = c.get("r")
            if not ref:
                continue
            t, v = c.get("t"), c.find("m:v", ns)
            if t == "inlineStr":
                val = "".join(x.text or "" for x in c.iter("{%s}t" % ns["m"]))
            elif v is None or v.text is None:
                continue
            elif t == "s":
                val = shared[int(v.text)] if int(v.text) < len(shared) else ""
            elif t in ("str", "e"):
                val = v.text
            elif t == "b":
                val = "1" if v.text == "1" else "0"
            else:
                try:
                    num = float(v.text)
                except ValueError:
                    val = v.text
                else:
                    if int(c.get("s", 0)) in date_styles and 1 <= num < 2958466:
                        val = (date(1899, 12, 30) + timedelta(days=int(num))).isoformat()
                    else:
                        val = int(num) if num == int(num) and abs(num) < 1e15 else num
            cells[_col_index(ref)] = val
        if cells:
            width = max(cells) + 1
            rows.append([cells.get(i, "") for i in range(width)])
        else:
            rows.append([])
        if len(rows) > IMPORT_MAX_ROWS + 20:
            raise ValueError(f"عدد الصفوف كبير (الحد الأقصى {IMPORT_MAX_ROWS}). قسّم الملف")
    return rows


def read_csv_rows(data):
    for enc in ("utf-8-sig", "cp1256", "latin-1"):
        try:
            text = data.decode(enc)
            break
        except UnicodeDecodeError:
            continue
    sample = text[:4000]
    delim = max(",;\t", key=sample.count) if any(d in sample for d in ",;\t") else ","
    return [row for row in csv.reader(io.StringIO(text), delimiter=delim)]


def cell_text(v):
    if v is None:
        return ""
    if isinstance(v, float):
        v = int(v) if v == int(v) else v
    return re.sub(r"\s+", " ", str(v)).strip()


def norm_sex(v):
    s = norm_head(v)
    if s in ("ذكر", "م", "m", "male", "garcon", "h", "homme", "1", "ذ"):
        return "ذكر"
    if s in ("انثي", "انثى", "ف", "f", "female", "fille", "اناث", "2", "ا"):
        return "أنثى"
    return ""


def norm_date(v):
    s = cell_text(v)
    m = re.match(r"^(\d{4})[-/.](\d{1,2})[-/.](\d{1,2})", s)
    if m:
        y, mo, d = map(int, m.groups())
    else:
        m = re.match(r"^(\d{1,2})[-/.](\d{1,2})[-/.](\d{4})$", s)
        if not m:
            return s          # نبقيه كما هو بدل رفض الصف
        d, mo, y = map(int, m.groups())
    try:
        return date(y, mo, d).isoformat()
    except ValueError:
        return s


def parse_import_rows(rows):
    """يجد صف العناوين ويرجع (الخريطة، صفوف القيم). الاسم هو الحقل الوحيد المطلوب في الملف."""
    for hi, row in enumerate(rows[:15]):
        mapping = {}
        for i, h in enumerate(row):
            k = ALIAS_LOOKUP.get(norm_head(h))
            if k and k not in mapping.values():
                mapping[i] = k
        if "name" in mapping.values():
            lack = [IMPORT_LABELS[k] for k in ("nni", "school_no") if k not in mapping.values()]
            if lack:
                raise ValueError("الملف ينقصه عمود مطلوب: " + "، ".join(lack))
            return mapping, rows[hi + 1:], hi + 1
    raise ValueError("لم أجد عمود الاسم. يجب أن يحتوي الصف الأول على عنوان مثل: الاسم أو اسم التلميذ أو Nom")


def do_import(db, data, filename, default_class, create_classes, new_stage):
    rows = read_csv_rows(data) if filename.lower().endswith((".csv", ".txt")) else read_xlsx(data)
    mapping, body, first_data_row = parse_import_rows(rows)
    classes = {norm_head(c["name"]): c["id"] for c in db.execute("SELECT id, name FROM classes")}
    seen_nni = {x[0] for x in db.execute("SELECT nni FROM students WHERE nni<>''")}
    seen_no = {x[0] for x in db.execute("SELECT school_no FROM students WHERE school_no<>''")}
    added, skipped, created = 0, [], []
    for off, row in enumerate(body):
        line = first_data_row + off + 1
        rec = {}
        for i, k in mapping.items():
            rec[k] = cell_text(row[i]) if i < len(row) else ""
        if not any(rec.values()) and not any(cell_text(x) for x in row):
            continue                                   # صف فارغ تماماً
        name = rec.get("name", "")
        name = " ".join(x for x in (rec.get("given"), name, rec.get("surname")) if x)
        if not name:
            skipped.append((line, "", "بلا اسم"))
            continue
        cname = rec.get("class", "")
        cid = classes.get(norm_head(cname)) if cname else default_class
        if cname and cid is None:
            if create_classes:
                cur = db.execute("INSERT INTO classes(name, stage) VALUES(?,?)", (cname, new_stage))
                cid = classes[norm_head(cname)] = cur.lastrowid
                created.append(cname)
            elif default_class:
                cid = default_class
            else:
                skipped.append((line, name, f"الفصل «{cname}» غير موجود"))
                continue
        if not cid:
            skipped.append((line, name, "لا فصل لهذا الطالب (اختر فصلاً افتراضياً)"))
            continue
        nni, no = rec.get("nni", ""), rec.get("school_no", "")
        if not nni or not no:
            skipped.append((line, name, "الرقم الوطني والرقم المدرسي مطلوبان" if not nni and not no else
                            ("الرقم الوطني مطلوب" if not nni else "الرقم المدرسي مطلوب")))
            continue
        if nni and nni in seen_nni:
            skipped.append((line, name, "الرقم الوطني موجود مسبقاً"))
            continue
        if no and no in seen_no:
            skipped.append((line, name, "الرقم المدرسي موجود مسبقاً"))
            continue
        db.execute("""INSERT INTO students(name, nni, school_no, sex, birth_date, birth_place, guardian, phone,
                      class_id, photo) VALUES(?,?,?,?,?,?,?,?,?,'')""",
                   (name, nni, no, norm_sex(rec.get("sex", "")), norm_date(rec.get("birth_date", "")),
                    rec.get("birth_place", ""), rec.get("guardian", ""), rec.get("phone", ""), cid))
        if nni:
            seen_nni.add(nni)
        if no:
            seen_no.add(no)
        added += 1
        if added + len(skipped) > IMPORT_MAX_ROWS:
            raise ValueError(f"عدد الصفوف كبير (الحد الأقصى {IMPORT_MAX_ROWS})")
    return mapping, added, skipped, created


@route("/students/import")
def students_import_page(r):
    classes = r.db.execute("SELECT * FROM classes ORDER BY name").fetchall()
    body = f"""<div class="card"><b>استيراد قائمة الطلاب من ملف إكسل</b>
      <p class="muted">الحقول المطلوبة في الملف: <b>الاسم، الرقم الوطني، الرقم المدرسي</b> (الصف الذي ينقص أحدها يُتخطى
      ويُذكر في التقرير). باقي الأعمدة اختيارية: الفصل (أو اختر فصلاً افتراضياً)، الجنس، تاريخ الميلاد، مكان الميلاد، ولي الأمر، هاتف ولي الأمر. إن غاب عمود أو كانت
      خانته فارغة يُستورد الطالب عادياً. يتعرف البرنامج على العناوين بالعربية أو الفرنسية (Nom, Classe, Sexe…).
      الصور لا تُستورد من إكسل؛ أضفها لاحقاً من صفحة تعديل الطالب.</p>
      <form method="post" action="/students/import" enctype="multipart/form-data" class="form-row">
        <div><label>الملف (.xlsx أو .csv)</label><input type="file" name="file" accept=".xlsx,.csv,.txt" required></div>
        <div><label>الفصل الافتراضي (لمن ليس له فصل في الملف)</label>
          <select name="class_id">{options(classes, None, '— بلا —')}</select></div>
        <div><label style="font-weight:400"><input type="checkbox" name="create_classes" value="1">
          أنشئ الفصول غير الموجودة تلقائياً</label><br>
          <label>مرحلتها</label>{stage_select('new_stage')}</div>
        <button>استيراد</button></form>
      <p><a href="/students/template.csv">تحميل نموذج جاهز (يفتحه إكسل)</a></p></div>
      <a class="btn light" href="/students">رجوع</a>"""
    return r.page("استيراد الطلاب", body)


@route("/students/import", "POST")
def students_import_run(r):
    fname, data = r.files.get("file", ("", b""))
    if not data:
        raise ValueError("اختر ملفاً أولاً")
    default_class = r.int("class_id")
    if default_class and not get_class(r.db, default_class):
        default_class = None
    mapping, added, skipped, created = do_import(r.db, data, fname, default_class, r.get("create_classes") == "1",
                                                 valid_stage(r.get("new_stage") or "C1"))
    found = "، ".join(IMPORT_LABELS[k] for k in mapping.values())
    missing = "، ".join(IMPORT_LABELS[k] for k in IMPORT_LABELS if k not in mapping.values() and k not in ("surname", "given"))
    sk = "".join(f"<tr><td>{n}</td><td>{esc(nm)}</td><td>{esc(why)}</td></tr>" for n, nm, why in skipped)
    body = f"""<div class="card"><div class="msg ok">تم استيراد <b>{added}</b> طالباً.
      {f'وتخطي <b>{len(skipped)}</b> صفاً.' if skipped else ''}</div>
      <p>الأعمدة التي تعرّف عليها البرنامج: {esc(found)}</p>
      {f'<p class="muted">أعمدة غير موجودة في الملف (تُركت فارغة): {esc(missing)}</p>' if missing else ''}
      {f'<p>فصول أُنشئت: {esc("، ".join(sorted(set(created))))}</p>' if created else ''}</div>
      {f'<div class="card"><b>الصفوف المتخطاة</b><table><tr><th>رقم الصف في الملف</th><th>الاسم</th><th>السبب</th></tr>{sk}</table></div>' if skipped else ''}
      <a class="btn" href="/students">عرض الطلاب</a> <a class="btn light" href="/students/import">استيراد ملف آخر</a>"""
    return r.page("نتيجة الاستيراد", body)


@route("/students/template.csv")
def students_template(r):
    text = ("الاسم,الفصل,الرقم الوطني,الرقم المدرسي,الجنس,تاريخ الميلاد,مكان الميلاد,ولي الأمر,هاتف ولي الأمر\r\n"
            "محمد أحمد سالم,1AS1,1234567890,2024001,ذكر,2012-05-30,نواكشوط,,\r\n")
    return ("file", ("﻿" + text).encode("utf-8"), "text/csv; charset=utf-8", "students_template.csv")


# ---------------------------- المواد ----------------------------
@route("/subjects")
def subjects_page(r):
    rows = r.db.execute("SELECT * FROM subjects ORDER BY sort_order, id").fetchall()
    trs = "".join(f"""<tr><td><form method="post" action="/subjects/save" class="form-row">
        <input type="hidden" name="id" value="{s['id']}">
        <div><input name="name_ar" value="{esc(s['name_ar'])}" required></div>
        <div><input name="name_fr" value="{esc(s['name_fr'])}" dir="ltr"></div>
        <div><input class="num" name="sort_order" value="{s['sort_order']}" title="الترتيب في الكشف"></div>
        <button class="light">حفظ</button>
        <button class="danger" formaction="/subjects/delete" onclick="return confirm('حذف المادة مع درجاتها وضواربها؟')">حذف</button>
        </form></td></tr>""" for s in rows)
    nxt = (rows[-1]["sort_order"] + 1) if rows else 1
    body = f"""<div class="card"><form method="post" action="/subjects/save" class="form-row">
        <div><label>اسم المادة (عربي)</label><input name="name_ar" required></div>
        <div><label>Matière (فرنسي)</label><input name="name_fr" dir="ltr"></div>
        <div><label>الترتيب في الكشف</label><input class="num" name="sort_order" value="{nxt}"></div>
        <button>إضافة</button></form></div>
        <div class="card"><table><tr><th>المادة — Matière — الترتيب</th></tr>
        {trs or "<tr><td class='muted'>لا توجد مواد بعد</td></tr>"}</table>
        <p class="muted">الدرجة العظمى لكل المواد 20. حدّد ضارب كل مادة من «جدول الضوارب».</p></div>"""
    return r.page("جدول المواد", body)


@route("/subjects/save", "POST")
def subjects_save(r):
    if not r.get("name_ar"):
        raise ValueError("اسم المادة مطلوب")
    order = parse_num(r.get("sort_order")) or 0
    args = (r.get("name_ar"), r.get("name_fr"), int(order))
    if r.int("id"):
        r.db.execute("UPDATE subjects SET name_ar=?, name_fr=?, sort_order=? WHERE id=?", args + (r.int("id"),))
    else:
        r.db.execute("INSERT INTO subjects(name_ar, name_fr, sort_order) VALUES(?,?,?)", args)
    return redirect("/subjects", "تم الحفظ")


@route("/subjects/delete", "POST")
def subjects_delete(r):
    r.db.execute("DELETE FROM subjects WHERE id=?", (r.int("id"),))
    return redirect("/subjects", "تم حذف المادة")


# ---------------------------- الضوارب (حسب المرحلة) ----------------------------
@route("/coefficients")
def coef_page(r):
    subjects = r.db.execute("SELECT * FROM subjects ORDER BY sort_order, id").fetchall()
    stage = r.get("stage") if r.get("stage") in dict(STAGES) else "C1"
    classes = r.db.execute("SELECT name FROM classes WHERE stage=? ORDER BY name", (stage,)).fetchall()
    tabs = " ".join(f"<a class='btn{'' if code == stage else ' light'}' href='/coefficients?stage={code}'>{esc(label)}</a>"
                    for code, label in STAGES)
    cur = {x["subject_id"]: x["coef"] for x in
           r.db.execute("SELECT subject_id, coef FROM coefficients WHERE stage=?", (stage,))}
    trs = "".join(f"<tr><td>{esc(s['name_ar'])}</td><td dir='ltr' style='text-align:left'>{esc(s['name_fr'])}</td>"
                  f"<td><input class='num' name='c_{s['id']}' value='{fmt(cur[s['id']]) if s['id'] in cur else ''}'></td></tr>"
                  for s in subjects)
    names = "، ".join(c["name"] for c in classes) or "لا توجد فصول في هذه المرحلة بعد"
    body = f"""<div class="card">{tabs}<p class="muted" style="margin-bottom:0">فصول هذه المرحلة: {esc(names)}</p></div>"""
    if subjects:
        body += f"""<div class="card"><form method="post" action="/coefficients/save">
            <input type="hidden" name="stage" value="{stage}">
            <table><tr><th>المادة</th><th>Matière</th><th>الضارب</th></tr>{trs}</table>
            <p class="muted">اترك الضارب فارغاً (أو 0) إذا كانت المادة لا تُدرَّس في هذه المرحلة.</p>
            <button>حفظ ضوارب {esc(dict(STAGES)[stage])}</button></form></div>"""
    else:
        body += need_choice(subjects, "مواد")
    return r.page("جدول الضوارب", body)


@route("/coefficients/save", "POST")
def coef_save(r):
    stage = valid_stage(r.get("stage"))
    values = []
    for s in r.db.execute("SELECT id FROM subjects"):
        v = parse_num(r.get(f"c_{s['id']}"))
        if v is not None and v < 0:
            raise ValueError("الضارب لا يمكن أن يكون سالباً")
        values.append((s["id"], v))
    for sid, v in values:
        if v is None or v == 0:
            r.db.execute("DELETE FROM coefficients WHERE stage=? AND subject_id=?", (stage, sid))
        else:
            r.db.execute("""INSERT INTO coefficients(stage, subject_id, coef) VALUES(?,?,?)
                            ON CONFLICT(stage, subject_id) DO UPDATE SET coef=excluded.coef""", (stage, sid, v))
    return redirect(f"/coefficients?stage={stage}", "تم حفظ الضوارب")


# ---------------------------- الأساتذة ----------------------------
@route("/teachers")
def teachers_page(r):
    subjects = r.db.execute("SELECT id, name_ar AS name FROM subjects ORDER BY sort_order, id").fetchall()
    rows = r.db.execute("SELECT * FROM teachers ORDER BY name").fetchall()
    trs = "".join(f"""<tr><td><form method="post" action="/teachers/save" class="form-row">
        <input type="hidden" name="id" value="{t['id']}">
        <div><input name="name" value="{esc(t['name'])}" required></div>
        <div><select name="subject_id">{options(subjects, t['subject_id'], 'بدون مادة')}</select></div>
        <div><input name="phone" value="{esc(t['phone'])}" placeholder="الهاتف" dir="ltr"></div>
        <button class="light">حفظ</button>
        <button class="danger" formaction="/teachers/delete" onclick="return confirm('حذف الأستاذ؟')">حذف</button>
        </form></td></tr>""" for t in rows)
    body = f"""<div class="card"><form method="post" action="/teachers/save" class="form-row">
        <div><label>اسم الأستاذ</label><input name="name" required></div>
        <div><label>المادة</label><select name="subject_id">{options(subjects, None, 'بدون مادة')}</select></div>
        <div><label>الهاتف</label><input name="phone" dir="ltr"></div>
        <button>إضافة</button></form></div>
        <p><a class="btn light" target="_blank" href="/teachers/print">طباعة قائمة الأساتذة</a></p>
        <div class="card"><table><tr><th>الأستاذ — المادة — الهاتف</th></tr>
        {trs or "<tr><td class='muted'>لا يوجد أساتذة بعد</td></tr>"}</table></div>"""
    return r.page("جدول الأساتذة", body)


@route("/teachers/print")
def teachers_print(r):
    rows = r.db.execute("""
        SELECT t.name, t.phone, s.name_ar AS subject
        FROM teachers t LEFT JOIN subjects s ON s.id = t.subject_id
        ORDER BY t.name""").fetchall()
    school = r.settings.get("school_name_ar", "")
    year = r.settings.get("school_year", "")
    trs = "".join(
        f"<tr><td>{i}</td><td>{esc(t['name'])}</td>"
        f"<td>{esc(t['subject'] or '—')}</td>"
        f"<td dir='ltr'>{esc(t['phone'] or '—')}</td></tr>"
        for i, t in enumerate(rows, 1)
    )
    page = f"""<!DOCTYPE html><html lang="ar" dir="rtl"><head><meta charset="utf-8">
<title>قائمة الأساتذة</title>
<style>
body{{font-family:Tahoma,Arial,sans-serif;margin:16px;color:#222}}
h1{{font-size:18px;margin:0 0 2px}}
h2{{font-size:15px;margin:0 0 10px;font-weight:600}}
.meta{{color:#555;margin-bottom:14px;font-size:13px}}
table{{width:100%;border-collapse:collapse;font-size:13px}}
th,td{{padding:8px 10px;text-align:right;border:none}}
th{{background:#1f5fbf;color:#fff;font-weight:700}}
tbody tr:nth-child(even){{background:#f0f4fa}}
tbody tr:nth-child(odd){{background:#fff}}
@media print{{
  .toolbar{{display:none}}
  body{{margin:8mm}}
  tbody tr:nth-child(even){{background:#f0f4fa !important;-webkit-print-color-adjust:exact;print-color-adjust:exact}}
  th{{background:#1f5fbf !important;color:#fff !important;-webkit-print-color-adjust:exact;print-color-adjust:exact}}
}}
.toolbar{{margin-bottom:12px}}
.toolbar button{{font:inherit;padding:6px 14px;cursor:pointer;margin-left:8px}}
</style></head><body>
<div class="toolbar">
  <button onclick="window.print()">طباعة</button>
  <button onclick="window.close()">إغلاق</button>
</div>
<h1>{esc(school)}</h1>
<h2>قائمة الأساتذة</h2>
<div class="meta">السنة الدراسية: {esc(year)} — التاريخ: {today_fr()} — العدد: {len(rows)}</div>
<table>
<thead><tr>
  <th style="width:40px">#</th>
  <th>اسم الأستاذ</th>
  <th>المادة</th>
  <th>الهاتف</th>
</tr></thead>
<tbody>{trs or '<tr><td colspan="4">لا يوجد أساتذة</td></tr>'}</tbody>
</table>
</body></html>"""
    return ("html", page)


@route("/teachers/save", "POST")
def teachers_save(r):
    if not r.get("name"):
        raise ValueError("اسم الأستاذ مطلوب")
    args = (r.get("name"), r.get("phone"), r.int("subject_id"))
    if r.int("id"):
        r.db.execute("UPDATE teachers SET name=?, phone=?, subject_id=? WHERE id=?", args + (r.int("id"),))
    else:
        r.db.execute("INSERT INTO teachers(name, phone, subject_id) VALUES(?,?,?)", args)
    return redirect("/teachers", "تم الحفظ")


@route("/teachers/delete", "POST")
def teachers_delete(r):
    r.db.execute("DELETE FROM teachers WHERE id=?", (r.int("id"),))
    return redirect("/teachers", "تم حذف الأستاذ")


# ---------------------------- إدخال الدرجات ----------------------------
KIND_CHOICES = EXAMS + [("q", "معدل الاختبارات")]


@route("/grades")
def grades_page(r):
    """إدخال الدرجات مركّز على طالب واحد: يختار الفصل ثم الطالب ثم يُدخل درجات كل المواد."""
    classes = r.db.execute("SELECT * FROM classes ORDER BY name").fetchall()
    cid = r.int("class_id")
    stid = r.int("student_id")
    cls = get_class(r.db, cid)
    students = (r.db.execute("SELECT id, name FROM students WHERE class_id=? ORDER BY name", (cid,)).fetchall()
                if cls else [])
    subjects = (r.db.execute("""SELECT s.id, s.name_ar, s.name_fr, c.coef FROM subjects s
                                JOIN coefficients c ON c.subject_id=s.id
                                WHERE c.stage=? ORDER BY s.sort_order, s.id""", (cls["stage"],)).fetchall()
                if cls else [])

    sel = f"""<div class="card"><form method="get" class="form-row">
      <div><label>الفصل</label><select name="class_id" onchange="this.form.submit()">{options(classes, cid, 'اختر الفصل')}</select></div>
      <div><label>الطالب</label><select name="student_id" onchange="this.form.submit()">{options(students, stid, 'اختر الطالب')}</select></div>
      </form></div>"""

    table, hint = "", ""
    if cls and not subjects:
        hint = (f"<div class='warn'>لا توجد ضوارب للمرحلة {esc(cls['stage'])}. حدّدها من «جدول الضوارب» أولاً.</div>")

    if cls and stid:
        st = r.db.execute("SELECT * FROM students WHERE id=? AND class_id=?", (stid, cid)).fetchone()
        if st is None:
            return redirect(f"/grades?class_id={cid}", "الطالب غير موجود في هذا الفصل", ok=False)

        # جلب كل درجات هذا الطالب
        grades = {}
        for g in r.db.execute("SELECT * FROM grades WHERE student_id=?", (stid,)):
            grades.setdefault(g["subject_id"], {})[g["kind"]] = (g["score"], g["status"])

        # أزرار التنقل بين الطلاب
        ids = [s["id"] for s in students]
        idx = ids.index(stid) if stid in ids else -1
        prev_id = ids[idx - 1] if idx > 0 else None
        next_id = ids[idx + 1] if 0 <= idx < len(ids) - 1 else None
        nav = f"""<div class="form-row" style="margin-bottom:10px;align-items:center">
          <span class="badge">طالب {idx + 1} من {len(ids)}</span>
          {'<a class="btn light" href="/grades?class_id=%s&student_id=%s">← السابق</a>' % (cid, prev_id) if prev_id else '<span class="btn light" style="opacity:.4">← السابق</span>'}
          {'<a class="btn light" href="/grades?class_id=%s&student_id=%s">التالي →</a>' % (cid, next_id) if next_id else '<span class="btn light" style="opacity:.4">التالي →</span>'}
          <span style="margin-right:auto;font-weight:700">{esc(st['name'])} — {esc(cls['name'])}</span>
        </div>"""

        rows_html = []
        for sub in subjects:
            ent = grades.get(sub["id"], {})
            direct_q = ent["q"][0] if "q" in ent else None
            # صف لكل مادة: e1, e2, e3، ومعدل الاختبارات
            cells = []
            for kind, label in EXAMS:
                g = ent.get(kind)
                val = fmt(g[0]) if g and g[0] is not None else ""
                st_sel = options([(k, t) for k, t in STATUSES], g[1] if g else "")
                cells.append(
                    f"<td><input class='num' inputmode='decimal' autocomplete='off' "
                    f"name='s_{sub['id']}_{kind}' value='{val}' placeholder='درجة'></td>"
                    f"<td><select name='t_{sub['id']}_{kind}'>{st_sel}</select></td>"
                )
            # معدل الاختبارات: خانة واحدة فقط
            dq = fmt(direct_q) if direct_q is not None else ""
            cells.append(
                f"<td><input class='num' inputmode='decimal' autocomplete='off' name='d_{sub['id']}' "
                f"value='{dq}' placeholder='المعدل'></td>"
            )
            rows_html.append(
                f"<tr><td class='ar' style='font-weight:600'>{esc(sub['name_ar'])}</td>"
                f"<td dir='ltr' style='text-align:left;font-size:13px'>{esc(sub['name_fr'])}</td>"
                f"{''.join(cells)}</tr>"
            )

        exam_heads = "".join(
            f"<th colspan='2'>{esc(label)}<br><span class='muted' style='font-weight:400;font-size:12px'>درجة / حالة</span></th>"
            for _, label in EXAMS
        )
        table = f"""
        <style>
        .sticky-bar{{position:sticky;bottom:0;z-index:10;background:#1f5fbf;color:#fff;padding:12px 16px;
          display:flex;gap:12px;align-items:center;border-radius:10px 10px 0 0;margin-top:12px;
          box-shadow:0 -4px 16px #0002}}
        .sticky-bar button{{background:#fff;color:#1f5fbf;font-weight:700;padding:10px 28px;font-size:16px}}
        .sticky-bar button:hover{{background:#e8f0fe}}
        .sticky-bar .hint{{font-size:13px;opacity:.9}}
        #grades-form table input.num{{width:64px}}
        </style>
        <div class="card">
          {nav}
          <form method="post" action="/grades/save" id="grades-form">
            <input type="hidden" name="class_id" value="{cid}">
            <input type="hidden" name="student_id" value="{stid}">
            <table>
              <thead><tr>
                <th>المادة</th><th>Matière</th>
                {exam_heads}
                <th>معدل الاختبارات</th>
              </tr></thead>
              <tbody>
                {''.join(rows_html) or '<tr><td colspan="9" class="muted">لا توجد مواد لهذه المرحلة</td></tr>'}
              </tbody>
            </table>
            <p class="muted" style="margin-top:8px">
              إذا اخترت «غائب بدون عذر» حُسبت 0، و«غائب بعذر» حُسبت 10، ويُتجاهل الرقم المكتوب.
              الخانة الفارغة تعني أن الامتحان لم يُجرَ بعد.
              معدل الاختبارات: أدخل المعدل النهائي مرة واحدة لكل مادة.
            </p>
            <div class="sticky-bar">
              <button type="submit">حفظ درجات هذا الطالب</button>
              <span class="hint">يُحفظ كل ما أدخلته لهذا الطالب في كل المواد</span>
              {('<button type="submit" name="next_id" value="%s" style="margin-right:auto">حفظ والانتقال للتالي →</button>' % next_id) if next_id else ''}
            </div>
          </form>
        </div>"""

    return r.page("إدخال درجات الطلاب", need_choice(classes, "فصول") + sel + hint + table)


@route("/grades/save", "POST")
def grades_save(r):
    cid, stid = r.int("class_id"), r.int("student_id")
    if not get_class(r.db, cid):
        raise ValueError("الفصل غير موجود")
    st = r.db.execute("SELECT id, name FROM students WHERE id=? AND class_id=?", (stid, cid)).fetchone()
    if st is None:
        raise ValueError("الطالب غير موجود في هذا الفصل")
    subjects = r.db.execute("""SELECT s.id FROM subjects s JOIN coefficients c ON c.subject_id=s.id
                               JOIN classes cl ON cl.stage=c.stage WHERE cl.id=?""", (cid,)).fetchall()
    # التحقق أولاً ثم الحفظ
    plan = []  # list of (subject_id, kind, score, status) or for q: (subject_id, 'q', direct, quiz_list)
    for sub in subjects:
        sid = sub["id"]
        # الامتحانات الثلاثة
        for kind, _ in EXAMS:
            status = r.get(f"t_{sid}_{kind}")
            if status not in dict(STATUSES):
                raise ValueError(f"حالة غير صحيحة في مادة")
            try:
                score = parse_score(r.get(f"s_{sid}_{kind}"))
            except ValueError as e:
                raise ValueError(f"{st['name']}: {e}")
            plan.append(("exam", sid, kind, None if status else score, status))
        # معدل الاختبارات (خانة واحدة)
        try:
            direct = parse_score(r.get(f"d_{sid}"))
        except ValueError as e:
            raise ValueError(f"{st['name']}: {e}")
        plan.append(("q", sid, direct))

    for item in plan:
        if item[0] == "exam":
            _, sid, kind, score, status = item
            if score is None and not status:
                r.db.execute("DELETE FROM grades WHERE student_id=? AND subject_id=? AND kind=?", (stid, sid, kind))
            else:
                r.db.execute("""INSERT INTO grades(student_id, subject_id, kind, score, status) VALUES(?,?,?,?,?)
                    ON CONFLICT(student_id, subject_id, kind) DO UPDATE SET score=excluded.score, status=excluded.status""",
                             (stid, sid, kind, score, status))
        else:
            _, sid, direct = item
            # نمسح الاختبارات الصغيرة القديمة إن وُجدت ونعتمد المعدل المباشر فقط
            r.db.execute("DELETE FROM quizzes WHERE student_id=? AND subject_id=?", (stid, sid))
            if direct is None:
                r.db.execute("DELETE FROM grades WHERE student_id=? AND subject_id=? AND kind='q'", (stid, sid))
            else:
                r.db.execute("""INSERT INTO grades(student_id, subject_id, kind, score, status) VALUES(?,?,?,?,?)
                    ON CONFLICT(student_id, subject_id, kind) DO UPDATE SET score=excluded.score, status=excluded.status""",
                             (stid, sid, "q", direct, ""))

    # الانتقال للطالب التالي إن وُجد زر «حفظ والانتقال»
    next_id = r.int("next_id")
    if next_id:
        return redirect(f"/grades?class_id={cid}&student_id={next_id}", "تم الحفظ — انتقلت للطالب التالي")
    return redirect(f"/grades?class_id={cid}&student_id={stid}", "تم حفظ درجات الطالب")


# ---------------------------- الغياب (بالساعات) ----------------------------
@route("/absences")
def absences_page(r):
    classes = r.db.execute("SELECT * FROM classes ORDER BY name").fetchall()
    cid = r.int("class_id")
    day = r.get("day") or today()
    sel = f"""<div class="card"><form method="get" class="form-row">
      <div><label>الفصل</label><select name="class_id" onchange="this.form.submit()">{options(classes, cid, 'اختر الفصل')}</select></div>
      <div><label>التاريخ</label><input type="date" name="day" value="{esc(day)}" onchange="this.form.submit()" dir="ltr"></div>
      </form></div>"""
    body = ""
    if cid:
        studs = r.db.execute("SELECT * FROM students WHERE class_id=? ORDER BY name", (cid,)).fetchall()
        cur = {a["student_id"]: a["hours"] for a in r.db.execute(
            "SELECT a.student_id, a.hours FROM absences a JOIN students s ON s.id=a.student_id "
            "WHERE a.day=? AND s.class_id=?", (day, cid))}
        trs = "".join(f"<tr><td>{i}</td><td>{esc(s['name'])}</td><td><input class='num' inputmode='decimal' "
                      f"name='h_{s['id']}' value='{fmt(cur[s['id']]) if s['id'] in cur else ''}' autocomplete='off'></td></tr>"
                      for i, s in enumerate(studs, 1))
        totals = r.db.execute("""SELECT s.name, COALESCE(SUM(a.hours), 0) t
              FROM students s LEFT JOIN absences a ON a.student_id=s.id
              WHERE s.class_id=? GROUP BY s.id ORDER BY s.name""", (cid,)).fetchall()
        ttr = "".join(f"<tr><td>{esc(t['name'])}</td><td class='stat'>{fmt(t['t'] or 0)}</td></tr>" for t in totals)
        # تقارير الغياب
        report = f"""<div class="card"><b>تقارير الغياب</b>
          <form method="get" action="/absences/report" target="_blank" class="form-row" style="margin-top:10px">
            <input type="hidden" name="class_id" value="{cid}">
            <div><label>من تاريخ</label><input type="date" name="from" value="{esc(day)}" dir="ltr" required></div>
            <div><label>إلى تاريخ</label><input type="date" name="to" value="{esc(today())}" dir="ltr" required></div>
            <div><label>الطالب</label>
              <select name="student_id">
                <option value="">كل الفصل</option>
                {options(studs, None)}
              </select>
            </div>
            <button class="light">عرض / طباعة التقرير</button>
          </form>
          <p class="muted">اختر «كل الفصل» لتقرير جماعي، أو طالباً معيّناً لتقرير تفصيلي بأيام الغياب وساعاته.</p>
        </div>"""
        body = f"""<div class="card"><form method="post" action="/absences/save">
          <input type="hidden" name="class_id" value="{cid}">
          <input type="hidden" name="day" value="{esc(day)}">
          <p><b>ساعات الغياب يوم {esc(day)}</b></p>
          <table><tr><th style="width:44px">#</th><th>الطالب</th><th>عدد ساعات الغياب</th></tr>
          {trs or "<tr><td colspan=3 class='muted'>لا يوجد طلاب</td></tr>"}</table>
          <p class="muted">اترك الخانة فارغة (أو 0) للحاضر. تُحفظ ساعات هذا اليوم فقط. الغياب يُسجَّل عن الحصص وليس مرتبطاً بامتحان معيّن.</p>
          <button>حفظ</button></form></div>
          {report}
          <div class="card"><b>مجموع ساعات الغياب (كل الأيام)</b><br><br>
          <table><tr><th>الطالب</th><th>المجموع</th></tr>{ttr}</table></div>"""
    return r.page("تسجيل الغياب", need_choice(classes, "فصول") + sel + body)


@route("/absences/save", "POST")
def absences_save(r):
    cid, day = r.int("class_id"), r.get("day")
    try:
        date.fromisoformat(day)
    except ValueError:
        raise ValueError("التاريخ غير صحيح")
    if not get_class(r.db, cid):
        raise ValueError("بيانات غير مكتملة")
    studs = r.db.execute("SELECT id, name FROM students WHERE class_id=?", (cid,)).fetchall()
    plan = {}
    for s in studs:
        v = parse_num(r.get(f"h_{s['id']}"))
        if v is not None and not 0 <= v <= 24:
            raise ValueError(f"{s['name']}: عدد الساعات يجب أن يكون بين 0 و 24")
        plan[s["id"]] = v
    for stid, v in plan.items():
        r.db.execute("DELETE FROM absences WHERE student_id=? AND day=?", (stid, day))
        if v:
            r.db.execute("INSERT INTO absences(student_id, day, hours) VALUES(?,?,?)", (stid, day, v))
    return redirect("/absences?" + urlencode({"class_id": cid, "day": day}), "تم حفظ الغياب")


@route("/absences/report")
def absences_report(r):
    cid = r.int("class_id")
    stid = r.int("student_id")
    dfrom, dto = r.get("from"), r.get("to")
    cls = get_class(r.db, cid)
    if not cls:
        return redirect("/absences", "الفصل غير موجود", ok=False)
    try:
        date.fromisoformat(dfrom)
        date.fromisoformat(dto)
    except ValueError:
        return redirect("/absences?" + urlencode({"class_id": cid}), "تاريخ غير صحيح", ok=False)
    if dfrom > dto:
        dfrom, dto = dto, dfrom
    school = r.settings.get("school_name_ar", "")
    year = r.settings.get("school_year", "")
    period = f"من {dfrom} إلى {dto}"

    if stid:
        # تقرير طالب واحد — تفصيلي
        st = r.db.execute("SELECT * FROM students WHERE id=? AND class_id=?", (stid, cid)).fetchone()
        if not st:
            return redirect("/absences?" + urlencode({"class_id": cid}), "الطالب غير موجود", ok=False)
        rows = r.db.execute("""SELECT day, hours FROM absences
                               WHERE student_id=? AND day BETWEEN ? AND ? ORDER BY day""",
                            (stid, dfrom, dto)).fetchall()
        total = sum(a["hours"] for a in rows)
        trs = "".join(
            f"<tr><td>{i}</td><td dir='ltr'>{esc(a['day'])}</td><td>{fmt(a['hours'])}</td></tr>"
            for i, a in enumerate(rows, 1)
        )
        page = f"""<!DOCTYPE html><html lang="ar" dir="rtl"><head><meta charset="utf-8">
<title>تقرير غياب — {esc(st['name'])}</title>
<style>
body{{font-family:Tahoma,Arial,sans-serif;margin:16px;color:#222}}
h1{{font-size:18px;margin:0 0 2px}}
h2{{font-size:15px;margin:0 0 10px;font-weight:600}}
.meta{{color:#555;margin-bottom:8px;font-size:13px}}
.info{{margin-bottom:14px;font-size:14px;line-height:1.7}}
.info b{{display:inline-block;min-width:110px}}
table{{width:100%;border-collapse:collapse;font-size:13px;margin-top:8px}}
th,td{{padding:8px 10px;text-align:right;border:none}}
th{{background:#1f5fbf;color:#fff;font-weight:700}}
tbody tr:nth-child(even){{background:#f0f4fa}}
tbody tr:nth-child(odd){{background:#fff}}
.total{{font-weight:700;font-size:14px;margin-top:12px}}
@media print{{
  .toolbar{{display:none}} body{{margin:8mm}}
  tbody tr:nth-child(even){{background:#f0f4fa !important;-webkit-print-color-adjust:exact;print-color-adjust:exact}}
  th{{background:#1f5fbf !important;color:#fff !important;-webkit-print-color-adjust:exact;print-color-adjust:exact}}
}}
.toolbar{{margin-bottom:12px}}
.toolbar button{{font:inherit;padding:6px 14px;cursor:pointer;margin-left:8px}}
</style></head><body>
<div class="toolbar">
  <button onclick="window.print()">طباعة</button>
  <button onclick="window.close()">إغلاق</button>
</div>
<h1>{esc(school)}</h1>
<h2>تقرير غياب طالب</h2>
<div class="meta">الفصل: {esc(cls['name'])} — السنة الدراسية: {esc(year)} — فترة الاستعلام: {esc(period)}</div>
<div class="info">
  <div><b>الاسم:</b> {esc(st['name'])}</div>
  <div><b>الرقم الوطني:</b> <span dir="ltr">{esc(st['nni'])}</span></div>
  <div><b>الرقم المدرسي:</b> <span dir="ltr">{esc(st['school_no'])}</span></div>
</div>
<table>
<thead><tr><th style="width:40px">#</th><th>تاريخ الغياب</th><th>عدد الساعات</th></tr></thead>
<tbody>{trs or '<tr><td colspan="3">لا يوجد غياب في هذه الفترة</td></tr>'}</tbody>
</table>
<div class="total">مجموع ساعات الغياب في الفترة: {fmt(total)} ساعة</div>
</body></html>"""
        return ("html", page)

    # تقرير الفصل كاملاً
    studs = r.db.execute("SELECT * FROM students WHERE class_id=? ORDER BY name", (cid,)).fetchall()
    abs_rows = r.db.execute("""SELECT a.student_id, a.day, a.hours FROM absences a
                               JOIN students s ON s.id=a.student_id
                               WHERE s.class_id=? AND a.day BETWEEN ? AND ?
                               ORDER BY s.name, a.day""", (cid, dfrom, dto)).fetchall()
    by_student = {}
    for a in abs_rows:
        by_student.setdefault(a["student_id"], []).append(a)

    blocks = []
    for i, st in enumerate(studs, 1):
        days = by_student.get(st["id"], [])
        total = sum(a["hours"] for a in days)
        if not days:
            detail = "<tr><td colspan='2' class='muted'>لا يوجد غياب</td></tr>"
        else:
            detail = "".join(
                f"<tr><td dir='ltr'>{esc(a['day'])}</td><td>{fmt(a['hours'])}</td></tr>"
                for a in days
            )
        blocks.append(f"""
<div class="stu">
  <div class="stu-h">
    <span class="n">{i}. {esc(st['name'])}</span>
    <span dir="ltr">وطني: {esc(st['nni'])}</span>
    <span dir="ltr">مدرسي: {esc(st['school_no'])}</span>
    <span class="tot">المجموع: {fmt(total)} ساعة</span>
  </div>
  <table class="inner">
    <thead><tr><th>تاريخ الغياب</th><th>الساعات</th></tr></thead>
    <tbody>{detail}</tbody>
  </table>
</div>""")

    page = f"""<!DOCTYPE html><html lang="ar" dir="rtl"><head><meta charset="utf-8">
<title>تقرير غياب الفصل {esc(cls['name'])}</title>
<style>
body{{font-family:Tahoma,Arial,sans-serif;margin:16px;color:#222}}
h1{{font-size:18px;margin:0 0 2px}}
h2{{font-size:15px;margin:0 0 10px;font-weight:600}}
.meta{{color:#555;margin-bottom:14px;font-size:13px}}
.stu{{margin-bottom:16px;border:1px solid #d9dee7;border-radius:8px;overflow:hidden}}
.stu-h{{background:#eef2f8;padding:8px 12px;display:flex;flex-wrap:wrap;gap:14px;align-items:center;font-size:13px}}
.stu-h .n{{font-weight:700;font-size:14px}}
.stu-h .tot{{font-weight:700;margin-right:auto}}
table.inner{{width:100%;border-collapse:collapse;font-size:13px}}
table.inner th,table.inner td{{padding:6px 10px;text-align:right;border:none}}
table.inner th{{background:#f5f7fb;font-weight:600}}
table.inner tr:nth-child(even) td{{background:#fafbfd}}
.muted{{color:#888}}
@media print{{
  .toolbar{{display:none}} body{{margin:8mm}}
  .stu{{break-inside:avoid}}
}}
.toolbar{{margin-bottom:12px}}
.toolbar button{{font:inherit;padding:6px 14px;cursor:pointer;margin-left:8px}}
</style></head><body>
<div class="toolbar">
  <button onclick="window.print()">طباعة</button>
  <button onclick="window.close()">إغلاق</button>
</div>
<h1>{esc(school)}</h1>
<h2>تقرير غياب الفصل: {esc(cls['name'])}</h2>
<div class="meta">السنة الدراسية: {esc(year)} — فترة الاستعلام: {esc(period)} — عدد الطلاب: {len(studs)} — التاريخ: {today_fr()}</div>
{''.join(blocks) or '<p>لا يوجد طلاب في هذا الفصل</p>'}
</body></html>"""
    return ("html", page)


# ---------------------------- كشوف الدرجات ----------------------------
@route("/transcripts")
def transcripts_page(r):
    classes = r.db.execute("SELECT * FROM classes ORDER BY name").fetchall()
    cid = r.int("class_id")
    exam = r.get("exam") if r.get("exam") in dict(EXAMS) else "e3"
    list_btn = ""
    if cid:
        list_btn = (f"<div><label>&nbsp;</label>"
                    f"<a class='btn light' target='_blank' "
                    f"href='/transcripts/list?class_id={cid}&exam={exam}'>طباعة قائمة النتائج</a></div>")
    sel = f"""<div class="card"><form method="get" class="form-row">
      <div><label>الفصل</label><select name="class_id" onchange="this.form.submit()">{options(classes, cid, 'اختر الفصل')}</select></div>
      <div><label>الكشف</label><select name="exam" onchange="this.form.submit()">{options(EXAMS, exam)}</select></div>
      {list_btn}
      </form></div>"""
    body = ""
    if cid:
        data = class_results(r.db, cid, EXAM_LEVEL[exam])
        warn = ""
        if not data["subjects"]:
            warn = f"<div class='warn'>لا توجد ضوارب للمرحلة {esc(data['class']['stage'])}. حدّدها من «جدول الضوارب» أولاً.</div>"
        final = exam == "e3"
        trs = ""
        for x in sorted(data["results"], key=lambda x: (x["rank"] is None, x["rank"] or 0, x["student"]["name"])):
            st = x["student"]
            avg_cls = " low" if x["avg"] is not None and x["avg"] < 10 else ""
            miss = f"<span class='badge'>ناقص {x['missing']}</span>" if x["missing"] else ""
            decision = ""
            if final:
                decision = (f"<td><select name='dec_{st['id']}'>{options(DECISIONS, st['decision'])}</select></td>"
                            f"<td><input name='note_{st['id']}' value='{esc(st['director_note'])}' maxlength='200'></td>")
            trs += (f"<tr><td>{esc(st['name'])}</td><td class='stat{avg_cls}'>{f2(x['avg'])}</td><td>{x['rank'] or ''}</td>"
                    f"<td>{fmt(x['hours']) or 0}</td><td>{miss}</td>{decision}"
                    f"<td class='actions'><a class='btn light' target='_blank' "
                    f"href='/transcript/print?student_id={st['id']}&exam={exam}'>عرض / طباعة</a></td></tr>")
        extra_h = "<th>القرار</th><th>ملاحظة المدير</th>" if final else ""
        cols = 8 if final else 6
        table = (f"<table><tr><th>الطالب</th><th>المعدل</th><th>الرتبة</th><th>ساعات الغياب</th><th>خانات ناقصة</th>"
                 f"{extra_h}<th></th></tr>{trs or f'<tr><td colspan={cols} class=muted>لا يوجد طلاب</td></tr>'}</table>")
        if final and data["results"]:
            table = (f"<form method='post' action='/transcripts/decisions'><input type='hidden' name='class_id' value='{cid}'>"
                     f"{table}<br><button>حفظ القرارات والملاحظات</button></form>")
        body = (f"{warn}<div class='card'><a class='btn' target='_blank' href='/transcript/print?class_id={cid}&exam={exam}'>"
                f"طباعة كشوف الفصل كاملة (صفحة لكل طالب)</a><br><br>{table}</div>")
    return r.page("كشوف الدرجات", need_choice(classes, "فصول") + sel + body)


@route("/transcripts/list")
def transcripts_list(r):
    """طباعة قائمة نتائج الفصل: الاسم، الرقم الوطني، الرقم المدرسي، المعدل، الترتيب."""
    cid = r.int("class_id")
    exam = r.get("exam") if r.get("exam") in dict(EXAMS) else "e3"
    cls = get_class(r.db, cid)
    if not cls:
        return redirect("/transcripts", "الفصل غير موجود", ok=False)
    data = class_results(r.db, cid, EXAM_LEVEL[exam])
    exam_name = dict(EXAMS)[exam]
    title = f"قائمة الفصل {cls['name']} — نتائج {exam_name}"
    school = r.settings.get("school_name_ar", "")
    year = r.settings.get("school_year", "")
    rows = sorted(data["results"], key=lambda x: (x["rank"] is None, x["rank"] or 0, x["student"]["name"]))
    trs = "".join(
        f"<tr><td>{i}</td><td>{esc(x['student']['name'])}</td>"
        f"<td dir='ltr'>{esc(x['student']['nni'])}</td>"
        f"<td dir='ltr'>{esc(x['student']['school_no'])}</td>"
        f"<td class='avg'>{f2(x['avg'])}</td>"
        f"<td>{x['rank'] or '—'}</td></tr>"
        for i, x in enumerate(rows, 1)
    )
    page = f"""<!DOCTYPE html><html lang="ar" dir="rtl"><head><meta charset="utf-8">
<title>{esc(title)}</title>
<style>
body{{font-family:Tahoma,Arial,sans-serif;margin:16px;color:#222}}
h1{{font-size:18px;margin:0 0 2px}}
h2{{font-size:15px;margin:0 0 10px;font-weight:600}}
.meta{{color:#555;margin-bottom:14px;font-size:13px}}
table{{width:100%;border-collapse:collapse;font-size:13px}}
th,td{{padding:8px 10px;text-align:right;border:none}}
th{{background:#1f5fbf;color:#fff;font-weight:700}}
tbody tr:nth-child(even){{background:#f0f4fa}}
tbody tr:nth-child(odd){{background:#fff}}
td.avg{{font-weight:700}}
@media print{{
  .toolbar{{display:none}}
  body{{margin:8mm}}
  tbody tr:nth-child(even){{background:#f0f4fa !important;-webkit-print-color-adjust:exact;print-color-adjust:exact}}
  th{{background:#1f5fbf !important;color:#fff !important;-webkit-print-color-adjust:exact;print-color-adjust:exact}}
}}
.toolbar{{margin-bottom:12px}}
.toolbar button{{font:inherit;padding:6px 14px;cursor:pointer;margin-left:8px}}
</style></head><body>
<div class="toolbar">
  <button onclick="window.print()">طباعة</button>
  <button onclick="window.close()">إغلاق</button>
</div>
<h1>{esc(school)}</h1>
<h2>{esc(title)}</h2>
<div class="meta">السنة الدراسية: {esc(year)} — التاريخ: {today_fr()} — عدد الطلاب: {len(rows)}</div>
<table>
<thead><tr>
  <th style="width:40px">#</th>
  <th>الاسم</th>
  <th>الرقم الوطني</th>
  <th>الرقم المدرسي</th>
  <th>النتيجة</th>
  <th>الترتيب</th>
</tr></thead>
<tbody>{trs or '<tr><td colspan="6">لا يوجد طلاب</td></tr>'}</tbody>
</table>
</body></html>"""
    return ("html", page)


@route("/transcripts/decisions", "POST")
def transcripts_decisions(r):
    cid = r.int("class_id")
    if not get_class(r.db, cid):
        raise ValueError("الفصل غير موجود")
    for s in r.db.execute("SELECT id FROM students WHERE class_id=?", (cid,)).fetchall():
        dec = r.get(f"dec_{s['id']}")
        if dec not in dict(DECISIONS):
            raise ValueError("قرار غير صحيح")
        r.db.execute("UPDATE students SET decision=?, director_note=? WHERE id=?",
                     (dec, r.get(f"note_{s['id']}")[:200], s["id"]))
    return redirect(f"/transcripts?class_id={cid}&exam=e3", "تم حفظ القرارات")


@route("/transcript/print")
def transcript_print(r):
    exam = r.get("exam")
    if exam not in dict(EXAMS):
        return redirect("/transcripts", "الكشف غير صحيح", ok=False)
    sid, cid = r.int("student_id"), r.int("class_id")
    if sid:
        row = r.db.execute("SELECT class_id FROM students WHERE id=?", (sid,)).fetchone()
        if row is None:
            return redirect("/transcripts", "الطالب غير موجود", ok=False)
        cid = row["class_id"]
    if not get_class(r.db, cid):
        return redirect("/transcripts", "الفصل غير موجود", ok=False)
    data = class_results(r.db, cid, EXAM_LEVEL[exam])
    chosen = [x for x in data["results"] if not sid or x["student"]["id"] == sid]
    sheets = "".join(sheet_html(x, data["class"], exam, r.settings) for x in chosen)
    if not sheets:
        return redirect("/transcripts", "لا يوجد طلاب", ok=False)
    page = (f"<!DOCTYPE html><html lang='ar' dir='rtl'><head><meta charset='utf-8'><title>كشف الدرجات</title>"
            f"<style>{SHEET_CSS}</style></head><body><div class='toolbar'>"
            f"<button onclick='window.print()'>طباعة</button>"
            f"<button onclick='window.close()'>إغلاق</button>"
            f"<span class='toolbar-note'>الحجم A4 أفقي. اختر «حفظ كـ PDF» من نافذة الطباعة إن أردت ملفاً.</span></div>"
            f"{sheets}<script>{SHEET_JS}</script></body></html>")
    return ("html", page)


# ---------------------------- الإعدادات ----------------------------
@route("/settings")
def settings_page(r):
    s = r.settings
    groups = [("الدولة والوزارة", HEADER_FIELDS[0:10]), ("المؤسسة", HEADER_FIELDS[10:15]),
              ("التواصل والسنة الدراسية", HEADER_FIELDS[15:])]
    fields = ""
    for title, items in groups:
        inner = "".join(f"<div><label>{lbl}</label><input name='{k}' value='{esc(s[k])}' dir='{d}'></div>"
                        for k, lbl, _, d in items)
        fields += f"<fieldset><legend>{title}</legend><div class='cols2'>{inner}</div></fieldset>"
    logo_now = (f"<img class='logo-prev' src='{esc(s['logo'])}' alt=''> "
                f"<label style='font-weight:400'><input type='checkbox' name='remove_logo' value='1'> حذف الشعار</label>"
                if s["logo"] else "<span class='muted'>لا يوجد شعار</span>")
    demo = ""
    if db_is_empty(r.db):
        demo = """<div class="card"><b>بيانات تجريبية</b><p class="muted">لتجربة البرنامج بسرعة (تعمل فقط والقاعدة فارغة).</p>
          <form method="post" action="/demo"><button class="light">تحميل بيانات تجريبية</button></form></div>"""
    return r.page("الإعدادات", f"""
      <div class="card"><form method="post" action="/settings/save" enctype="multipart/form-data">
        {fields}
        <fieldset><legend>شعار المؤسسة</legend>{logo_now}<br><br>
          <input type="file" name="logo" accept="image/*"></fieldset>
        <button>حفظ الإعدادات</button></form></div>
      <div class="card"><b>تغيير كلمة المرور</b><br><br><form method="post" action="/settings/password" class="form-row">
        <div><label>الحالية</label><input type="password" name="old" required></div>
        <div><label>الجديدة</label><input type="password" name="new" required minlength="4"></div>
        <div><label>تأكيد الجديدة</label><input type="password" name="new2" required></div>
        <button>تغيير</button></form></div>{demo}""")


@route("/settings/save", "POST")
def settings_save(r):
    logo = image_data_uri(r.files.get("logo", ("", b""))[1], 1_000_000)
    for k, _, _, _ in HEADER_FIELDS:
        r.db.execute("UPDATE settings SET value=? WHERE key=?", (r.get(k), k))
    if logo:
        r.db.execute("UPDATE settings SET value=? WHERE key='logo'", (logo,))
    elif r.get("remove_logo") == "1":
        r.db.execute("UPDATE settings SET value='' WHERE key='logo'")
    return redirect("/settings", "تم حفظ الإعدادات")


@route("/settings/password", "POST")
def settings_password(r):
    old, new, new2 = (r.params.get(k, [""])[0] for k in ("old", "new", "new2"))
    if not check_password(r.db, r.user, old):
        raise ValueError("كلمة المرور الحالية غير صحيحة")
    if len(new) < 4 or new != new2:
        raise ValueError("كلمة المرور الجديدة قصيرة (4 أحرف على الأقل) أو غير متطابقة")
    set_password(r.db, r.user, new)
    return redirect("/settings", "تم تغيير كلمة المرور")


@route("/demo", "POST")
def demo_load(r):
    if not db_is_empty(r.db):
        raise ValueError("توجد بيانات مسبقاً")
    load_demo(r.db)
    return redirect("/settings", "تم تحميل البيانات التجريبية")


def db_is_empty(db):
    return all(db.execute(f"SELECT COUNT(*) FROM {t}").fetchone()[0] == 0
               for t in ("students", "classes", "subjects", "teachers"))


def load_demo(db):
    rnd = random.Random(7)
    # (عربي، فرنسي، ضارب C1، ضارب C2)
    subs = [("التربية الإسلامية", "Education Islamique", 3, 3), ("اللغة العربية", "Arabe", 5, 5),
            ("التاريخ والجغرافيا", "Histoire-Géographie", 2, 2), ("التربية المدنية", "Instruction Civique", 1, 1),
            ("اللغة الفرنسية", "Français", 4, 4), ("اللغة الإنجليزية", "Anglais", 1, 2),
            ("الرياضيات / المعلوماتية", "Maths / Informatique", 5, 5), ("العلوم الطبيعية", "Sciences Naturelles", 2, 2),
            ("الفيزياء والكيمياء", "Physique-Chimie", 0, 3)]
    ids = []
    for order, (ar, fr, c1, c2) in enumerate(subs, 1):
        sid = db.execute("INSERT INTO subjects(name_ar, name_fr, sort_order) VALUES(?,?,?)", (ar, fr, order)).lastrowid
        ids.append(sid)
        if c1:
            db.execute("INSERT INTO coefficients VALUES('C1',?,?)", (sid, c1))
        if c2:
            db.execute("INSERT INTO coefficients VALUES('C2',?,?)", (sid, c2))
        db.execute("INSERT INTO teachers(name, phone, subject_id) VALUES(?,?,?)",
                   (f"الأستاذ {rnd.choice(['محمد', 'أحمد', 'سيدي', 'الشيخ', 'عبد الله'])} "
                    f"{rnd.choice(['ولد أحمد', 'ولد سيدي', 'ولد محمد'])}", "", sid))
    first = ["أحمد", "محمد", "فاطمة", "مريم", "عبد الله", "خديجة", "سيدي", "عائشة", "الشيخ", "زينب", "يحيى", "آمنة"]
    last = ["ولد أحمد", "بنت المختار", "ولد سيدي", "منت اباه", "ولد محمد", "بنت أحمد"]
    for cname, stage in (("1AS1", "C1"), ("2AS1", "C1"), ("3AS1", "C2")):
        cid = db.execute("INSERT INTO classes(name, stage) VALUES(?,?)", (cname, stage)).lastrowid
        taught = [sid for sid, s in zip(ids, subs) if (s[2] if stage == "C1" else s[3])]
        for i in range(12):
            sid = db.execute("""INSERT INTO students(name, class_id, nni, school_no, sex, birth_date, birth_place)
                VALUES(?,?,?,?,?,?,?)""", (f"{first[i % len(first)]} {rnd.choice(last)}", cid,
                                          f"NNI{rnd.randint(1000000, 9999999)}", f"{cid}{i + 1:03d}",
                                          "أنثى" if i % 2 else "ذكر", f"{2011 + (i % 3)}-0{1 + i % 9}-1{i % 9}",
                                          "نواكشوط")).lastrowid
            for sub in taught:
                for kind in ("e1", "e2", "e3"):
                    roll = rnd.random()
                    if roll < 0.03:
                        db.execute("INSERT INTO grades VALUES(?,?,?,NULL,'abs')", (sid, sub, kind))
                    elif roll < 0.06:
                        db.execute("INSERT INTO grades VALUES(?,?,?,NULL,'exc')", (sid, sub, kind))
                    else:
                        db.execute("INSERT INTO grades VALUES(?,?,?,?,'')",
                                   (sid, sub, kind, rnd.randint(6, 19) + rnd.choice([0, 0, 0.25, 0.5, 0.75])))
                if rnd.random() < 0.5:
                    db.execute("INSERT INTO grades VALUES(?,?,'q',?,'')", (sid, sub, rnd.randint(8, 18) + rnd.choice([0, 0.5])))
                else:
                    for j in range(1, 4):
                        db.execute("INSERT INTO quizzes VALUES(?,?,?,?)", (sid, sub, j, rnd.randint(7, 19)))
            for day in ("2025-10-14", "2026-01-12", "2026-04-20"):
                if rnd.random() < 0.5:
                    db.execute("INSERT INTO absences VALUES(?,?,?)", (sid, day, rnd.randint(1, 4)))


# ======================================================================
#                              الخادم
# ======================================================================
class Handler(BaseHTTPRequestHandler):
    server_version = "School/2.0"

    def log_message(self, *a):
        pass

    def _cookie(self):
        for part in (self.headers.get("Cookie") or "").split(";"):
            k, _, v = part.strip().partition("=")
            if k == "sid":
                return v
        return ""

    def _send(self, status, body=b"", ctype="text/html; charset=utf-8", headers=()):
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Frame-Options", "DENY")
        for k, v in headers:
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def _redirect(self, url, headers=()):
        self._send(303, b"", headers=[("Location", url)] + list(headers))

    def _read_params(self, method, parsed):
        params = parse_qs(parsed.query, keep_blank_values=True)
        files = {}
        if method == "POST":
            n = int(self.headers.get("Content-Length") or 0)
            ctype = self.headers.get("Content-Type") or ""
            limit = 4_000_000 if ctype.startswith("multipart/form-data") else 2_000_000
            if n > limit:
                raise ValueError("حجم الطلب كبير جداً")
            raw = self.rfile.read(n)
            if ctype.startswith("multipart/form-data"):
                fields, files = parse_multipart(ctype, raw)
            else:
                fields = parse_qs(raw.decode("utf-8", "replace"), keep_blank_values=True)
            params.update(fields)
        return params, files

    def _dispatch(self, method):
        parsed = urlparse(self.path)
        entry = ROUTES.get((method, parsed.path))
        if entry is None:
            return self._send(404, layout("غير موجود", "<a href='/'>القائمة الرئيسية</a>", show_nav=False).encode())
        fn, public = entry
        token = self._cookie()
        user = SESSIONS.get(token)
        if not public and not user:
            return self._redirect("/login")
        if method == "POST":       # حماية إضافية: الطلب يجب أن يأتي من نفس الموقع
            origin = self.headers.get("Origin")
            if origin and urlparse(origin).netloc != self.headers.get("Host"):
                return self._send(403, "مرفوض".encode())
        db = connect()
        try:
            try:
                params, files = self._read_params(method, parsed)
                result = fn(Req(db, params, user, files))
                db.commit()
            except (ValueError, sqlite3.IntegrityError) as e:       # أخطاء متوقعة من المستخدم
                db.rollback()
                if isinstance(e, sqlite3.IntegrityError):
                    e = ValueError("القيمة مكررة أو مرتبطة ببيانات أخرى")
                ref = urlparse(self.headers.get("Referer") or "/")
                back = ref.path + ("?" + ref.query if ref.query else "")
                if ref.path in ("/login", ""):
                    back = "/"
                result = redirect(back or "/", str(e), ok=False)
            except Exception:                                        # خطأ غير متوقع
                db.rollback()
                import traceback
                traceback.print_exc()
                page = layout("خطأ في البرنامج", "<div class='msg err'>حدث خطأ داخلي. تفاصيله ظاهرة في نافذة "
                              "الأوامر التي يعمل فيها البرنامج؛ أرسلها للمطوّر.</div><a class='btn' href='/'>"
                              "القائمة الرئيسية</a>", show_nav=False)
                return self._send(500, page.encode("utf-8"))
        finally:
            db.close()
        if result[0] == "html":
            self._send(200, result[1].encode("utf-8"))
        elif result[0] == "file":
            self._send(200, result[1], result[2],
                       [("Content-Disposition", f'attachment; filename="{result[3]}"')])
        else:
            headers = []
            if len(result) > 2:                   # تسجيل دخول/خروج
                if result[2]:
                    headers.append(("Set-Cookie", f"sid={result[2]}; HttpOnly; SameSite=Strict; Path=/"))
                else:
                    SESSIONS.pop(token, None)
                    headers.append(("Set-Cookie", "sid=; Max-Age=0; HttpOnly; SameSite=Strict; Path=/"))
            self._redirect(result[1], headers)

    def do_GET(self):
        self._dispatch("GET")

    def do_POST(self):
        self._dispatch("POST")


def make_server(port=PORT):
    for p in range(port, port + 20):
        try:
            return ThreadingHTTPServer((HOST, p), Handler)
        except OSError:
            continue
    raise SystemExit("تعذر فتح منفذ للبرنامج")


def main():
    init_db()
    if "--demo" in sys.argv:
        db = connect()
        if db_is_empty(db):
            load_demo(db)
            db.commit()
        db.close()
    server = make_server()
    url = f"http://{HOST}:{server.server_address[1]}"
    print(f"البرنامج يعمل على {url}   (للإيقاف: Ctrl+C)")
    threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nتم إيقاف البرنامج")


if __name__ == "__main__":
    main()