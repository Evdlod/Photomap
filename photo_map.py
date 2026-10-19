import argparse
import json
import os
import random
import re
import shutil
import sqlite3
import sys
import time
from collections import defaultdict, namedtuple
from datetime import datetime, timedelta

from PIL import Image, ImageFile, ImageOps

# Внимание: отключение лимита разрешено для доверенных панорам, но повышает
# риск чрезмерного расхода памяти на повреждённых/вредоносных файлах.
Image.MAX_IMAGE_PIXELS = None
# Битой папке архива лучше миниатюра с серой заливкой в повреждённом месте,
# чем полностью пропущенный снимок: включаем дозагрузку обрезанных JPEG.
ImageFile.LOAD_TRUNCATED_IMAGES = True

EXTENSIONS = ('.jpg', '.jpeg', '.tif', '.tiff', '.webp', '.png', '.heic', '.heif')
MAX_PATH_GAP = timedelta(hours=1)
MAX_PATH_DISTANCE_M = 1000.0

# Миниатюры: папка рядом с данными, максимальный размер по ширине и высоте.
THUMB_DIR_NAME = 'ico'
THUMB_MAX_SIZE = 240
THUMB_QUALITY = 85

# Журнал ошибок и пробный прогон.
LOG_FILE_NAME = 'photo_map.log'
CACHE_FILE_NAME = 'photo_map.cache.json'
CACHE_VERSION = 1

# Внешняя папка с уже готовыми миниатюрами и её индекс в SQLite.
DEFAULT_THUMB_SOURCE_DIR = r'D:\YandexDisk\ico'
THUMB_INDEX_FILE_NAME = 'photo_map_thumbs.sqlite3'
SAMPLE_THUMBS = 5          # сколько миниатюр сделать «на пробу» для оценки времени
TEST_DIR_NAME = 'test_run'
TEST_FILE_LIMIT = 1000
PROGRESS_STEP = 5          # шаг вывода прогресса, процентов
LOG_CONSOLE_LIMIT = 5      # сколько первых ошибок дублировать в консоль
SKIP_NOTICE_STEP = 500     # через сколько пропущенных миниатюр сообщать о них

# Результат чтения метаданных: источник даты и папка, из которой она взята.
Metadata = namedtuple('Metadata', 'lat lon timestamp source folder')

# Папка, которая сканируется, если путь не передан аргументом.
DEFAULT_PHOTO_DIR = r'D:\YandexDisk\Альбомы по годам'


def _configure_console():
    """Переводит консоль в UTF-8, чтобы эмодзи не ломали вывод на Windows."""
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding='utf-8', errors='replace')
        except (AttributeError, ValueError, OSError):
            pass


def format_spent(seconds):
    """Длительность этапа с точностью, полезной при разборе «где тормозит»."""
    if seconds < 1:
        return f'{seconds * 1000:.0f} мс'
    if seconds < 60:
        return f'{seconds:.1f} с'
    return format_duration(seconds)


class StageReporter:
    """Пошаговая телеметрия: что делаем, сколько запланировано, сколько заняло.

    Нужна, чтобы по выводу было видно, на каком этапе программа тормозит,
    и чтобы перед каждым этапом было объявлено, что именно будет сделано.
    """

    def __init__(self, total_stages, log=None):
        self.index = 0
        self.total = total_stages
        self.log = log
        self.timings = []
        self._started = 0.0
        self._title = ''

    def start(self, title, plan=None):
        self.index += 1
        self._title = title
        print(f'\n▶️  Этап {self.index}/{self.total}. {title}')
        if plan:
            print(f'   план: {plan}')
        if self.log:
            self.log.info(f'Этап {self.index}/{self.total}: {title}; план: {plan or "-"}')
        self._started = time.monotonic()

    def note(self, text):
        print(f'   {text}')
        if self.log:
            self.log.info(f'Этап {self.index}: {text}')

    def finish(self, details=None):
        spent = time.monotonic() - self._started
        if details:
            print(f'   {details}')
        print(f'   ✔ заняло {format_spent(spent)}')
        if self.log:
            self.log.info(f'Этап {self.index} завершён за {format_spent(spent)}'
                          + (f'; {details}' if details else ''))
        self.timings.append((self.index, self._title, spent))

    def summary(self):
        if not self.timings:
            return
        total = sum(item[2] for item in self.timings) or 1e-9
        print('\n⏱️  Где потрачено время:')
        for number, title, spent in self.timings:
            share = spent / total * 100
            bar = '█' * max(1, round(share / 4))
            print(f'   {number}. {title:<44} {format_spent(spent):>12}  '
                  f'{share:5.1f}%  {bar}')
        print(f'   {"итого":<48} {format_spent(total):>12}')


class ThumbIndex:
    """Список готовых миниатюр из внешних папок ico, с кэшем в SQLite.

    Сканирование 220 тысяч файлов в 5900 папках — сама по себе небыстрая
    операция, особенно на облачном диске. Поэтому список сохраняется в
    SQLite и переиспользуется: повторно папка обходится только если
    изменилось время её изменения или указан --rescan-thumbs.
    """

    def __init__(self, db_path):
        self.db_path = db_path
        self.by_name = {}       # имя в нижнем регистре -> [(source_root, rel)]
        self.loaded = False
        self.name_only_hits = 0  # имя нашлось, а путь в структуре — нет

    def _connect(self):
        conn = sqlite3.connect(self.db_path, timeout=30)
        conn.execute('PRAGMA journal_mode=WAL')
        conn.execute('PRAGMA synchronous=NORMAL')
        conn.execute('CREATE TABLE IF NOT EXISTS meta '
                     '(key TEXT PRIMARY KEY, value TEXT)')
        conn.execute('CREATE TABLE IF NOT EXISTS files ('
                     'source TEXT, name TEXT, rel TEXT, size INTEGER, '
                     'PRIMARY KEY (source, name, rel))')
        conn.execute('CREATE INDEX IF NOT EXISTS files_name ON files(name)')
        return conn

    def scan(self, source_root, force=False, progress=None):
        """Обходит source_root и обновляет список в БД.

        Возвращает (файлов, папок, из_кэша) или None, если папки нет.
        """
        if not source_root or not os.path.isdir(source_root):
            return None
        source_root = os.path.abspath(source_root)
        conn = self._connect()
        try:
            stamp = str(os.stat(source_root).st_mtime_ns)
            key_mtime = f'{source_root}|mtime'
            key_files = f'{source_root}|files'
            key_dirs = f'{source_root}|dirs'
            row = conn.execute('SELECT value FROM meta WHERE key=?',
                               (key_mtime,)).fetchone()
            if row and row[0] == stamp and not force:
                files_row = conn.execute('SELECT value FROM meta WHERE key=?',
                                         (key_files,)).fetchone()
                dirs_row = conn.execute('SELECT value FROM meta WHERE key=?',
                                        (key_dirs,)).fetchone()
                if files_row and dirs_row:
                    return int(files_row[0]), int(dirs_row[0]), True

            rows = []
            dirs = 0
            started = time.monotonic()
            last_report = started
            stack = [source_root]
            while stack:
                current = stack.pop()
                dirs += 1
                now = time.monotonic()
                if progress and (dirs % 100 == 0 or now - last_report >= 2):
                    last_report = now
                    progress(dirs, len(rows), now - started)
                try:
                    with os.scandir(current) as entries:
                        for entry in entries:
                            try:
                                if entry.is_dir(follow_symlinks=False):
                                    stack.append(entry.path)
                                    continue
                                if not entry.name.lower().endswith('.jpg'):
                                    continue
                                stat = entry.stat()
                                if stat.st_size <= 0:
                                    continue
                            except OSError:
                                continue
                            rel = os.path.relpath(entry.path, source_root)
                            rows.append((source_root, entry.name.lower(),
                                         rel.replace('\\', '/'), stat.st_size))
                except OSError:
                    continue

            with conn:
                conn.execute('DELETE FROM files WHERE source=?', (source_root,))
                conn.executemany(
                    'INSERT OR REPLACE INTO files (source, name, rel, size) '
                    'VALUES (?, ?, ?, ?)', rows)
                conn.executemany(
                    'INSERT OR REPLACE INTO meta (key, value) VALUES (?, ?)',
                    [(key_mtime, stamp), (key_files, str(len(rows))),
                     (key_dirs, str(dirs))])
            return len(rows), dirs, False
        finally:
            conn.close()

    def load(self):
        """Загружает весь список в память: имя -> [(папка-источник, путь)]."""
        if self.loaded:
            return len(self.by_name)
        self.by_name = {}
        if not os.path.isfile(self.db_path):
            self.loaded = True
            return 0
        conn = self._connect()
        try:
            for source, name, rel in conn.execute(
                    'SELECT source, name, rel FROM files'):
                self.by_name.setdefault(name, []).append((source, rel))
        finally:
            conn.close()
        self.loaded = True
        return len(self.by_name)

    def match(self, rel_thumb):
        """Ищет готовую миниатюру для ожидаемого пути, с учётом структуры папок.

        Сравнение регистронезависимое: миниатюры и снимки легко расходятся
        в регистре (IMG_0001.JPG против img_0001.jpg), а на Windows, где
        обычно и запускается программа, это один и тот же файл.
        """
        name = rel_thumb.rsplit('/', 1)[-1].lower()
        target = rel_thumb.lower().replace('\\', '/')
        candidates = self.by_name.get(name, ())
        for source, rel in candidates:
            low = rel.lower()
            # Миниатюра может лежать ровно по ожидаемому пути (ico — сам корень)
            # или глубже, если в ico сохранён ещё и родительский уровень.
            if low == target or low.endswith('/' + target):
                return os.path.join(source, *rel.split('/'))
        if candidates:
            self.name_only_hits += 1
        return None

    def close(self):
        self.by_name = {}

class RunLog:
    """Журнал работы: ошибки и предупреждения пишутся в файл (UTF-8).

    Первые LOG_CONSOLE_LIMIT ошибок дублируются в консоль, дальше консоль
    не засоряется — при тысячах неподдерживаемых HEIC это важно.
    """

    def __init__(self, path=None, console_limit=LOG_CONSOLE_LIMIT):
        self.path = os.path.abspath(path) if path else None
        self.console_limit = console_limit
        self.errors = 0
        self.warnings = 0
        self._stream = None
        if self.path:
            directory = os.path.dirname(self.path)
            if directory:
                os.makedirs(directory, exist_ok=True)
            self._stream = open(self.path, 'a', encoding='utf-8')

    def _stamp(self):
        return datetime.now().strftime('%Y-%m-%d %H:%M:%S')

    def _write(self, text):
        if self._stream:
            self._stream.write(text + '\n')
            self._stream.flush()

    def section(self, title):
        self._write('')
        self._write(f'===== {title} =====')

    def info(self, message):
        self._write(f'[{self._stamp()}] {message}')

    def warning(self, message):
        self.warnings += 1
        self._write(f'[{self._stamp()}] ВНИМАНИЕ {message}')

    def error(self, message):
        self.errors += 1
        self._write(f'[{self._stamp()}] ОШИБКА {message}')
        if self.errors <= self.console_limit:
            print(f'⚠️ {message}', file=sys.stderr)
        elif self.errors == self.console_limit + 1:
            print(f'⚠️ Дальнейшие ошибки — только в логе: {self.path}', file=sys.stderr)

    def close(self):
        if self._stream:
            self._stream.close()
            self._stream = None


DEFAULT_LOG = RunLog()


def plural(number, one, few, many):
    """'1 папка', '2 папки', '5 папок' — чтобы сообщения читались по-русски."""
    number = abs(int(number))
    if number % 10 == 1 and number % 100 != 11:
        return f'{number} {one}'
    if 2 <= number % 10 <= 4 and not 12 <= number % 100 <= 14:
        return f'{number} {few}'
    return f'{number} {many}'


def with_approx(text):
    """'~5 мин 10 с', но '<1 с' без лишней тильды."""
    return text if text.startswith('<') else f'~{text}'


def format_duration(seconds):
    """'1 ч 12 мин', '3 мин 05 с' — для оценки оставшегося времени."""
    if 0 <= seconds < 1:
        return '<1 с'
    seconds = int(max(0, seconds))
    hours, rest = divmod(seconds, 3600)
    minutes, secs = divmod(rest, 60)
    if hours:
        return f'{hours} ч {minutes:02d} мин'
    if minutes:
        return f'{minutes} мин {secs:02d} с'
    return f'{secs} с'


def progress_printer(label, total, step=PROGRESS_STEP):
    """Возвращает функцию: печатает прогресс шагами по step% от ожидаемого объёма.

    Шаг считается от предполагаемого количества (total), поэтому для 1000 файлов
    строка появляется каждые 50 файлов: 5%, 10%, …, 100%. Рядом печатаются
    скорость и оценка остатка — чтобы длинная обработка не выглядела зависанием.
    """
    # На малых объёмах шаг 5% — это 1–2 файла, и строка превращается в шум.
    # Поэтому не чаще, чем раз в 50 файлов (финальные 100% печатаются всегда).
    every = max(50 if total >= 200 else total + 1,
                int(round(total * step / 100)))
    printed = 0
    started = datetime.now()
    last_print = started

    def report(index):
        nonlocal printed, last_print
        now = datetime.now()
        due_by_step = (index % every == 0 and index != printed) or index >= total
        # Если очередной шаг далеко (сотни тысяч файлов), раз в минуту
        # печатаем строку, чтобы работа не выглядела зависанием.
        due_by_time = (now - last_print).total_seconds() >= 60
        if not (due_by_step or due_by_time):
            return
        printed = index
        last_print = now
        percent = min(100, round(index * 100 / total))
        elapsed = max(0.001, (now - started).total_seconds())
        rate = index / elapsed
        tail = ''
        if elapsed > 2 and index < total and rate > 0:
            remaining = (total - index) / rate
            if remaining >= 1:
                tail = (f' — {rate:.1f} файлов/с, осталось '
                        f'{with_approx(format_duration(remaining))}')
        print(f'⏳ {label}: {percent}% ({index} из {total}){tail}')

    return report


def register_heic_support():
    """Подключает pillow-heif, если он установлен. Иначе HEIC/HEIF не декодируются."""
    try:
        import pillow_heif
    except ImportError:
        return False
    pillow_heif.register_heif_opener()
    return True


def collect_images(root_dir, excluded_dirs, progress=None):
    """Собирает изображения, не заходя в папки миниатюр и пробных прогонов."""
    files = []
    started = time.monotonic()
    last_report = started
    for dirpath, dirnames, filenames in os.walk(root_dir):
        dirnames[:] = [
            name for name in dirnames
            if os.path.abspath(os.path.join(dirpath, name)) not in excluded_dirs
        ]
        for filename in filenames:
            if filename.lower().endswith(EXTENSIONS):
                files.append(os.path.join(dirpath, filename))
        now = time.monotonic()
        if progress and now - last_report >= 2:
            last_report = now
            progress(len(files), now - started)
    files.sort()
    return files


def copy_viewer_files(target_dir):
    """Копирует map.html и photo-path.html рядом с JSON пробного прогона."""
    script_dir = os.path.dirname(os.path.abspath(__file__))
    copied = []
    for name in ('map.html', 'photo-path.html'):
        source = os.path.join(script_dir, name)
        if os.path.isfile(source):
            shutil.copyfile(source, os.path.join(target_dir, name))
            copied.append(name)
    return copied


def dms_to_dd(dms, ref):
    """Конвертирует GPS-координаты из градусов/минут/секунд в десятичные."""
    def to_float(value):
        if isinstance(value, tuple) and len(value) == 2:
            return value[0] / value[1]
        return float(value)

    try:
        degrees, minutes, seconds = (to_float(value) for value in dms)
        result = degrees + minutes / 60.0 + seconds / 3600.0
        if ref in ('S', 'W', b'S', b'W'):
            result = -result
        return result
    except (TypeError, ValueError, ZeroDivisionError):
        return None


def parse_exif_datetime(value):
    """Парсит дату EXIF: '2023:05:15 14:30:00' и близкие варианты.

    Встречаются файлы с долями секунды, смещением часового пояса, форматом
    через дефис или без секунд — такие значения тоже разбираем.
    """
    if not value:
        return None
    if isinstance(value, bytes):
        value = value.decode('utf-8', errors='ignore')
    value = str(value).strip().strip('\x00').strip()
    # '2023:05:15 14:30:00.123+03:00' -> '2023:05:15 14:30:00'
    value = re.split(r'[.\s]?(?:Z|[+-]\d{2}:?\d{2})$', value)[0]
    value = re.sub(r'\.\d+$', '', value).strip()
    for fmt in ('%Y:%m:%d %H:%M:%S', '%Y-%m-%d %H:%M:%S',
                '%Y:%m:%d %H:%M', '%Y-%m-%dT%H:%M:%S', '%Y:%m:%d'):
        try:
            return datetime.strptime(value, fmt)
        except ValueError:
            continue
    return None


def read_exif_timestamp(exif, img=None):
    """Дата съёмки из EXIF: Exif-подкаталог, затем IFD0, затем XMP.

    Теги DateTimeOriginal (0x9003) и DateTimeDigitized (0x9004) лежат
    в Exif-подкаталоге (0x8769), а не в основном IFD. DateTime (0x0132)
    наоборот — в основном. Читаем оба места: раньше 0x9003 искали только
    в основном IFD, поэтому дата почти всегда терялась и бралась из mtime.
    """
    exif_ifd = {}
    try:
        exif_ifd = exif.get_ifd(0x8769) or {}
    except Exception:
        exif_ifd = {}

    for tag_id in (0x9003, 0x9004, 0x0132):
        # Сначала подкаталог, потом основной IFD — на случай нестандартной записи.
        for source in (exif_ifd, exif):
            try:
                value = source.get(tag_id)
            except Exception:
                value = None
            timestamp = parse_exif_datetime(value)
            if timestamp:
                return timestamp

    # Некоторые конвертеры пишут дату только в XMP.
    if img is not None:
        xmp = img.info.get('xmp') or exif.get(700) or b''
        if isinstance(xmp, bytes):
            xmp = xmp.decode('utf-8', errors='ignore')
        if xmp:
            for pattern in (r'exif:DateTimeOriginal[^>]*>([^<]+)<',
                            r'photoshop:DateCreated[^>]*>([^<]+)<',
                            r'xmp:CreateDate[^>]*>([^<]+)<'):
                match = re.search(pattern, xmp)
                if match:
                    timestamp = parse_exif_datetime(match.group(1))
                    if timestamp:
                        return timestamp
    return None


# Папки с датой в имени: 2024_01_31, 2024-01-31, 2024.01.31, 2025_07, _2025.
# Порядок важен: сначала самое точное совпадение.
FOLDER_DATE_PATTERNS = (
    ('day', re.compile(
        r'^(?P<y>(?:19|20)\d{2})[_\-\.](?P<m>0?[1-9]|1[0-2])'
        r'[_\-\.](?P<d>0?[1-9]|[12]\d|3[01])(?:$|[_\-\s(.])')),
    ('month', re.compile(
        r'^(?P<y>(?:19|20)\d{2})[_\-\.](?P<m>0?[1-9]|1[0-2])(?:$|[_\-\s(.])')),
    ('year', re.compile(
        r'^[_\-\.\s]*(?P<y>(?:19|20)\d{2})[_\-\.\s]*(?:$|[_\-\s(.])')),
)


def match_folder_date(name):
    """Возвращает (дата, точность) по имени папки или (None, None)."""
    for precision, pattern in FOLDER_DATE_PATTERNS:
        match = pattern.match(name)
        if not match:
            continue
        year = int(match.group('y'))
        month = int(match.groupdict().get('m') or 1)
        day = int(match.groupdict().get('d') or 1)
        try:
            return datetime(year, month, day), precision
        except ValueError:
            continue      # например 2024_02_31 — некорректная дата, пробуем грубее
    return None, None


def date_from_path(path, root_dir=None):
    """Дата по папке, в которой лежит файл: 2024_01_31, 2025_07, _2025.

    Идём от папки файла вверх до root_dir и берём первое совпадение —
    самая близкая папка считается самой точной. Если даты в пути нет,
    возвращает (None, None).
    """
    folder = os.path.dirname(os.path.abspath(path))
    root = os.path.abspath(root_dir) if root_dir else None
    while True:
        name = os.path.basename(folder)
        found, precision = match_folder_date(name)
        if found:
            return found, precision, name
        if root and os.path.normcase(folder) == os.path.normcase(root):
            return None, None, None
        parent = os.path.dirname(folder)
        if parent == folder:
            return None, None, None
        folder = parent


def get_metadata(path, log=None, root_dir=None):
    """Возвращает (широта, долгота, дата, источник даты).

    Источник: 'exif' (EXIF/XMP), 'folder' (имя папки), 'mtime' (файловая
    система) или None, если дата не определена.
    """
    log = log or DEFAULT_LOG
    lat = lon = timestamp = None
    source = None
    try:
        with Image.open(path) as img:
            exif = img.getexif()
            timestamp = read_exif_timestamp(exif, img)
            if timestamp:
                source = 'exif'

            gps_ifd = exif.get_ifd(0x8825)
            if gps_ifd:
                lat = dms_to_dd(gps_ifd.get(0x0002), gps_ifd.get(0x0001))
                lon = dms_to_dd(gps_ifd.get(0x0004), gps_ifd.get(0x0003))
                if lat == 0.0 and lon == 0.0:
                    lat = lon = None

            if lat is None or lon is None:
                xmp = (img.info.get('xmp') or img.info.get('XML:com.adobe.xmp')
                       or exif.get(700))
                if xmp:
                    if isinstance(xmp, bytes):
                        xmp = xmp.decode('utf-8', errors='ignore')
                    lat_match = re.search(r'Latitude[">]+([+-]?\d+\.?\d*)', xmp)
                    lon_match = re.search(r'Longitude[">]+([+-]?\d+\.?\d*)', xmp)
                    if lat_match and lon_match:
                        lat = float(lat_match.group(1))
                        lon = float(lon_match.group(1))
                        if lat == 0.0 and lon == 0.0:
                            lat = lon = None
    except Exception as exc:
        log.error(f'Не удалось прочитать метаданные {path}: {exc}')

    # Нет даты в метаданных — пробуем имя папки (2024_01_31, 2025_07, _2025),
    # и только в последнюю очередь время изменения файла.
    folder_name = None
    if timestamp is None:
        timestamp, _precision, folder_name = date_from_path(path, root_dir)
        if timestamp:
            source = 'folder'
    if timestamp is None:
        try:
            timestamp = datetime.fromtimestamp(os.path.getmtime(path))
            source = 'mtime'
        except OSError:
            pass
    return Metadata(lat, lon, timestamp, source, folder_name)


def plan_thumbnails(files, root_dir):
    """Планирует имена миниатюр, повторяя структуру папок исходных файлов.

    Возвращает словарь {исходный файл: путь миниатюры относительно папки ico}.
    Расширение всегда .jpg — иначе браузер не покажет HEIC/TIFF/PNG-исходник.
    Если в папке есть файлы с одинаковым именем, но разными расширениями
    (a.jpg и a.png), к имени добавляется исходное расширение.
    """
    by_dir = defaultdict(list)
    for path in files:
        by_dir[os.path.dirname(path)].append(path)

    plan = {}
    for group in by_dir.values():
        by_stem = defaultdict(list)
        for path in group:
            by_stem[os.path.splitext(os.path.basename(path))[0].lower()].append(path)
        for stem, same_stem in by_stem.items():
            for path in same_stem:
                base = os.path.basename(path)
                ext = base.rsplit('.', 1)[-1].lower() if '.' in base else ''
                thumb_name = f'{stem}.jpg' if len(same_stem) == 1 else f'{stem}_{ext}.jpg'
                rel = os.path.relpath(path, root_dir).replace('\\', '/')
                sub = os.path.dirname(rel)
                plan[path] = f'{sub}/{thumb_name}' if sub else thumb_name
    return plan


def make_thumbnail(source_path, dest_path, max_size=THUMB_MAX_SIZE, log=None, force=False):
    """Создаёт уменьшенную копию: не более max_size пикселей по ширине и высоте.

    Ориентация EXIF учитывается, прозрачность заливается белым.
    Уже существующая миниатюра не пересоздаётся (если не указан force).
    Возвращает 'created', 'skipped' или 'failed'.
    """
    log = log or DEFAULT_LOG
    if not force and os.path.isfile(dest_path) and os.path.getsize(dest_path) > 0:
        return 'skipped'

    tmp_path = dest_path + '.tmp'
    try:
        with Image.open(source_path) as img:
            # JPEG умеет декодироваться сразу в уменьшенном масштабе (1/2, 1/4, 1/8):
            # для миниатюры 240 px полный кадр 4000 px разбирать незачем.
            if img.format == 'JPEG':
                try:
                    img.draft('RGB', (max_size * 2, max_size * 2))
                except Exception:
                    pass
            img = ImageOps.exif_transpose(img)
            if img.mode in ('RGBA', 'LA', 'P'):
                img = img.convert('RGBA')
                background = Image.new('RGB', img.size, (255, 255, 255))
                background.paste(img, mask=img.split()[-1])
                img = background
            elif img.mode != 'RGB':
                img = img.convert('RGB')
            img.thumbnail((max_size, max_size), Image.LANCZOS)
            parent = os.path.dirname(dest_path)
            if parent:
                os.makedirs(parent, exist_ok=True)
            img.save(tmp_path, 'JPEG', quality=THUMB_QUALITY, optimize=True)
        # Переименование атомарно: недописанный файл не будет принят за готовый.
        os.replace(tmp_path, dest_path)
        return 'created'
    except Exception as exc:
        log.error(f'Не удалось создать миниатюру {source_path}: {exc}')
        try:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
        except OSError:
            pass
        return 'failed'


def haversine_m(lat1, lon1, lat2, lon2):
    """Расстояние между координатами по дуге большого круга, в метрах."""
    from math import asin, cos, radians, sin, sqrt

    earth_radius_m = 6_371_000.0
    phi1, phi2 = radians(lat1), radians(lat2)
    d_phi = radians(lat2 - lat1)
    d_lambda = radians(lon2 - lon1)
    a = sin(d_phi / 2) ** 2 + cos(phi1) * cos(phi2) * sin(d_lambda / 2) ** 2
    return 2 * earth_radius_m * asin(sqrt(min(1.0, a)))


def build_paths(points):
    """Строит последовательные сегменты: соседние точки <1 ч и <1 км.

    Индексы в путях ссылаются на исходный массив points. Если хотя бы одно
    условие для соседней пары не соблюдено, текущий сегмент заканчивается.
    """
    paths = []
    current = []
    previous = None

    for index, point in enumerate(points):
        timestamp_text = point.get('timestamp')
        try:
            timestamp = datetime.fromisoformat(timestamp_text) if timestamp_text else None
        except (TypeError, ValueError):
            timestamp = None

        if timestamp is None:
            if len(current) >= 2:
                paths.append(current)
            current, previous = [], None
            continue

        if previous is None:
            current = [index]
        else:
            prev_index, prev_timestamp = previous
            prev = points[prev_index]
            elapsed = timestamp - prev_timestamp
            distance = haversine_m(float(prev['lat']), float(prev['lon']),
                                   float(point['lat']), float(point['lon']))
            if (timedelta(0) <= elapsed < MAX_PATH_GAP
                    and distance < MAX_PATH_DISTANCE_M):
                current.append(index)
            else:
                if len(current) >= 2:
                    paths.append(current)
                current = [index]
        previous = (index, timestamp)

    if len(current) >= 2:
        paths.append(current)
    return paths


def load_metadata_cache(path):
    """Кэш метаданных: {путь: [размер, mtime_ns, широта, долгота, дата, источник]}.

    Чтение EXIF — самая дорогая операция после миниатюр: на 200+ тысячах
    снимков с облачного диска это часы. Для неизменившихся файлов (совпали
    размер и время изменения) метаданные берутся из кэша, файл не открывается.
    """
    try:
        with open(path, encoding='utf-8') as file_obj:
            data = json.load(file_obj)
    except (OSError, ValueError):
        return {}
    if not isinstance(data, dict) or data.get('version') != CACHE_VERSION:
        return {}
    files = data.get('files')
    return files if isinstance(files, dict) else {}


def save_metadata_cache(path, files):
    """Атомарно сохраняет кэш метаданных."""
    tmp_path = path + '.tmp'
    try:
        with open(tmp_path, 'w', encoding='utf-8') as file_obj:
            json.dump({'version': CACHE_VERSION, 'files': files}, file_obj,
                      ensure_ascii=False, separators=(',', ':'))
        os.replace(tmp_path, path)
        return True
    except OSError:
        try:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
        except OSError:
            pass
        return False


def cached_metadata(entry, rel_path):
    """Восстанавливает Metadata из записи кэша или возвращает None."""
    if not isinstance(entry, (list, tuple)) or len(entry) < 6:
        return None
    timestamp = None
    if entry[4]:
        try:
            timestamp = datetime.fromisoformat(entry[4])
        except (TypeError, ValueError):
            return None
    return Metadata(entry[2], entry[3], timestamp, entry[5], None)


def index_thumbnails(thumbs_root):
    """Собирает готовые миниатюры одним проходом по папке ico.

    Возвращает словарь {нормализованный путь: путь как на диске}. Индекс
    заменяет отдельный stat на каждую фотографию: на коллекции в сотни
    тысяч файлов это сильно быстрее, особенно на облачном/сетевом диске.
    """
    existing = {}
    if not os.path.isdir(thumbs_root):
        return existing
    # os.scandir обходит дерево быстрее os.walk: размер берётся из записи каталога.
    stack = [thumbs_root]
    while stack:
        current = stack.pop()
        try:
            with os.scandir(current) as entries:
                for entry in entries:
                    try:
                        if entry.is_dir(follow_symlinks=False):
                            stack.append(entry.path)
                            continue
                        if not entry.name.lower().endswith('.jpg'):
                            continue
                        if entry.stat().st_size <= 0:
                            continue      # пустой/обрезанный файл — пересоздадим
                    except OSError:
                        continue
                    rel = os.path.relpath(entry.path, thumbs_root).replace('\\', '/')
                    existing[os.path.normcase(rel)] = rel
        except OSError:
            continue
    return existing


def explain_root_mismatch(existing, plan):
    """Ищет объяснение: миниатюры есть, но пути не совпадают с текущим корнем.

    Сравниваем по имени файла: если миниатюра с таким же именем лежит под
    другим префиксом, значит ico создавалась для другой корневой папки —
    самый частый случай после изменения папки по умолчанию.
    Возвращает текст подсказки или None.
    """
    if not existing:
        return None
    by_name = {}
    for rel in existing.values():
        by_name.setdefault(rel.rsplit('/', 1)[-1], []).append(rel)
    samples = []
    for rel_thumb in plan.values():
        name = rel_thumb.rsplit('/', 1)[-1]
        for found in by_name.get(name, ()):
            if found != rel_thumb and found.endswith('/' + rel_thumb):
                prefix = found[:-len(rel_thumb)].rstrip('/')
                samples.append((prefix, found, rel_thumb))
                break
        if len(samples) >= 20:
            break
    if not samples:
        return None
    prefixes = {prefix for prefix, _, _ in samples}
    if len(prefixes) == 1:
        prefix = samples[0][0]
        return (f'Готовые миниатюры лежат в подпапке «{prefix}». '
                f'Похоже, ico создавалась для родительской папки. Перенесите '
                f'{os.path.join(THUMB_DIR_NAME, *prefix.split("/"))} в '
                f'{os.path.join(os.path.basename(prefix), THUMB_DIR_NAME)} — '
                f'тогда пути совпадут и миниатюры не придётся создавать заново.')
    prefix, found, expected = samples[0]
    return (f'Есть похожая миниатюра {found}, а ожидается {expected}. '
            f'Похоже, ico создавалась для другой корневой папки.')


def find_thumb_migration_hint(root_dir, thumbs_root, plan):
    """Подсказка, если готовые миниатюры лежат в ico родительской папки.

    Типичный случай: раньше сканировали `...\\new1`, миниатюры легли в
    `...\\new1\\ico\\Альбомы по годам\\...`, а теперь корень —
    `...\\new1\\Альбомы по годам`, и ожидается
    `...\\new1\\Альбомы по годам\\ico\\...`. Пути не совпадают, хотя
    сами миниатюры уже есть. Возвращает текст с готовым решением.
    """
    root_abs = os.path.abspath(root_dir)
    parent_ico = os.path.join(os.path.dirname(root_abs), THUMB_DIR_NAME)
    if not os.path.isdir(parent_ico):
        return None
    if os.path.normcase(parent_ico) == os.path.normcase(os.path.abspath(thumbs_root)):
        return None

    expected_by_name = {}
    for rel in plan.values():
        expected_by_name.setdefault(os.path.normcase(rel.rsplit('/', 1)[-1]), []).append(rel)

    prefixes = set()
    example = None
    found = 0
    for dirpath, _, filenames in os.walk(parent_ico):
        for name in filenames:
            if not name.lower().endswith('.jpg'):
                continue
            for expected in expected_by_name.get(os.path.normcase(name), ()):
                rel = os.path.relpath(os.path.join(dirpath, name), parent_ico)
                rel = rel.replace('\\', '/')
                normed = os.path.normcase(rel)
                if not normed.endswith('/' + os.path.normcase(expected)):
                    continue
                prefix = rel[:len(rel) - len(expected)].rstrip('/')
                prefixes.add(prefix)
                example = example or (rel, expected)
                found += 1
        if found >= 20:
            break
    if not found:
        return None

    if len(prefixes) == 1:
        prefix = prefixes.pop()
        source = os.path.join(parent_ico, *prefix.split('/'))
        target = os.path.join(root_abs, THUMB_DIR_NAME)
        return (f'Похоже, миниатюры уже созданы для папки верхнего уровня: '
                f'{source}. Перенесите эту папку в {target} (или запустите '
                f'скрипт с корнем {os.path.dirname(root_abs)}) — тогда готовые '
                f'миниатюры будут переиспользованы, а не созданы заново.')
    existing_rel, expected_rel = example
    return (f'Есть похожая миниатюра {existing_rel}, а ожидается {expected_rel}. '
            f'Похоже, ico создавалась для другой корневой папки.')


def plan_thumbnail_work(files, root_dir, thumbs_root, thumb_index=None, force=False):
    """Сопоставляет снимки с готовыми миниатюрами, ничего не создавая.

    Возвращает словарь с планом: что уже на месте, что можно скопировать
    из внешней ico и что придётся создавать.
    """
    plan = plan_thumbnails(files, root_dir)
    existing = index_thumbnails(thumbs_root)
    missing = [(rel, path) for path, rel in plan.items()
               if force or os.path.normcase(rel) not in existing]
    ready = len(plan) - len(missing)

    reusable = {}
    if thumb_index is not None and not force:
        for rel, _ in missing:
            source = thumb_index.match(rel)
            if source and os.path.isfile(source):
                reusable[os.path.normcase(rel)] = source

    return {
        'plan': plan,
        'existing': existing,
        'missing': missing,
        'reusable': reusable,
        'ready': ready,
        'todo': len(missing) - len(reusable),
    }


def build_thumbnails(files, root_dir, thumbs_root, thumb_size, url_base=None,
                     log=None, force=False, thumb_index=None, stages=None,
                     work=None):
    """Создаёт недостающие миниатюры, используя индекс внешних папок ico.

    Возвращает ({исходный файл: путь миниатюры для JSON}, статистику).
    Готовые миниатюры не пересоздаются, но всё равно попадают в результат.
    """
    log = log or DEFAULT_LOG
    url_base = url_base or root_dir
    try:
        url_prefix = os.path.relpath(thumbs_root, url_base).replace('\\', '/')
    except ValueError:
        log.warning(f'Папка миниатюр {thumbs_root} на другом диске: '
                    f'ссылки в JSON будут указывать на {THUMB_DIR_NAME}/')
        url_prefix = THUMB_DIR_NAME
    if url_prefix == '.':
        url_prefix = ''
    elif url_prefix.startswith('..'):
        note = (f'Папка миниатюр {thumbs_root} лежит вне корня {url_base}: '
                f'браузер не покажет такие изображения. Лучше держать ico '
                f'внутри корня или указать серверу более общую папку.')
        print(f'⚠️  {note}')
        log.warning(note)

    work = work or plan_thumbnail_work(files, root_dir, thumbs_root,
                                       thumb_index, force)
    plan = work['plan']
    existing = work['existing']
    missing = work['missing']
    reusable = work['reusable']
    ready = work['ready']
    todo = work['todo']

    if not todo:
        print('🧭 Решение: создавать нечего — этап генерации миниатюр '
              'пропускается, все файлы уже есть.')
    elif todo == len(plan):
        print(f'🧭 Решение: создавать миниатюры — готовых нет, нужно создать '
              f'все {len(plan)}.')
    else:
        print(f'🧭 Решение: {plural(todo, "миниатюра", "миниатюры", "миниатюр")} '
              f'создать, {len(plan) - todo} возьмётся готовыми '
              f'({todo * 100 // max(1, len(plan))}% работы).')

    if todo and not ready and not reusable and not force:
        hint = explain_root_mismatch(existing, plan) or \
            find_thumb_migration_hint(root_dir, thumbs_root, plan)
        if hint:
            print(f'⚠️  {hint}')
            log.warning(hint)

    stats = {'created': 0, 'skipped': 0, 'reused': 0, 'failed': 0}
    result = {}
    processed = 0
    report = progress_printer('Миниатюры', len(plan))

    def register(rel_thumb, path, status):
        nonlocal processed
        stats[status] += 1
        processed += 1
        if status != 'failed':
            rel_file = os.path.relpath(path, url_base).replace('\\', '/')
            result[rel_file] = (f'{url_prefix}/{rel_thumb}' if url_prefix
                                else rel_thumb)
        if status == 'skipped' and stats['skipped'] % SKIP_NOTICE_STEP == 0:
            note = (f'Пропущено уже готовых миниатюр: {stats["skipped"]} '
                    f'(не пересоздаются)')
            print(f'♻️  {note}')
            log.info(note)
        report(processed)

    def create(rel, path):
        # make_thumbnail сам решает, нужно ли работать: если файл уже есть
        # и не задан force, исходник не открывается вообще.
        dest = os.path.join(thumbs_root, *rel.split('/'))
        status = make_thumbnail(path, dest, thumb_size, log=log, force=force)
        if status == 'created':
            existing[os.path.normcase(rel)] = rel
        return status

    # 3. Пробный замер на нескольких файлах — чтобы объявить оценку времени.
    pending = [(rel, path) for rel, path in missing
               if os.path.normcase(rel) not in reusable]
    sample_keys = set()
    if pending:
        sample = pending[:min(SAMPLE_THUMBS, len(pending))]
        started = time.monotonic()
        made = 0
        for rel, path in sample:
            status = create(rel, path)
            if status == 'created':
                made += 1
            sample_keys.add(os.path.normcase(rel))
            register(rel, path, status)
        spent = time.monotonic() - started
        if made and spent > 0:
            rate = made / spent
            estimate = (len(pending) - made) / rate
            print(f'⏱️  Замер: {made} миниатюр за {spent:.1f} с '
                  f'({rate:.1f} шт/с). Оценка на остаток: '
                  f'{with_approx(format_duration(estimate))}')
            log.info(f'Замер скорости миниатюр: {rate:.1f} шт/с, '
                     f'оценка остатка {format_duration(estimate)}')
        if stages:
            stages.note(f'пробный замер: {made} шт за {spent:.1f} с')
        pending = pending[len(sample):]

    # 4. Копирование из внешней ico и создание остальных.
    for rel, path in missing:
        key = os.path.normcase(rel)
        if key in sample_keys:
            continue
        dest = os.path.join(thumbs_root, *rel.split('/'))
        if key in existing and not force:
            register(rel, path, 'skipped')
        elif key in reusable:
            try:
                # Готовая миниатюра из старой папки: снимок не открываем,
                # копирование в разы дешевле декодирования.
                parent = os.path.dirname(dest)
                if parent:
                    os.makedirs(parent, exist_ok=True)
                shutil.copy2(reusable[key], dest)
                existing[key] = rel
                register(rel, path, 'reused')
            except OSError as exc:
                log.warning(f'Не удалось скопировать миниатюру '
                            f'{reusable[key]}: {exc}')
                register(rel, path, create(rel, path))
        else:
            register(rel, path, create(rel, path))

    return result, stats


def resolve_root(root_dir):
    """Абсолютный путь к папке с фотографиями.

    Если путь не передан, берётся DEFAULT_PHOTO_DIR. Переменные окружения
    вида %USERPROFILE% раскрываются, '~' тоже понимается.
    """
    path = root_dir if root_dir else DEFAULT_PHOTO_DIR
    path = os.path.expandvars(os.path.expanduser(path))
    # Windows-путь в не-Windows среде (WSL, Linux) не склеиваем с текущей папкой:
    # так ошибка «папка не найдена» показывает исходный путь, а не /cwd/D:\...
    if os.name != 'nt' and re.match(r'^[A-Za-z]:[\\/]', path):
        return path
    return os.path.abspath(path)


def main(root_dir=None, thumbs_dir=None, thumb_size=THUMB_MAX_SIZE, make_thumbs=True,
         log_path=None, force_thumbs=False, test_limit=None, no_cache=False,
         thumb_sources=None, rescan_thumbs=False):
    started = datetime.now()
    used_default = not root_dir
    root_dir = resolve_root(root_dir)
    if not os.path.isdir(root_dir):
        print(f'❌ Папка не найдена: {root_dir}')
        if used_default:
            print(f'   Это папка по умолчанию ({DEFAULT_PHOTO_DIR}).')
            print('   Укажите путь явно:  python photo_map.py "D:\\путь\\к\\фотографиям"')
            print('   Или текущую папку:  python photo_map.py .')
        else:
            print('   Проверьте путь и повторите запуск.')
        return 1
    if used_default:
        print(f'📂 Папка по умолчанию: {root_dir}')

    # В пробном прогоне результаты и лог уходят в отдельную папку:
    # боевые points_*.json и миниатюры не перезаписываются.
    out_dir = os.path.join(root_dir, TEST_DIR_NAME) if test_limit else root_dir
    if test_limit:
        os.makedirs(out_dir, exist_ok=True)
    thumbs_root = (os.path.abspath(thumbs_dir) if thumbs_dir
                   else os.path.join(out_dir, THUMB_DIR_NAME))
    log = RunLog(os.path.abspath(log_path) if log_path
                 else os.path.join(out_dir, LOG_FILE_NAME))
    log.section(f'Запуск {started:%Y-%m-%d %H:%M:%S}')
    log.info(f'Папка с фотографиями: {root_dir}')
    if test_limit:
        log.info(f'Пробный прогон: не более {test_limit} файлов, результаты в {out_dir}')

    # Собственные папки результатов не должны попадать в сканирование,
    # иначе миниатюры .jpg со второго запуска начнут считаться фотографиями.
    excluded_dirs = {os.path.abspath(path) for path in (
        thumbs_root,
        os.path.join(root_dir, THUMB_DIR_NAME),
        os.path.join(root_dir, TEST_DIR_NAME),
    )}

    stages = StageReporter(6 if make_thumbs else 4, log=log)

    # ---- Этап 1: папка с изображениями ----
    stages.start('Сканирование папки с изображениями', f'обход {root_dir}')
    shown = []

    def show_files(count, spent):
        shown.append(count)
        print(f'   ⏳ обход: {count} изображений, {spent:.0f} с',
              end='\r', flush=True)

    files = collect_images(root_dir, excluded_dirs, progress=show_files)
    if shown:
        print(' ' * 60, end='\r')
    found = len(files)
    stages.finish(f'найдено изображений: {found}')
    if not found:
        print('Изображения не найдены; JSON-файлы не созданы.')
        log.info('Изображения не найдены.')
        log.close()
        return

    if test_limit:
        files = files[:test_limit]
        print(f'🧪 Пробный прогон: обрабатываю {len(files)} из {found} файлов')
        log.info(f'Пробный прогон: обрабатываю {len(files)} из {found} файлов')
    total = len(files)

    if not register_heic_support() and any(
            path.lower().endswith(('.heic', '.heif')) for path in files):
        hint = ('HEIC/HEIF не декодируется установленной Pillow: для таких файлов '
                'не будет ни миниатюр, ни метаданных. Установите: '
                'python -m pip install pillow-heif')
        print(f'💡 {hint}')
        log.warning(hint)

    thumbs = {}
    thumb_index = None
    if make_thumbs:
        # ---- Этап 2: внешние папки с готовыми миниатюрами ----
        sources = []
        for path in (thumb_sources or []) + [DEFAULT_THUMB_SOURCE_DIR]:
            if not path:
                continue
            path = os.path.abspath(os.path.expandvars(os.path.expanduser(path)))
            if os.path.normcase(path) not in {os.path.normcase(x) for x in sources}:
                sources.append(path)
        if test_limit:
            # В пробном прогоне миниатюры пишутся в test_run/ico, но готовые
            # ищем и в боевой папке — только на чтение.
            sources.append(os.path.join(root_dir, THUMB_DIR_NAME))
        parent_ico = os.path.join(os.path.dirname(root_dir), THUMB_DIR_NAME)
        if os.path.isdir(parent_ico) and os.path.normcase(parent_ico) not in {
                os.path.normcase(x) for x in sources}:
            sources.append(parent_ico)
        existing_sources = [path for path in sources if os.path.isdir(path)]

        if existing_sources:
            stages.start('Предварительное сканирование папок ico',
                         plural(len(existing_sources), 'папка', 'папки', 'папок')
                         + ': ' + ', '.join(existing_sources))
        else:
            stages.start('Предварительное сканирование папок ico',
                         'внешних папок не найдено — используются только '
                         'миниатюры рядом с JSON')

        index_db = os.path.join(out_dir, THUMB_INDEX_FILE_NAME)
        thumb_index = ThumbIndex(index_db)
        scanned_now = False
        for source in existing_sources:
            shown_scan = []

            def show_scan(dirs, files_count, spent):
                shown_scan.append(dirs)
                print(f'   ⏳ обход ico: {dirs} папок, {files_count} файлов, '
                      f'{spent:.0f} с', end='\r', flush=True)

            result = thumb_index.scan(source, force=rescan_thumbs,
                                      progress=show_scan)
            if shown_scan:
                print(' ' * 70, end='\r')
            if result is None:
                continue
            count, dirs, from_cache = result
            scanned_now = scanned_now or not from_cache
            stages.note(f'{source}: файлов {count}, папок {dirs}'
                        + (' — из кэша SQLite' if from_cache else ' — просканировано'))
        loaded = thumb_index.load()
        total_rows = sum(len(v) for v in thumb_index.by_name.values())
        db_size = os.path.getsize(index_db) / 1e6 if os.path.isfile(index_db) else 0
        stages.finish(f'в индексе {total_rows} файлов, {loaded} различных имён, '
                      f'база {index_db} ({db_size:.1f} МБ)'
                      + (' — просканировано сейчас' if scanned_now
                         else ' — взято из кэша SQLite'))

        # ---- Этап 3: сопоставление, без единой записи на диск ----
        stages.start('Сопоставление списков',
                     plural(total, 'снимок', 'снимка', 'снимков') + ' против '
                     + plural(len(thumb_index.by_name), 'имени', 'имён', 'имён')
                     + ' из ico')
        thumb_index.name_only_hits = 0
        work = plan_thumbnail_work(files, root_dir, thumbs_root,
                                   thumb_index, force_thumbs)
        if thumb_index.name_only_hits:
            stages.note(f'⚠️  у {thumb_index.name_only_hits} снимков миниатюра '
                        f'нашлась по имени, но не по структуре папок')
        stages.finish(f'уже на месте: {work["ready"]}, '
                      f'скопировать из внешней ico: {len(work["reusable"])}, '
                      f'создать: {work["todo"]}')

        # ---- Этап 4: копирование и создание ----
        if work['todo'] == 0 and not work['reusable']:
            stages.start('Создание миниатюр', 'ничего делать не нужно')
            stages.finish('все миниатюры уже готовы — этап пропущен')
        else:
            stages.start('Создание миниатюр',
                         f'скопировать {len(work["reusable"])}, '
                         f'создать {work["todo"]}; папка {thumbs_root}')
            thumbs, stats = build_thumbnails(
                files, root_dir, thumbs_root, thumb_size, url_base=out_dir,
                log=log, force=force_thumbs, thumb_index=thumb_index,
                stages=stages, work=work)
            stages.finish(f'создано {stats["created"]}, '
                          f'скопировано {stats["reused"]}, '
                          f'уже было {stats["skipped"]}, ошибок {stats["failed"]}')
        thumb_index.close()
    else:
        print('🖼️  Миниатюры отключены (--no-thumbs).')

    # ---- Этап: метаданные ----
    stages.start('Извлечение метаданных', f'{total} файлов, кэш '
                     + ('выключен' if no_cache else 'включён'))
    all_items = []
    date_sources = {}
    folder_dates = {}
    cache_path = os.path.join(out_dir, CACHE_FILE_NAME)
    cache = {} if no_cache else load_metadata_cache(cache_path)
    if cache:
        stages.note(f'в кэше {len(cache)} записей')
    new_cache = {}
    cache_hits = 0
    report = progress_printer('Метаданные', total)
    for index, path in enumerate(files, 1):
        rel_path = os.path.relpath(path, out_dir).replace('\\', '/')
        meta = None
        signature = None
        try:
            stat = os.stat(path)
            signature = (stat.st_size, stat.st_mtime_ns)
        except OSError:
            stat = None
        if signature and not no_cache:
            entry = cache.get(rel_path)
            if entry and len(entry) >= 2 and entry[0] == signature[0] \
                    and entry[1] == signature[1]:
                meta = cached_metadata(entry, rel_path)
                if meta is not None:
                    cache_hits += 1
        if meta is None:
            meta = get_metadata(path, log=log, root_dir=root_dir)
        elif meta.source == 'folder' and not meta.folder:
            # В кэше имя папки не хранится — восстанавливаем по пути, без
            # чтения файла: это две строковые операции.
            meta = meta._replace(folder=date_from_path(path, root_dir)[2])
        if signature:
            new_cache[rel_path] = [
                signature[0], signature[1], meta.lat, meta.lon,
                meta.timestamp.isoformat() if meta.timestamp else None, meta.source,
            ]
        date_sources[meta.source] = date_sources.get(meta.source, 0) + 1
        if meta.source == 'folder':
            folder_dates.setdefault(meta.folder, meta.timestamp)
        all_items.append({'lat': meta.lat, 'lon': meta.lon,
                          'timestamp': meta.timestamp, 'file': rel_path})
        report(index)

    if not no_cache:
        if save_metadata_cache(cache_path, new_cache):
            stages.note(f'кэш обновлён: {len(new_cache)} записей, '
                        f'без чтения файлов: {cache_hits}')
        else:
            print('⚠️  Не удалось сохранить кэш метаданных.')

    labels = {'exif': 'EXIF/XMP', 'folder': 'по папке', 'mtime': 'mtime', None: 'без даты'}
    summary = ', '.join(f'{labels.get(key, key)}: {value}'
                        for key, value in sorted(date_sources.items(),
                                                 key=lambda kv: str(kv[0])))
    if folder_dates:
        summary += '; папки: ' + ', '.join(
            f'{name} → {value:%Y-%m-%d}'
            for name, value in list(folder_dates.items())[:3])
    stages.finish(f'источники дат — {summary}')
    for name, value in folder_dates.items():
        log.info(f'Дата из папки: {name} -> {value:%Y-%m-%d}')

    # ---- Этап: группировка и запись JSON ----
    stages.start('Группировка по годам и запись JSON',
                 plural(total, 'точка', 'точки', 'точек'))
    by_year = defaultdict(list)
    for item in all_items:
        year = item['timestamp'].year if item['timestamp'] else 'unknown'
        by_year[year].append(item)

    print(f"📅 Обнаружено годов: {len(by_year)} "
          f"({', '.join(str(y) for y in sorted(by_year, key=str))})")

    written = []
    for year in sorted(by_year, key=str):
        items = by_year[year]
        items.sort(key=lambda item: item['timestamp'] or datetime.min)
        real = [item for item in items if item['lat'] is not None
                and item['lon'] is not None and item['timestamp'] is not None]
        no_gps = [item for item in items if item['lat'] is None or item['lon'] is None]

        fake_points = []
        threshold = timedelta(minutes=30)
        for item in no_gps:
            if item['timestamp'] is None:
                continue
            best, best_diff = None, threshold
            for gps_item in real:
                diff = abs(item['timestamp'] - gps_item['timestamp'])
                if diff < best_diff:
                    best, best_diff = gps_item, diff
            if best is not None:
                ratio = best_diff.total_seconds() / threshold.total_seconds()
                offset = 0.001 * max(ratio, 0.1)
                fake_points.append({
                    'lat': best['lat'] + random.uniform(-offset, offset),
                    'lon': best['lon'] + random.uniform(-offset, offset),
                    'timestamp': item['timestamp'], 'file': item['file'], 'fake': True,
                })

        points_out = []
        for item in items:
            if item['lat'] is not None and item['lon'] is not None:
                point = {
                    'lat': item['lat'], 'lon': item['lon'], 'file': item['file'],
                    'timestamp': item['timestamp'].isoformat() if item['timestamp'] else None,
                    'fake': False,
                }
                # Поле добавляется только при наличии миниатюры:
                # старые клиенты о нём не знают.
                if thumbs.get(item['file']):
                    point['thumb'] = thumbs[item['file']]
                points_out.append(point)
        # Сортировка до построения линий гарантирует последовательность
        # псевдопутей по времени.
        for point in fake_points:
            entry = {
                'lat': point['lat'], 'lon': point['lon'], 'file': point['file'],
                'timestamp': point['timestamp'].isoformat(), 'fake': True,
            }
            if thumbs.get(point['file']):
                entry['thumb'] = thumbs[point['file']]
            points_out.append(entry)

        points_out.sort(key=lambda point: point['timestamp'] or '')
        paths = build_paths(points_out)

        output_file = os.path.join(out_dir, f'points_{year}.json')
        try:
            with open(output_file, 'w', encoding='utf-8') as file_obj:
                json.dump({'points': points_out, 'paths': paths}, file_obj,
                          ensure_ascii=False, indent=2)
        except OSError as exc:
            log.error(f'Не удалось записать {output_file}: {exc}')
            continue

        real_count = sum(not point['fake'] for point in points_out)
        fake_count = len(points_out) - real_count
        written.append((os.path.basename(output_file), real_count,
                        fake_count, len(paths)))
        print(f'  📁 {os.path.basename(output_file)}: {real_count} реальных + '
              f'{fake_count} фейковых точек, {len(paths)} путей')
    stages.finish(f'файлов JSON: {len(written)}')

    elapsed = (datetime.now() - started).total_seconds()
    print('\n✅ Готово!')
    if test_limit:
        copied = copy_viewer_files(out_dir)
        print(f'🧪 Результаты пробного прогона: {out_dir}')
        if copied:
            print(f'   Откройте http://localhost:8000/{TEST_DIR_NAME}/map.html — '
                  f'сервер запускайте из {root_dir}')
    else:
        print('   Откройте map.html через локальный сервер.')
    if make_thumbs:
        print(f'🖼️  Миниатюры: {thumbs_root}')
    stages.summary()
    print(f'📝 Лог: {log.path} (ошибок: {log.errors}, '
          f'предупреждений: {log.warnings})')
    log.info(f'Итог: файлов {total}, ошибок {log.errors}, '
             f'предупреждений {log.warnings}, время {elapsed:.1f} с')
    log.close()
    return 0


def parse_args(argv):
    parser = argparse.ArgumentParser(
        description='Сканирует фотографии, строит фото-карту и псевдопути.')
    parser.add_argument('root', nargs='?', default=None,
                        help=f'папка с фотографиями (по умолчанию — {DEFAULT_PHOTO_DIR})')
    parser.add_argument('--thumbs-dir', default=None,
                        help=f'папка для миниатюр (по умолчанию <root>/{THUMB_DIR_NAME})')
    parser.add_argument('--thumb-size', type=int, default=THUMB_MAX_SIZE,
                        help='максимальный размер миниатюры по ширине и высоте, px')
    parser.add_argument('--no-thumbs', action='store_true',
                        help='не создавать миниатюры')
    parser.add_argument('--force-thumbs', action='store_true',
                        help='пересоздать миниатюры, даже если файлы уже есть')
    parser.add_argument('--no-cache', action='store_true',
                        help='не использовать кэш метаданных (перечитать EXIF у всех файлов)')
    parser.add_argument('--thumbs-source', action='append', default=None,
                        metavar='ПАПКА',
                        help='дополнительная папка с готовыми миниатюрами '
                             '(можно несколько раз); по умолчанию '
                             f'{DEFAULT_THUMB_SOURCE_DIR}')
    parser.add_argument('--rescan-thumbs', action='store_true',
                        help='заново просканировать внешние папки ico, '
                             'не доверяя индексу SQLite')
    parser.add_argument('--log', default=None, metavar='ФАЙЛ',
                        help=f'файл журнала (по умолчанию <root>/{LOG_FILE_NAME})')
    parser.add_argument('--test', nargs='?', type=int, const=TEST_FILE_LIMIT,
                        default=None, metavar='N',
                        help=f'пробный прогон на N файлах (по умолчанию {TEST_FILE_LIMIT}); '
                             f'результаты и лог — в {TEST_DIR_NAME}/, '
                             f'боевые JSON и миниатюры не трогаются')
    return parser.parse_args(argv)


if __name__ == '__main__':
    _configure_console()
    args = parse_args(sys.argv[1:])
    sys.exit(main(args.root, thumbs_dir=args.thumbs_dir, thumb_size=args.thumb_size,
                  make_thumbs=not args.no_thumbs, log_path=args.log,
                  force_thumbs=args.force_thumbs, test_limit=args.test,
                  no_cache=args.no_cache, thumb_sources=args.thumbs_source,
                  rescan_thumbs=args.rescan_thumbs) or 0)
