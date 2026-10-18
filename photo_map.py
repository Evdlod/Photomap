import argparse
import json
import os
import random
import re
import shutil
import sys
from collections import defaultdict
from datetime import datetime, timedelta

from PIL import Image, ImageOps

# Внимание: отключение лимита разрешено для доверенных панорам, но повышает
# риск чрезмерного расхода памяти на повреждённых/вредоносных файлах.
Image.MAX_IMAGE_PIXELS = None

EXTENSIONS = ('.jpg', '.jpeg', '.tif', '.tiff', '.webp', '.png', '.heic', '.heif')
MAX_PATH_GAP = timedelta(hours=1)
MAX_PATH_DISTANCE_M = 1000.0

# Миниатюры: папка рядом с данными, максимальный размер по ширине и высоте.
THUMB_DIR_NAME = 'ico'
THUMB_MAX_SIZE = 240
THUMB_QUALITY = 85

# Журнал ошибок и пробный прогон.
LOG_FILE_NAME = 'photo_map.log'
TEST_DIR_NAME = 'test_run'
TEST_FILE_LIMIT = 1000
PROGRESS_STEP = 5          # шаг вывода прогресса, процентов
LOG_CONSOLE_LIMIT = 5      # сколько первых ошибок дублировать в консоль
SKIP_NOTICE_STEP = 500     # через сколько пропущенных миниатюр сообщать о них

# Папка, которая сканируется, если путь не передан аргументом.
DEFAULT_PHOTO_DIR = r'D:\YandexDisk\Альбомы по годам'


def _configure_console():
    """Переводит консоль в UTF-8, чтобы эмодзи не ломали вывод на Windows."""
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding='utf-8', errors='replace')
        except (AttributeError, ValueError, OSError):
            pass


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


def progress_printer(label, total, step=PROGRESS_STEP):
    """Возвращает функцию: печатает прогресс шагами по step% от ожидаемого объёма.

    Шаг считается от предполагаемого количества (total), поэтому для 1000 файлов
    строка появляется каждые 50 файлов: 5%, 10%, …, 100%.
    """
    every = max(1, int(round(total * step / 100)))
    printed = 0

    def report(index):
        nonlocal printed
        if (index % every == 0 or index >= total) and index != printed:
            printed = index
            percent = min(100, round(index * 100 / total))
            print(f'⏳ {label}: {percent}% ({index} из {total})')

    return report


def register_heic_support():
    """Подключает pillow-heif, если он установлен. Иначе HEIC/HEIF не декодируются."""
    try:
        import pillow_heif
    except ImportError:
        return False
    pillow_heif.register_heif_opener()
    return True


def collect_images(root_dir, excluded_dirs):
    """Собирает изображения, не заходя в папки миниатюр и пробных прогонов."""
    files = []
    for dirpath, dirnames, filenames in os.walk(root_dir):
        dirnames[:] = [
            name for name in dirnames
            if os.path.abspath(os.path.join(dirpath, name)) not in excluded_dirs
        ]
        for filename in filenames:
            if filename.lower().endswith(EXTENSIONS):
                files.append(os.path.join(dirpath, filename))
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
    """Парсит стандартную EXIF-дату вида '2023:05:15 14:30:00'."""
    if not value:
        return None
    if isinstance(value, bytes):
        value = value.decode('utf-8', errors='ignore')
    value = str(value).strip().strip('\x00')
    try:
        return datetime.strptime(value, '%Y:%m:%d %H:%M:%S')
    except ValueError:
        return None


def get_metadata(path, log=None):
    """Возвращает (широта, долгота, дата); отсутствующие значения равны None."""
    log = log or DEFAULT_LOG
    lat = lon = timestamp = None
    try:
        with Image.open(path) as img:
            exif = img.getexif()
            for tag_id in (0x9003, 0x9004, 0x0132):
                timestamp = parse_exif_datetime(exif.get(tag_id))
                if timestamp:
                    break

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

    if timestamp is None:
        try:
            timestamp = datetime.fromtimestamp(os.path.getmtime(path))
        except OSError:
            pass
    return lat, lon, timestamp


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


def build_thumbnails(files, root_dir, thumbs_root, thumb_size,
                     url_base=None, log=None, force=False):
    """Создаёт недостающие миниатюры.

    Возвращает ({исходный файл: путь миниатюры для JSON}, статистику по статусам).
    Готовые миниатюры не пересоздаются, но всё равно попадают в результат,
    чтобы поле thumb было в JSON и после повторного запуска.
    """
    log = log or DEFAULT_LOG
    url_base = url_base or root_dir
    try:
        url_prefix = os.path.relpath(thumbs_root, url_base).replace('\\', '/')
    except ValueError:
        # Windows: папка миниатюр на другом диске, относительную ссылку не построить.
        log.warning(f'Папка миниатюр {thumbs_root} на другом диске: '
                    f'ссылки в JSON будут указывать на {THUMB_DIR_NAME}/')
        url_prefix = THUMB_DIR_NAME
    if url_prefix == '.':
        url_prefix = ''

    plan = plan_thumbnails(files, root_dir)
    print(f'🖼️  Миниатюры (не более {thumb_size} px) в {thumbs_root}')
    report = progress_printer('Миниатюры', len(plan))
    result = {}
    stats = {'created': 0, 'skipped': 0, 'failed': 0}
    for index, (path, rel_thumb) in enumerate(plan.items(), 1):
        dest = os.path.join(thumbs_root, *rel_thumb.split('/'))
        status = make_thumbnail(path, dest, thumb_size, log=log, force=force)
        stats[status] += 1
        if status == 'skipped' and stats['skipped'] % SKIP_NOTICE_STEP == 0:
            note = (f'Пропущено уже готовых миниатюр: {stats["skipped"]} '
                    f'(не пересоздаются)')
            print(f'♻️  {note}')
            log.info(note)
        if status != 'failed':
            # Ключ совпадает с полем file в JSON: оба считаются от url_base.
            rel_file = os.path.relpath(path, url_base).replace('\\', '/')
            result[rel_file] = f'{url_prefix}/{rel_thumb}' if url_prefix else rel_thumb
        report(index)
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
         log_path=None, force_thumbs=False, test_limit=None):
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

    print('🔍 Подсчет файлов...')
    files = collect_images(root_dir, excluded_dirs)
    found = len(files)
    print(f'📸 Найдено изображений: {found}')
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
    if make_thumbs:
        thumbs, stats = build_thumbnails(files, root_dir, thumbs_root, thumb_size,
                                         url_base=out_dir, log=log, force=force_thumbs)
        summary = (f'создано {stats["created"]}, уже были {stats["skipped"]}, '
                   f'ошибок {stats["failed"]}')
        print(f'🖼️  Миниатюры: {summary}')
        log.info(f'Миниатюры: {summary}')
    else:
        print('🖼️  Миниатюры отключены (--no-thumbs).')

    print('⚙️ Извлечение метаданных...')
    all_items = []
    report = progress_printer('Метаданные', total)
    for index, path in enumerate(files, 1):
        lat, lon, timestamp = get_metadata(path, log=log)
        rel_path = os.path.relpath(path, out_dir).replace('\\', '/')
        all_items.append({'lat': lat, 'lon': lon, 'timestamp': timestamp, 'file': rel_path})
        report(index)

    by_year = defaultdict(list)
    for item in all_items:
        year = item['timestamp'].year if item['timestamp'] else 'unknown'
        by_year[year].append(item)

    print(f"📅 Обнаружено годов: {len(by_year)} "
          f"({', '.join(str(y) for y in sorted(by_year, key=str))})")

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
                # Поле добавляется только при наличии миниатюры: старые клиенты его не знают.
                if thumbs.get(item['file']):
                    point['thumb'] = thumbs[item['file']]
                points_out.append(point)
        for point in fake_points:
            entry = {
                'lat': point['lat'], 'lon': point['lon'], 'file': point['file'],
                'timestamp': point['timestamp'].isoformat(), 'fake': True,
            }
            if thumbs.get(point['file']):
                entry['thumb'] = thumbs[point['file']]
            points_out.append(entry)

        # Сортировка до построения линий гарантирует последовательность по времени.
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
        print(f'  📁 {os.path.basename(output_file)}: {real_count} реальных + '
              f'{fake_count} фейковых точек, {len(paths)} путей')

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
    print(f'📝 Лог: {log.path} (ошибок: {log.errors}, предупреждений: {log.warnings})')
    log.info(f'Итог: файлов {total}, ошибок {log.errors}, '
             f'предупреждений {log.warnings}, время {elapsed:.1f} с')
    log.close()


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
                  force_thumbs=args.force_thumbs, test_limit=args.test) or 0)
