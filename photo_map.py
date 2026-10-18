import json
import os
import random
import re
import sys
from collections import defaultdict
from datetime import datetime, timedelta

from PIL import Image

# Внимание: отключение лимита разрешено для доверенных панорам, но повышает
# риск чрезмерного расхода памяти на повреждённых/вредоносных файлах.
Image.MAX_IMAGE_PIXELS = None

EXTENSIONS = ('.jpg', '.jpeg', '.tif', '.tiff', '.webp', '.png', '.heic', '.heif')
MAX_PATH_GAP = timedelta(hours=1)
MAX_PATH_DISTANCE_M = 1000.0


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


def get_metadata(path):
    """Возвращает (широта, долгота, дата); отсутствующие значения равны None."""
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
        print(f'⚠️ Не удалось прочитать метаданные {path}: {exc}', file=sys.stderr)

    if timestamp is None:
        try:
            timestamp = datetime.fromtimestamp(os.path.getmtime(path))
        except OSError:
            pass
    return lat, lon, timestamp


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


def main(root_dir='.'):
    root_dir = os.path.abspath(root_dir)
    print('🔍 Подсчет файлов...')
    files = []
    for dirpath, _, filenames in os.walk(root_dir):
        for filename in filenames:
            if filename.lower().endswith(EXTENSIONS):
                files.append(os.path.join(dirpath, filename))
    files.sort()

    total = len(files)
    print(f'📸 Найдено изображений: {total}')
    if not total:
        print('Изображения не найдены; JSON-файлы не созданы.')
        return

    print('⚙️ Извлечение метаданных...')
    all_items = []
    milestones = {max(1, int(total * p / 100)) for p in range(10, 101, 10)}
    for i, path in enumerate(files, 1):
        if i in milestones:
            print(f'⏳ Прогресс: {int(i / total * 100)}%')
        lat, lon, timestamp = get_metadata(path)
        rel_path = os.path.relpath(path, root_dir).replace('\\', '/')
        all_items.append({'lat': lat, 'lon': lon, 'timestamp': timestamp, 'file': rel_path})

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
                points_out.append({
                    'lat': item['lat'], 'lon': item['lon'], 'file': item['file'],
                    'timestamp': item['timestamp'].isoformat() if item['timestamp'] else None,
                    'fake': False,
                })
        for point in fake_points:
            points_out.append({
                'lat': point['lat'], 'lon': point['lon'], 'file': point['file'],
                'timestamp': point['timestamp'].isoformat(), 'fake': True,
            })

        # Сортировка до построения линий гарантирует последовательность по времени.
        points_out.sort(key=lambda point: point['timestamp'] or '')
        paths = build_paths(points_out)

        output_file = os.path.join(root_dir, f'points_{year}.json')
        with open(output_file, 'w', encoding='utf-8') as file_obj:
            json.dump({'points': points_out, 'paths': paths}, file_obj,
                      ensure_ascii=False, indent=2)

        real_count = sum(not point['fake'] for point in points_out)
        fake_count = len(points_out) - real_count
        print(f'  📁 {os.path.basename(output_file)}: {real_count} реальных + '
              f'{fake_count} фейковых точек, {len(paths)} путей')

    print('\n✅ Готово! Откройте map.html через локальный сервер.')


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else '.')
