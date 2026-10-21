def _days_from_civil(y: int, m: int, d: int) -> int:
    # Howard Hinnant's algorithm: days since 1970-01-01 in proleptic Gregorian.
    if m <= 2:
        y -= 1
    era = y // 400
    yoe = y - era * 400
    mp = (m + 9) % 12
    doy = (153 * mp + 2) // 5 + d - 1
    doe = yoe * 365 + yoe // 4 - yoe // 100 + doy
    return era * 146097 + doe - 719468


def days_between(y1: int, m1: int, d1: int, y2: int, m2: int, d2: int) -> int:
    return _days_from_civil(y2, m2, d2) - _days_from_civil(y1, m1, d1)
