def utf8_valid(bs: list[int]) -> bool:
    n = len(bs)
    i = 0
    while i < n:
        b = bs[i]
        if not isinstance(b, int) or b < 0 or b > 255:
            return False
        if b < 0x80:
            i += 1
            continue
        if 0xC2 <= b <= 0xDF:
            length, lo, hi = 2, 0x80, 0xBF
        elif b == 0xE0:
            length, lo, hi = 3, 0xA0, 0xBF
        elif 0xE1 <= b <= 0xEC or 0xEE <= b <= 0xEF:
            length, lo, hi = 3, 0x80, 0xBF
        elif b == 0xED:
            length, lo, hi = 3, 0x80, 0x9F
        elif b == 0xF0:
            length, lo, hi = 4, 0x90, 0xBF
        elif 0xF1 <= b <= 0xF3:
            length, lo, hi = 4, 0x80, 0xBF
        elif b == 0xF4:
            length, lo, hi = 4, 0x80, 0x8F
        else:
            return False
        if i + length > n:
            return False
        c = bs[i + 1]
        if not isinstance(c, int) or not (lo <= c <= hi):
            return False
        for j in range(i + 2, i + length):
            c = bs[j]
            if not isinstance(c, int) or not (0x80 <= c <= 0xBF):
                return False
        i += length
    return True
