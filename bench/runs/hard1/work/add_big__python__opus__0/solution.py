def _cmp_abs(x: str, y: str) -> int:
    if len(x) != len(y):
        return 1 if len(x) > len(y) else -1
    if x == y:
        return 0
    return 1 if x > y else -1


def _add_abs(x: str, y: str) -> str:
    i, j = len(x) - 1, len(y) - 1
    carry = 0
    out = []
    while i >= 0 or j >= 0 or carry:
        s = carry
        if i >= 0:
            s += ord(x[i]) - 48
            i -= 1
        if j >= 0:
            s += ord(y[j]) - 48
            j -= 1
        out.append(chr(48 + s % 10))
        carry = s // 10
    return "".join(reversed(out)) or "0"


def _sub_abs(x: str, y: str) -> str:
    # requires |x| >= |y|
    i, j = len(x) - 1, len(y) - 1
    borrow = 0
    out = []
    while i >= 0:
        d = ord(x[i]) - 48 - borrow
        if j >= 0:
            d -= ord(y[j]) - 48
            j -= 1
        if d < 0:
            d += 10
            borrow = 1
        else:
            borrow = 0
        out.append(chr(48 + d))
        i -= 1
    res = "".join(reversed(out)).lstrip("0")
    return res or "0"


def add_big(a: str, b: str) -> str:
    neg_a = a.startswith("-")
    neg_b = b.startswith("-")
    x = a[1:] if neg_a else a
    y = b[1:] if neg_b else b
    if neg_a == neg_b:
        res = _add_abs(x, y)
        neg = neg_a
    else:
        c = _cmp_abs(x, y)
        if c == 0:
            return "0"
        if c > 0:
            res = _sub_abs(x, y)
            neg = neg_a
        else:
            res = _sub_abs(y, x)
            neg = neg_b
    if res == "0":
        return "0"
    return "-" + res if neg else res
