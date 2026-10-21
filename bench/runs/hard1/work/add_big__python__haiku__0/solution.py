def add_big(a: str, b: str) -> str:
    a_negative = a.startswith('-')
    b_negative = b.startswith('-')

    a_abs = a[1:] if a_negative else a
    b_abs = b[1:] if b_negative else b

    if a_negative == b_negative:
        result = _add_positive(a_abs, b_abs)
        if result == '0':
            return '0'
        if a_negative:
            return '-' + result
        return result

    cmp = _compare_positive(a_abs, b_abs)

    if cmp > 0:
        result = _subtract_positive(a_abs, b_abs)
        if result == '0':
            return '0'
        if a_negative:
            return '-' + result
        return result
    elif cmp < 0:
        result = _subtract_positive(b_abs, a_abs)
        if result == '0':
            return '0'
        if b_negative:
            return '-' + result
        return result
    else:
        return '0'


def _add_positive(a: str, b: str) -> str:
    result = []
    carry = 0
    i = len(a) - 1
    j = len(b) - 1

    while i >= 0 or j >= 0 or carry:
        digit_a = int(a[i]) if i >= 0 else 0
        digit_b = int(b[j]) if j >= 0 else 0

        total = digit_a + digit_b + carry
        result.append(str(total % 10))
        carry = total // 10

        i -= 1
        j -= 1

    return ''.join(reversed(result))


def _subtract_positive(a: str, b: str) -> str:
    result = []
    borrow = 0
    i = len(a) - 1
    j = len(b) - 1

    while i >= 0:
        digit_a = int(a[i])
        digit_b = int(b[j]) if j >= 0 else 0

        diff = digit_a - digit_b - borrow
        if diff < 0:
            diff += 10
            borrow = 1
        else:
            borrow = 0

        result.append(str(diff))
        i -= 1
        j -= 1

    result_str = ''.join(reversed(result)).lstrip('0')
    return result_str if result_str else '0'


def _compare_positive(a: str, b: str) -> int:
    if len(a) > len(b):
        return 1
    elif len(a) < len(b):
        return -1
    else:
        if a > b:
            return 1
        elif a == b:
            return 0
        else:
            return -1
