def parse_int(s: str) -> tuple[bool, int]:
    if not isinstance(s, str):
        return (False, 0)
    i = 0
    neg = False
    if s and s[0] in "+-":
        neg = s[0] == "-"
        i = 1
    digits = s[i:]
    if not digits:
        return (False, 0)
    value = 0
    for ch in digits:
        if not ("0" <= ch <= "9"):
            return (False, 0)
        value = value * 10 + (ord(ch) - 48)
    if neg:
        value = -value
    if value < -2147483648 or value > 2147483647:
        return (False, 0)
    return (True, value)
