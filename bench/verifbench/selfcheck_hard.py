"""GOOD / BUGGY solutions for the hard suite (merged into selfcheck). Each BUGGY one is a
mistake an agent plausibly makes on that task."""

GOOD = {
    "days_between": """
def days_between(y1, m1, d1, y2, m2, d2):
    def leap(y): return y % 4 == 0 and (y % 100 != 0 or y % 400 == 0)
    cum = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
    def days(y, m, d):
        p = y - 1
        return p * 365 + p // 4 - p // 100 + p // 400 + cum[m - 1] + (m > 2 and leap(y)) + d
    return days(y2, m2, d2) - days(y1, m1, d1)
""",
    "utf8_valid": """
def utf8_valid(bs):
    i, n = 0, len(bs)
    while i < n:
        b = bs[i]
        if b < 0x80: i += 1; continue
        if 0xC2 <= b <= 0xDF: k, lo, hi = 1, 0x80, 0xBF
        elif b == 0xE0: k, lo, hi = 2, 0xA0, 0xBF
        elif 0xE1 <= b <= 0xEC or 0xEE <= b <= 0xEF: k, lo, hi = 2, 0x80, 0xBF
        elif b == 0xED: k, lo, hi = 2, 0x80, 0x9F
        elif b == 0xF0: k, lo, hi = 3, 0x90, 0xBF
        elif 0xF1 <= b <= 0xF3: k, lo, hi = 3, 0x80, 0xBF
        elif b == 0xF4: k, lo, hi = 3, 0x80, 0x8F
        else: return False
        if i + k >= n or not lo <= bs[i + 1] <= hi: return False
        if any(not 0x80 <= bs[j] <= 0xBF for j in range(i + 2, i + k + 1)): return False
        i += k + 1
    return True
""",
    "glob_match": """
def glob_match(pattern, text):
    toks, i = [], 0
    while i < len(pattern):
        c = pattern[i]
        if c == '\\\\': toks.append(('lit', pattern[i + 1] if i + 1 < len(pattern) else '\\\\')); i += 2
        elif c == '*': toks.append(('star', None)); i += 1
        elif c == '?': toks.append(('any', None)); i += 1
        else: toks.append(('lit', c)); i += 1
    m = len(text)
    dp = [True] + [False] * m
    for kind, ch in toks:
        nd = [False] * (m + 1)
        if kind == 'star':
            acc = False
            for j in range(m + 1):
                acc = acc or dp[j]; nd[j] = acc
        else:
            for j in range(1, m + 1):
                nd[j] = dp[j - 1] and (kind == 'any' or text[j - 1] == ch)
        dp = nd
    return dp[m]
""",
    "lru_cache": """
def lru_cache(capacity, ops):
    order, vals, out = [], {}, []
    for kind, k, v in ops:
        if kind == 0:
            if k in vals: order.remove(k); order.append(k); out.append(vals[k])
            else: out.append(-1)
        else:
            if k in vals: order.remove(k)
            elif len(vals) == capacity: del vals[order.pop(0)]
            vals[k] = v; order.append(k)
    return out
""",
    "topo_sort": """
import heapq
def topo_sort(n, edges):
    indeg = [0] * n; adj = [[] for _ in range(n)]
    for u, v in edges: adj[u].append(v); indeg[v] += 1
    h = [i for i in range(n) if indeg[i] == 0]; heapq.heapify(h); out = []
    while h:
        u = heapq.heappop(h); out.append(u)
        for v in adj[u]:
            indeg[v] -= 1
            if indeg[v] == 0: heapq.heappush(h, v)
    return out if len(out) == n else []
""",
    "justify": """
def justify(words, width):
    lines, i = [], 0
    while i < len(words):
        j, ln = i + 1, len(words[i])
        while j < len(words) and ln + 1 + len(words[j]) <= width: ln += 1 + len(words[j]); j += 1
        ws = words[i:j]
        if j == len(words) or len(ws) == 1:
            s = ' '.join(ws); lines.append(s.ljust(width))
        else:
            gaps = len(ws) - 1; q, r = divmod(width - sum(map(len, ws)), gaps)
            lines.append(''.join(w + ' ' * (q + (k < r)) for k, w in enumerate(ws[:-1])) + ws[-1])
        i = j
    return lines
""",
    "add_big": """
def add_big(a, b):
    return str(int(a) + int(b))
""",
    "normalize_path": """
def normalize_path(p):
    absolute = p.startswith('/'); st = []
    for c in p.split('/'):
        if c in ('', '.'): continue
        if c == '..':
            if st and st[-1] != '..': st.pop()
            elif not absolute: st.append('..')
        else: st.append(c)
    return '/' + '/'.join(st) if absolute else ('/'.join(st) or '.')
""",
}

BUGGY = {
    "days_between": """
def days_between(y1, m1, d1, y2, m2, d2):   # leap rule ignores the 100/400 exceptions
    def leap(y): return y % 4 == 0
    cum = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
    def days(y, m, d):
        p = y - 1
        return p * 365 + p // 4 + cum[m - 1] + (m > 2 and leap(y)) + d
    return days(y2, m2, d2) - days(y1, m1, d1)
""",
    "utf8_valid": """
def utf8_valid(bs):                          # checks bit patterns only: accepts overlongs/surrogates
    i, n = 0, len(bs)
    while i < n:
        b = bs[i]
        if b >> 7 == 0: k = 0
        elif b >> 5 == 6: k = 1
        elif b >> 4 == 14: k = 2
        elif b >> 3 == 30: k = 3
        else: return False
        if i + k >= n: return False
        if any(bs[j] >> 6 != 2 for j in range(i + 1, i + k + 1)): return False
        i += k + 1
    return True
""",
    "glob_match": """
def glob_match(pattern, text):               # no escape handling: backslash is an ordinary char
    m = len(text)
    dp = [True] + [False] * m
    for c in pattern:
        nd = [False] * (m + 1)
        if c == '*':
            acc = False
            for j in range(m + 1):
                acc = acc or dp[j]; nd[j] = acc
        else:
            for j in range(1, m + 1):
                nd[j] = dp[j - 1] and (c == '?' or text[j - 1] == c)
        dp = nd
    return dp[m]
""",
    "lru_cache": """
from collections import OrderedDict
def lru_cache(capacity, ops):                # updating an existing key does not refresh recency
    c, out = OrderedDict(), []
    for kind, k, v in ops:
        if kind == 0:
            if k in c: c.move_to_end(k); out.append(c[k])
            else: out.append(-1)
        else:
            if k in c: c[k] = v
            else:
                if len(c) == capacity: c.popitem(last=False)
                c[k] = v
    return out
""",
    "topo_sort": """
from collections import deque
def topo_sort(n, edges):                     # FIFO queue: valid order, but not the smallest
    indeg = [0] * n; adj = [[] for _ in range(n)]
    for u, v in edges: adj[u].append(v); indeg[v] += 1
    q = deque(i for i in range(n) if indeg[i] == 0); out = []
    while q:
        u = q.popleft(); out.append(u)
        for v in sorted(adj[u]):
            indeg[v] -= 1
            if indeg[v] == 0: q.append(v)
    return out if len(out) == n else []
""",
    "justify": """
def justify(words, width):                   # extra spaces go to the RIGHTMOST gaps
    lines, i = [], 0
    while i < len(words):
        j, ln = i + 1, len(words[i])
        while j < len(words) and ln + 1 + len(words[j]) <= width: ln += 1 + len(words[j]); j += 1
        ws = words[i:j]
        if j == len(words) or len(ws) == 1:
            lines.append(' '.join(ws).ljust(width))
        else:
            gaps = len(ws) - 1; q, r = divmod(width - sum(map(len, ws)), gaps)
            lines.append(''.join(w + ' ' * (q + (k >= gaps - r)) for k, w in enumerate(ws[:-1])) + ws[-1])
        i = j
    return lines
""",
    "add_big": """
def add_big(a, b):                           # manual subtraction keeps leading zeros
    x, y = int(a), int(b)
    if (x < 0) == (y < 0): return str(x + y)
    big, small = (x, y) if abs(x) >= abs(y) else (y, x)
    da = str(abs(big)); db = str(abs(small)).rjust(len(da), '0')
    res, borrow = [], 0
    for p, q in zip(reversed(da), reversed(db)):
        d = int(p) - int(q) - borrow; borrow = d < 0; res.append(str(d + 10 if d < 0 else d))
    return ('-' if big < 0 else '') + ''.join(reversed(res))
""",
    "normalize_path": """
def normalize_path(p):                       # treats relative '..' like absolute: drops it
    absolute = p.startswith('/'); st = []
    for c in p.split('/'):
        if c in ('', '.'): continue
        if c == '..':
            if st: st.pop()
        else: st.append(c)
    return '/' + '/'.join(st) if absolute else ('/'.join(st) or '.')
""",
}
