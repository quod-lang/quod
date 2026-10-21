"""Suite "hard": tasks chosen because LLMs classically stumble on them
(calendar rules, UTF-8 corner cases, escaping, recency bookkeeping, tie-breaking,
spacing distribution, borrow/zero formatting, path edge cases)."""
from __future__ import annotations

import calendar
import heapq
import random
import re
from collections import OrderedDict
from datetime import date

from verifbench.tasks import Task

# --- 1. days_between --------------------------------------------------------

def _days_oracle(y1, m1, d1, y2, m2, d2):
    return date(y2, m2, d2).toordinal() - date(y1, m1, d1).toordinal()


def _rand_date(r: random.Random) -> tuple[int, int, int]:
    y = r.choice([1600, 1700, 1800, 1900, 2000, 2100, 2400, 2024, 2023]) + r.randint(-1, 1) \
        if r.random() < 0.6 else r.randint(1, 9999)
    y = min(max(y, 1), 9999)
    m = r.choice([1, 2, 2, 3, 12]) if r.random() < 0.5 else r.randint(1, 12)
    last = calendar.monthrange(y, m)[1]
    d = r.choice([1, last]) if r.random() < 0.5 else r.randint(1, last)
    return (y, m, d)


def _days_rand(r: random.Random) -> tuple:
    a = _rand_date(r)
    if r.random() < 0.5:  # nearby second date: stresses month/leap transitions
        o = date(*a).toordinal() + r.randint(-400, 400)
        o = min(max(o, 1), date(9999, 12, 31).toordinal())
        b = date.fromordinal(o)
        return a + (b.year, b.month, b.day)
    return a + _rand_date(r)


# --- 2. utf8_valid ----------------------------------------------------------

def _utf8_oracle(bs):
    try:
        bytes(bs).decode("utf-8")  # CPython's strict decoder: no overlongs/surrogates/>U+10FFFF
        return True
    except UnicodeDecodeError:
        return False


_UTF8_TRAPS = [[0xC0, 0x80], [0xC1, 0xBF], [0xE0, 0x80, 0x80], [0xE0, 0x9F, 0xBF],
               [0xED, 0xA0, 0x80], [0xED, 0xBF, 0xBF], [0xF0, 0x80, 0x80, 0x80],
               [0xF0, 0x8F, 0xBF, 0xBF], [0xF4, 0x90, 0x80, 0x80], [0xF5, 0x80, 0x80, 0x80],
               [0xFF], [0x80], [0xBF], [0xE2, 0x82], [0xF0, 0x9F, 0x98]]
_UTF8_BOUNDS = [0x7F, 0x80, 0x7FF, 0x800, 0xD7FF, 0xE000, 0xFFFF, 0x10000, 0x10FFFF]


def _utf8_rand(r: random.Random) -> tuple:
    out: list[int] = []
    for _ in range(r.randint(0, 4)):
        roll = r.random()
        if roll < 0.3:
            cp = r.choice(_UTF8_BOUNDS)
        else:
            lo, hi = r.choice([(0, 0x7F), (0x80, 0x7FF), (0x800, 0xD7FF), (0xE000, 0xFFFF),
                               (0x10000, 0x10FFFF)])
            cp = r.randint(lo, hi)
        out += list(chr(cp).encode("utf-8"))
    roll = r.random()
    if roll < 0.3:
        pos = r.randint(0, len(out))
        out[pos:pos] = r.choice(_UTF8_TRAPS)
    elif roll < 0.45 and out:
        out[r.randrange(len(out))] = r.randint(0, 255)
    elif roll < 0.55 and out:
        out = out[: r.randrange(len(out))]
    return (out,)


# --- 3. glob_match ----------------------------------------------------------

def _glob_oracle(pattern: str, text: str) -> bool:
    rx, i = [], 0
    while i < len(pattern):
        c = pattern[i]
        if c == "\\":
            rx.append(re.escape(pattern[i + 1] if i + 1 < len(pattern) else "\\"))
            i += 2
        elif c == "*":
            rx.append(".*")
            i += 1
        elif c == "?":
            rx.append(".")
            i += 1
        else:
            rx.append(re.escape(c))
            i += 1
    return re.fullmatch("".join(rx), text, re.DOTALL) is not None


_GLOB_TOKENS = ["a", "b", "a", "b", "?", "*", "*", "\\a", "\\*", "\\?", "\\\\"]


def _glob_rand(r: random.Random) -> tuple:
    toks = [r.choice(_GLOB_TOKENS) for _ in range(r.randint(0, 6))]
    if r.random() < 0.1:
        toks.append("\\")  # trailing lone backslash
    pattern = "".join(toks)
    if r.random() < 0.5:  # derive a matching text, then maybe perturb it
        parts = []
        for t in toks:
            if t == "*":
                parts.append("".join(r.choice("ab*?\\") for _ in range(r.randint(0, 3))))
            elif t == "?":
                parts.append(r.choice("ab*?\\"))
            else:
                parts.append(t[-1])
        text = "".join(parts)
        if text and r.random() < 0.4:
            i = r.randrange(len(text))
            text = text[:i] + r.choice("ab*?\\") + text[i + 1:]
    else:
        text = "".join(r.choice("ab*?\\") for _ in range(r.randint(0, 6)))
    return (pattern, text)


# --- 4. lru_cache -----------------------------------------------------------

def _lru_oracle(capacity, ops):
    c: OrderedDict[int, int] = OrderedDict()
    out = []
    for kind, k, v in ops:
        if kind == 0:
            if k in c:
                c.move_to_end(k)
                out.append(c[k])
            else:
                out.append(-1)
        else:
            if k in c:
                c.move_to_end(k)
            elif len(c) == capacity:
                c.popitem(last=False)
            c[k] = v
    return out


def _lru_rand(r: random.Random) -> tuple:
    ops = [(r.randint(0, 1), r.randint(0, 4), r.randint(0, 9)) for _ in range(r.randint(0, 30))]
    return (r.randint(1, 3), ops)


# --- 5. topo_sort -----------------------------------------------------------

def _topo_oracle(n, edges):
    indeg = [0] * n
    adj: list[list[int]] = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        indeg[v] += 1
    h = [i for i in range(n) if indeg[i] == 0]
    heapq.heapify(h)
    out = []
    while h:
        u = heapq.heappop(h)
        out.append(u)
        for v in adj[u]:
            indeg[v] -= 1
            if indeg[v] == 0:
                heapq.heappush(h, v)
    return out if len(out) == n else []


def _topo_rand(r: random.Random) -> tuple:
    n = r.randint(1, 8)
    perm = list(range(n))
    r.shuffle(perm)
    dag = r.random() < 0.7
    edges = []
    for _ in range(r.randint(0, 12)):
        u, v = r.randrange(n), r.randrange(n)
        if dag:
            if u == v:
                continue
            if perm.index(u) > perm.index(v):
                u, v = v, u
        edges.append((u, v))
    return (n, edges)


# --- 6. justify -------------------------------------------------------------

def _justify_oracle(words, width):
    lines, i = [], 0
    while i < len(words):
        j, ln = i + 1, len(words[i])
        while j < len(words) and ln + 1 + len(words[j]) <= width:
            ln += 1 + len(words[j])
            j += 1
        ws = words[i:j]
        if j == len(words) or len(ws) == 1:
            s = " ".join(ws)
            lines.append(s + " " * (width - len(s)))
        else:
            gaps = len(ws) - 1
            q, rem = divmod(width - sum(map(len, ws)), gaps)
            s = ""
            for k, w in enumerate(ws[:-1]):
                s += w + " " * (q + (1 if k < rem else 0))
            lines.append(s + ws[-1])
        i = j
    return lines


def _justify_rand(r: random.Random) -> tuple:
    width = r.randint(1, 16)
    words = ["".join(r.choice("abcxyz") for _ in range(r.randint(1, min(width, 6))))
             for _ in range(r.randint(0, 10))]
    return (words, width)


# --- 7. add_big -------------------------------------------------------------

def _add_oracle(a: str, b: str) -> str:
    return str(int(a) + int(b))


def _add_rand(r: random.Random) -> tuple:
    def big() -> int:
        v = r.randint(0, 10 ** r.randint(1, 30))
        if r.random() < 0.2:
            v = 10 ** r.randint(1, 25) + r.choice([-1, 0, 1])  # carry/borrow chains
        return -v if r.random() < 0.5 else v
    a = big()
    b = -a + r.randint(-3, 3) if r.random() < 0.3 else big()
    return (str(a), str(b))


# --- 8. normalize_path ------------------------------------------------------

def _path_oracle(p: str) -> str:
    absolute = p.startswith("/")
    st: list[str] = []
    for c in p.split("/"):
        if c in ("", "."):
            continue
        if c == "..":
            if st and st[-1] != "..":
                st.pop()
            elif not absolute:
                st.append("..")
        else:
            st.append(c)
    if absolute:
        return "/" + "/".join(st)
    return "/".join(st) or "."


def _path_rand(r: random.Random) -> tuple:
    comps = [r.choice(["a", "b", "..", "..", ".", "", "...", ".a", "a.."])
             for _ in range(r.randint(0, 7))]
    p = "/".join(comps)
    if r.random() < 0.5:
        p = "/" + p
    return (p,)


HARD_TASKS = [
    Task(
        id="days_between", func="days_between", suite="hard",
        spec=(
            "Given two valid dates (y1, m1, d1) and (y2, m2, d2) in the proleptic Gregorian "
            "calendar with years 1 to 9999, return the number of days from the first date to "
            "the second (negative if the second date is earlier, 0 if equal). A year is a leap "
            "year if divisible by 4, except years divisible by 100 that are not divisible by 400."
        ),
        py_signature="def days_between(y1: int, m1: int, d1: int, y2: int, m2: int, d2: int) -> int",
        dfy_signature="method days_between(y1: int, m1: int, d1: int, y2: int, m2: int, d2: int) returns (n: int)",
        oracle=_days_oracle,
        edge_cases=[(2000, 2, 28, 2000, 3, 1), (1900, 2, 28, 1900, 3, 1), (2024, 1, 1, 2023, 12, 31),
                    (1, 1, 1, 9999, 12, 31), (2000, 2, 29, 2001, 2, 28), (2023, 5, 5, 2023, 5, 5),
                    (2100, 2, 28, 2100, 3, 1), (1600, 12, 31, 1601, 1, 1)],
        random_case=_days_rand,
    ),
    Task(
        id="utf8_valid", func="utf8_valid", suite="hard",
        spec=(
            "Given a list of integers each in 0..255 (a byte string), return True iff it is "
            "well-formed UTF-8 as defined by RFC 3629 / the Unicode standard: every character "
            "uses its shortest encoding (no overlong forms), no code point exceeds U+10FFFF, no "
            "surrogate code points U+D800..U+DFFF are encoded, and no sequence is truncated or "
            "has an invalid continuation byte. The empty list is valid."
        ),
        py_signature="def utf8_valid(bs: list[int]) -> bool",
        dfy_signature="method utf8_valid(bs: seq<int>) returns (b: bool)",
        oracle=_utf8_oracle,
        edge_cases=[([],), ([0],), ([0x7F],), ([0xC2, 0x80],), ([0xC0, 0x80],), ([0xC1, 0xBF],),
                    ([0xE0, 0xA0, 0x80],), ([0xE0, 0x9F, 0xBF],), ([0xED, 0x9F, 0xBF],),
                    ([0xED, 0xA0, 0x80],), ([0xEF, 0xBF, 0xBF],), ([0xF0, 0x90, 0x80, 0x80],),
                    ([0xF0, 0x8F, 0xBF, 0xBF],), ([0xF4, 0x8F, 0xBF, 0xBF],),
                    ([0xF4, 0x90, 0x80, 0x80],), ([0xF5, 0x80, 0x80, 0x80],), ([0x80],),
                    ([0xC2],), ([0xE2, 0x82],), ([0xFF],)],
        random_case=_utf8_rand,
    ),
    Task(
        id="glob_match", func="glob_match", suite="hard",
        spec=(
            "Return True iff the whole string `text` matches the glob `pattern`. In the pattern, "
            "`?` matches exactly one character, `*` matches any sequence of characters (including "
            "the empty one), and a backslash `\\` makes the following character match literally "
            "(so `\\*` matches only `*`, `\\\\` matches only `\\`); a lone backslash at the very "
            "end of the pattern matches a literal backslash. Every other character matches itself."
        ),
        py_signature="def glob_match(pattern: str, text: str) -> bool",
        dfy_signature="method glob_match(pattern: string, text: string) returns (b: bool)",
        oracle=_glob_oracle,
        edge_cases=[("", ""), ("", "a"), ("*", ""), ("?", ""), ("a*b", "ab"), ("*a*", "bab"),
                    ("\\*", "*"), ("\\*", "a"), ("\\", "\\"), ("a\\", "a\\"), ("\\\\", "\\"),
                    ("**", "abc"), ("*?*?", "a"), ("\\?", "a"), ("a*a*a*b", "aaaaaaaaaa")],
        random_case=_glob_rand,
    ),
    Task(
        id="lru_cache", func="lru_cache", suite="hard",
        spec=(
            "Simulate an LRU cache with fixed `capacity` (>= 1), initially empty, over `ops`, a "
            "list of triples `(kind, key, value)`. kind 0 = get(key): append the cached value to "
            "the output, or -1 if absent (value field ignored). kind 1 = put(key, value): store "
            "the value (replacing any previous one). Both a successful get and any put make the "
            "key the most recently used. When a put inserts a NEW key while the cache already "
            "holds `capacity` keys, first evict the least recently used key. Values are >= 0. "
            "Return the output list."
        ),
        py_signature="def lru_cache(capacity: int, ops: list[tuple[int, int, int]]) -> list[int]",
        dfy_signature="method lru_cache(capacity: int, ops: seq<(int, int, int)>) returns (out: seq<int>)",
        oracle=_lru_oracle,
        edge_cases=[(1, [(1, 1, 1), (1, 2, 2), (0, 1, 0), (0, 2, 0)]),
                    (2, [(1, 1, 1), (1, 2, 2), (0, 1, 0), (1, 3, 3), (0, 2, 0), (0, 1, 0), (0, 3, 0)]),
                    (2, [(1, 1, 1), (1, 2, 2), (1, 1, 10), (1, 3, 3), (0, 2, 0), (0, 1, 0)]),
                    (2, [(1, 1, 1), (1, 2, 2), (1, 2, 20), (0, 1, 0), (0, 2, 0)]),
                    (1, [(0, 0, 0)])],
        random_case=_lru_rand,
    ),
    Task(
        id="topo_sort", func="topo_sort", suite="hard",
        spec=(
            "Given `n` >= 1 nodes numbered 0..n-1 and a list of directed edges `(u, v)` (0 <= u, "
            "v < n) meaning u must come before v — the list may contain duplicate edges and "
            "self-loops — return the lexicographically smallest ordering of all n nodes that "
            "respects every edge. If no such ordering exists (the graph has a cycle, including a "
            "self-loop), return the empty list."
        ),
        py_signature="def topo_sort(n: int, edges: list[tuple[int, int]]) -> list[int]",
        dfy_signature="method topo_sort(n: int, edges: seq<(int, int)>) returns (order: seq<int>)",
        oracle=_topo_oracle,
        edge_cases=[(1, []), (1, [(0, 0)]), (3, []), (3, [(2, 0)]), (2, [(0, 1), (0, 1)]),
                    (3, [(0, 1), (1, 2), (2, 0)]), (4, [(3, 1), (2, 1)]), (4, [(3, 0), (1, 2)])],
        random_case=_topo_rand,
    ),
    Task(
        id="justify", func="justify", suite="hard",
        spec=(
            "Fully justify text. `words` is a list of non-empty words (no spaces), each of length "
            "<= `width`. Greedily pack as many words as possible on each line with at least one "
            "space between words, so that each line has exactly `width` characters. On every "
            "line except the last, if the line has two or more words, distribute the spaces as "
            "evenly as possible between words, giving the extra spaces to the leftmost gaps. A "
            "line with a single word, and the last line, are left-justified: words separated by "
            "one space, padded with spaces on the right up to `width`. Return the list of lines "
            "(empty list for no words)."
        ),
        py_signature="def justify(words: list[str], width: int) -> list[str]",
        dfy_signature="method justify(words: seq<string>, width: int) returns (lines: seq<string>)",
        oracle=_justify_oracle,
        edge_cases=[([], 5), (["a"], 1), (["a", "b"], 3), (["a", "b"], 2),
                    (["This", "is", "an", "example", "of", "text", "justification."], 16),
                    (["What", "must", "be", "acknowledgment", "shall", "be"], 16),
                    (["ab", "c", "d"], 6), (["aa", "b", "cc", "d"], 7),
                    (["a", "b", "c", "d", "eeeeeeee"], 8)],
        random_case=_justify_rand,
    ),
    Task(
        id="add_big", func="add_big", suite="hard",
        spec=(
            "`a` and `b` are arbitrarily large integers written in canonical decimal form: either "
            "`0`, or an optional `-` followed by digits with a non-zero first digit (so no "
            "leading zeros, no `+`, no `-0`). Return a + b in the same canonical form. The "
            "operands can have hundreds of digits: do not rely on fixed-width integer types."
        ),
        py_signature="def add_big(a: str, b: str) -> str",
        dfy_signature="method add_big(a: string, b: string) returns (s: string)",
        oracle=_add_oracle,
        edge_cases=[("0", "0"), ("-1", "1"), ("999", "1"), ("-1000", "1"), ("1", "-1000"),
                    ("-5", "-5"), ("100000000000000000000", "-1"), ("123", "-123"), ("0", "-7"),
                    ("-999999", "1000000")],
        random_case=_add_rand,
    ),
    Task(
        id="normalize_path", func="normalize_path", suite="hard",
        spec=(
            "Normalize a Unix-style path string. Split it on `/`; drop empty components and `.`. "
            "A `..` removes the preceding kept component if there is one and it is not itself "
            "`..`; otherwise, in an absolute path (one starting with `/`) the `..` is dropped "
            "(you cannot go above the root), and in a relative path it is kept. Any other "
            "component (including `...` or `.a`) is an ordinary name. An absolute result is `/` "
            "followed by the kept components joined with `/` (just `/` if none); a relative "
            "result is the kept components joined with `/`, or `.` if none. Never a trailing `/` "
            "except for the root."
        ),
        py_signature="def normalize_path(p: str) -> str",
        dfy_signature="method normalize_path(p: string) returns (r: string)",
        oracle=_path_oracle,
        edge_cases=[("",), ("/",), ("//",), (".",), ("..",), ("/..",), ("a/..",), ("a/../..",),
                    ("../a",), ("/a/./b/../../c/",), ("a//b/",), ("...",), ("/.../..",),
                    ("./.",), ("a/b/../../../c",), ("../../a/..",)],
        random_case=_path_rand,
    ),
]
