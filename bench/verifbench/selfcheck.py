"""Sanity-check the hidden tests: every GOOD solution must pass 100%, every BUGGY one
(a plausible agent mistake) must be caught. Runs through the same subprocess path as real runs.

    python -m verifbench.selfcheck
"""
from __future__ import annotations

import sys
import tempfile
from pathlib import Path

from verifbench.run import hidden
from verifbench.tasks import TASKS

GOOD = {
    "binary_search": """
def binary_search(xs, target):
    lo, hi = 0, len(xs)
    while lo < hi:
        mid = (lo + hi) // 2
        if xs[mid] < target: lo = mid + 1
        elif xs[mid] > target: hi = mid
        else: return mid
    return -1
""",
    "merge_intervals": """
def merge_intervals(iv):
    out = []
    for a, b in sorted(iv):
        if out and a <= out[-1][1]: out[-1] = (out[-1][0], max(out[-1][1], b))
        else: out.append((a, b))
    return out
""",
    "rle_encode": """
def rle_encode(xs):
    out = []
    for x in xs:
        if out and out[-1][0] == x: out[-1] = (x, out[-1][1] + 1)
        else: out.append((x, 1))
    return out
""",
    "parse_int": """
def parse_int(s):
    body = s[1:] if s[:1] in ('+', '-') else s
    if not body or not all('0' <= c <= '9' for c in body): return (False, 0)
    v = int(body) * (-1 if s[0] == '-' else 1)
    return (True, v) if -2**31 <= v < 2**31 else (False, 0)
""",
    "bounded_queue": """
from collections import deque
def bounded_queue(capacity, ops):
    q, out = deque(maxlen=capacity), []
    for op in ops:
        if op: q.append(op)
        else: out.append(q.popleft() if q else -1)
    return out
""",
    "max_subarray": """
def max_subarray(xs):
    best = cur = xs[0]
    for x in xs[1:]:
        cur = max(x, cur + x); best = max(best, cur)
    return best
""",
    "rotate": """
def rotate(xs, k):
    if not xs: return []
    k %= len(xs)
    return xs[len(xs) - k:] + xs[:len(xs) - k]
""",
    "balanced": """
def balanced(s):
    st, m = [], {')': '(', ']': '[', '}': '{'}
    for c in s:
        if c in '([{': st.append(c)
        elif c in m and (not st or st.pop() != m[c]): return False
    return not st
""",
}

BUGGY = {
    "binary_search": """
def binary_search(xs, target):          # off-by-one: never inspects the last slot
    lo, hi = 0, len(xs) - 1
    while lo < hi:
        mid = (lo + hi) // 2
        if xs[mid] < target: lo = mid + 1
        elif xs[mid] > target: hi = mid
        else: return mid
    return -1
""",
    "merge_intervals": """
def merge_intervals(iv):                # strict '<': touching intervals are not merged
    out = []
    for a, b in sorted(iv):
        if out and a < out[-1][1]: out[-1] = (out[-1][0], max(out[-1][1], b))
        else: out.append((a, b))
    return out
""",
    "rle_encode": """
def rle_encode(xs):                     # forgets to flush the final run
    out, cur, n = [], None, 0
    for x in xs:
        if n and x == cur: n += 1
        else:
            if n: out.append((cur, n))
            cur, n = x, 1
    return out
""",
    "parse_int": """
def parse_int(s):                       # trusts int(): accepts ' 1', '1_000', unicode digits
    try: v = int(s)
    except ValueError: return (False, 0)
    return (True, v) if -2**31 <= v < 2**31 else (False, 0)
""",
    "bounded_queue": """
def bounded_queue(capacity, ops):       # drops the NEW element when full
    q, out = [], []
    for op in ops:
        if op:
            if len(q) < capacity: q.append(op)
        else: out.append(q.pop(0) if q else -1)
    return out
""",
    "max_subarray": """
def max_subarray(xs):                   # best starts at 0: wrong when all negative
    best = cur = 0
    for x in xs:
        cur = max(0, cur + x); best = max(best, cur)
    return best
""",
    "rotate": """
def rotate(xs, k):                      # no modulo: breaks when |k| > len
    return xs[-k:] + xs[:-k] if xs and k else list(xs)
""",
    "balanced": """
def balanced(s):                        # counts per bracket type: ignores nesting order
    for o, c in ('()', '[]', '{}'):
        d = 0
        for ch in s:
            d += (ch == o) - (ch == c)
            if d < 0: return False
        if d: return False
    return True
""",
}


from verifbench import selfcheck_hard  # noqa: E402

GOOD.update(selfcheck_hard.GOOD)
BUGGY.update(selfcheck_hard.BUGGY)


def main() -> int:
    ok = True
    with tempfile.TemporaryDirectory() as tmp:
        for kind, sols in (("good", GOOD), ("buggy", BUGGY)):
            for tid in sorted(TASKS):
                wd = Path(tmp) / f"{kind}_{tid}"
                wd.mkdir()
                (wd / "solution.py").write_text(sols[tid], encoding="utf-8")
                h = hidden(tid, "python", wd)
                passed_all = h.get("loaded") and h.get("passed") == h.get("total")
                expect = kind == "good"
                status = "OK " if passed_all == expect else "BAD"
                ok &= passed_all == expect
                detail = h.get("failures", [{}])[0].get("error", "") if h.get("failures") else h.get("error", "")
                print(f"{status} {kind:5} {tid:16} {h.get('passed')}/{h.get('total')}  {detail[:70]}")
    print("\nselfcheck:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
