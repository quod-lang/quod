"""Suite "heldout": six tasks kept away from the compiler. Written before any Quod solution of them
exists, and committed before any run. They measure what the base suite cannot, since writing the
base tasks changed the verifier and its messages. No Quod program for them is written or checked
by hand, and the compiler is not changed between their runs: see bench/heldout.md."""
from __future__ import annotations

import math
import random
from typing import Any

from verifbench.tasks import Task

# --- 1. gcd -----------------------------------------------------------------

def _gcd_rand(r: random.Random) -> tuple:
    if r.random() < 0.4:  # a common factor, so that the answer is not always 1
        k = r.randint(1, 50)
        return (k * r.randint(-200, 200), k * r.randint(-200, 200))
    return (r.randint(-1000, 1000), r.randint(-1000, 1000))


# --- 2. split_folds ---------------------------------------------------------

def _folds_oracle(pages):
    folds, start = [], None
    for i, c in enumerate(pages):
        if c == 2:
            if start is not None:
                folds.append((start, i))
                start = None
        elif c == 1:
            if start is not None:
                folds.append((start, i))
            start = i
        elif start is None:
            start = i
    if start is not None:
        folds.append((start, len(pages)))
    return folds


def _folds_rand(r: random.Random) -> tuple:
    weights = r.choice([(5, 2, 1), (1, 1, 1), (1, 5, 1), (1, 1, 5)])  # long folds, or many short ones, or many separators
    return (r.choices([0, 1, 2], weights=weights, k=r.randint(0, 25)),)


# --- 3. arbitrate_field -----------------------------------------------------

def _arbitrate_oracle(candidates, rank, threshold):
    best = -1
    for i, (engine, confidence, _) in enumerate(candidates):
        if confidence < threshold:
            continue
        if best < 0:
            best = i
        else:
            e, c, _ = candidates[best]
            if confidence > c or (confidence == c and rank[engine] < rank[e]):
                best = i
    return best


def _arbitrate_rand(r: random.Random) -> tuple:
    engines = r.randint(1, 5)
    rank = list(range(engines))
    r.shuffle(rank)
    if r.random() < 0.2:  # engines of the same rank
        rank = [r.randint(0, 2) for _ in range(engines)]
    threshold = r.randint(0, 100)
    around = [threshold - 1, threshold, threshold + 1, r.randint(0, 100), r.randint(0, 100)]
    shared = r.randint(0, 100)  # equal confidences, so that the tie-breaks matter
    candidates = []
    for _ in range(r.randint(0, 8)):
        confidence = shared if r.random() < 0.4 else r.choice(around)
        candidates.append((r.randrange(engines), min(100, max(0, confidence)), r.randint(0, 50)))
    return (candidates, rank, threshold)


# --- 4. transpose -----------------------------------------------------------

def _transpose_rand(r: random.Random) -> tuple:
    rows, cols = r.randint(1, 8), r.randint(1, 8)
    return ([[r.randint(-9, 9) for _ in range(cols)] for _ in range(rows)],)


# --- 5. next_permutation ----------------------------------------------------

def _next_perm_oracle(xs):
    xs = list(xs)
    i = len(xs) - 2
    while i >= 0 and xs[i] >= xs[i + 1]:
        i -= 1
    if i < 0:
        return sorted(xs)
    j = len(xs) - 1
    while xs[j] <= xs[i]:
        j -= 1
    xs[i], xs[j] = xs[j], xs[i]
    xs[i + 1:] = reversed(xs[i + 1:])
    return xs


def _next_perm_rand(r: random.Random) -> tuple:
    n = r.randint(0, 9)
    xs = [r.randint(0, r.choice([1, 3, 9])) for _ in range(n)]
    shape = r.random()
    if shape < 0.15:
        xs.sort(reverse=True)  # the last permutation: wraps around
    elif shape < 0.3:
        xs.sort()
    return (xs,)


# --- 6. two_sum_sorted ------------------------------------------------------

def _two_sum_check(args: tuple, out: Any) -> str | None:
    xs, t = args
    if not (isinstance(out, list) and len(out) == 2 and all(isinstance(v, int) and not isinstance(v, bool) for v in out)):
        return f"expected a pair of ints, got {out!r}"
    i, j = out
    exists = any(xs[a] + xs[b] == t for a in range(len(xs)) for b in range(a + 1, len(xs)))
    if exists:
        if not (0 <= i < j < len(xs) and xs[i] + xs[j] == t):
            return f"a pair exists, but {out!r} is not one"
    elif out != [-1, -1]:
        return f"no pair exists, expected [-1, -1], got {out!r}"
    return None


def _two_sum_rand(r: random.Random) -> tuple:
    xs = sorted(r.randint(-15, 15) for _ in range(r.randint(0, 25)))
    shape = r.random()
    once = [x for x in xs if xs.count(x) == 1]
    if once and shape < 0.3:  # twice a value that occurs once: a single index must not be used twice
        return (xs, 2 * r.choice(once))
    if len(xs) >= 2 and shape < 0.7:
        a, b = r.sample(range(len(xs)), 2)
        return (xs, xs[a] + xs[b])
    return (xs, r.randint(-35, 35))


HELDOUT_TASKS = [
    Task(
        id="gcd",
        func="gcd",
        suite="heldout",
        spec=(
            "Return the greatest common divisor of two integers `a` and `b`, either of which may be "
            "negative or zero. The result is never negative, and the greatest common divisor of 0 "
            "and 0 is 0."
        ),
        py_signature="def gcd(a: int, b: int) -> int",
        dfy_signature="method gcd(a: int, b: int) returns (r: int)",
        oracle=math.gcd,
        edge_cases=[(0, 0), (0, 5), (5, 0), (0, -5), (-5, 0), (12, 18), (-12, 18), (12, -18),
                    (-12, -18), (1, 1), (7, 7), (17, 13), (1000, 10)],
        random_case=_gcd_rand,
    ),
    Task(
        id="split_folds",
        func="split_folds",
        suite="heldout",
        spec=(
            "Given the classification of each page of a scanned batch, as a list of integers (0: a "
            "continuation page, 1: the first page of a document, 2: a separator sheet), return the folds "
            "of the batch, in order, as a list of pairs `(start, end)`: the fold covers the pages `start` "
            "to `end - 1`. A fold starts at a page classified 1, or at the first page that is not a "
            "separator, at the start of the batch or after a separator. It ends just before the next page "
            "classified 1, the next separator, or the end of the batch. Separator sheets belong to no "
            "fold, every other page belongs to exactly one, and no fold is empty."
        ),
        py_signature="def split_folds(pages: list[int]) -> list[tuple[int, int]]",
        dfy_signature="method split_folds(pages: seq<int>) returns (r: seq<(int, int)>)",
        oracle=_folds_oracle,
        edge_cases=[([],), ([2, 2],), ([0],), ([1, 0, 0, 1, 0],), ([1, 2, 0, 0],), ([2, 1, 1, 2],), ([1, 1, 1],),
                    ([0, 0, 1],), ([2, 0, 2, 0],), ([2],), ([1],)],
        random_case=_folds_rand,
    ),
    Task(
        id="arbitrate_field",
        func="arbitrate_field",
        suite="heldout",
        spec=(
            "Several engines propose a value for the same field. Each candidate is a triple "
            "`(engine, confidence, value)`, with `engine` an index into `rank` and `confidence` between 0 "
            "and 100; `threshold` is also between 0 and 100. `rank[e]` is the trust order of engine `e`: a "
            "smaller rank is more trusted. Return the index, in `candidates`, of the retained candidate: "
            "among the candidates whose confidence is at least `threshold`, the one with the highest "
            "confidence; between equal confidences, the one whose engine has the smallest rank; and between "
            "equal confidences and equal ranks, the first one. If no candidate reaches the threshold, "
            "return -1: the field goes to manual validation."
        ),
        py_signature="def arbitrate_field(candidates: list[tuple[int, int, int]], rank: list[int], threshold: int) -> int",
        dfy_signature="method arbitrate_field(candidates: seq<(int, int, int)>, rank: seq<int>, threshold: int) returns (r: int)",
        oracle=_arbitrate_oracle,
        edge_cases=[([], [0], 50), ([(0, 49, 7)], [0], 50), ([(0, 50, 7)], [0], 50),
                    ([(0, 80, 1), (1, 90, 2)], [0, 1], 50), ([(1, 90, 1), (0, 90, 2)], [0, 1], 50),
                    ([(0, 90, 1), (0, 90, 2)], [0], 50), ([(0, 90, 1), (1, 95, 2)], [1, 0], 96),
                    ([(0, 90, 1), (1, 90, 2)], [0, 0], 50), ([(0, 90, 1), (1, 90, 2)], [1, 0], 50)],
        random_case=_arbitrate_rand,
    ),
    Task(
        id="transpose",
        func="transpose",
        suite="heldout",
        spec=(
            "Given a matrix as a list of rows, with at least one row, at least one column, and all "
            "rows of the same length, return its transpose: element `j` of row `i` of the result is "
            "element `i` of row `j` of the input."
        ),
        py_signature="def transpose(m: list[list[int]]) -> list[list[int]]",
        dfy_signature="method transpose(m: seq<seq<int>>) returns (r: seq<seq<int>>)",
        oracle=lambda m: [[row[j] for row in m] for j in range(len(m[0]))],
        edge_cases=[([[1]],), ([[1, 2, 3]],), ([[1], [2], [3]],), ([[1, 2], [3, 4]],),
                    ([[1, 2, 3], [4, 5, 6]],), ([[0, 0], [0, 0], [0, 0]],)],
        random_case=_transpose_rand,
    ),
    Task(
        id="next_permutation",
        func="next_permutation",
        suite="heldout",
        spec=(
            "Given a list of integers (possibly empty, duplicates allowed), return the rearrangement "
            "of its elements that comes next in lexicographic order, that is the smallest "
            "rearrangement strictly greater than the list. If the list is its own greatest "
            "rearrangement, return the smallest one, its elements in non-decreasing order."
        ),
        py_signature="def next_permutation(xs: list[int]) -> list[int]",
        dfy_signature="method next_permutation(xs: seq<int>) returns (r: seq<int>)",
        oracle=_next_perm_oracle,
        edge_cases=[([],), ([1],), ([1, 2],), ([2, 1],), ([1, 1],), ([1, 2, 3],), ([3, 2, 1],), ([1, 3, 2],),
                    ([1, 1, 5],), ([1, 5, 1],), ([5, 1, 1],), ([2, 3, 1],)],
        random_case=_next_perm_rand,
    ),
    Task(
        id="two_sum_sorted",
        func="two_sum_sorted",
        suite="heldout",
        spec=(
            "Given a list of integers `xs` sorted in non-decreasing order (possibly empty, duplicates "
            "allowed) and an integer `target`, return a pair of indices `(i, j)` with `i < j` and "
            "`xs[i] + xs[j] == target`, or `(-1, -1)` if there is none. Any such pair will do."
        ),
        py_signature="def two_sum_sorted(xs: list[int], target: int) -> tuple[int, int]",
        dfy_signature="method two_sum_sorted(xs: seq<int>, target: int) returns (r: (int, int))",
        oracle=None,
        check=_two_sum_check,
        edge_cases=[([], 0), ([1], 2), ([1, 1], 2), ([1, 2], 4), ([1, 2, 3], 5), ([1, 2, 3], 7),
                    ([-3, 0, 3], 0), ([2, 2, 2], 4), ([0, 0], 0), ([-5, -1], -6)],
        random_case=_two_sum_rand,
    ),
]

# Reference and plausibly wrong solutions, for the self-check of the suite only. How many cases
# each wrong one passes is the sensitivity of the "escaped bug" measure, reported with the results.
GOOD = {
    "gcd": "def gcd(a, b):\n    a, b = abs(a), abs(b)\n    while b: a, b = b, a % b\n    return a\n",
    "split_folds": ("def split_folds(pages):\n    r = []; s = None\n    for i, c in enumerate(pages):\n"
                    "        if c == 2 or c == 1:\n            if s is not None: r.append((s, i))\n            s = i if c == 1 else None\n"
                    "        elif s is None: s = i\n    if s is not None: r.append((s, len(pages)))\n    return r\n"),
    "arbitrate_field": ("def arbitrate_field(candidates, rank, threshold):\n    best = None; at = -1\n"
                        "    for i, (e, c, _) in enumerate(candidates):\n        if c >= threshold and (best is None or (-c, rank[e]) < best):\n"
                        "            best = (-c, rank[e]); at = i\n    return at\n"),
    "transpose": "def transpose(m):\n    return [list(c) for c in zip(*m)]\n",
    "next_permutation": ("def next_permutation(xs):\n    xs = list(xs); i = len(xs) - 2\n"
                         "    while i >= 0 and xs[i] >= xs[i + 1]: i -= 1\n    if i < 0: return xs[::-1]\n"
                         "    j = len(xs) - 1\n    while xs[j] <= xs[i]: j -= 1\n    xs[i], xs[j] = xs[j], xs[i]\n"
                         "    return xs[:i + 1] + xs[:i:-1]\n"),
    "two_sum_sorted": ("def two_sum_sorted(xs, target):\n    i, j = 0, len(xs) - 1\n    while i < j:\n"
                       "        s = xs[i] + xs[j]\n        if s == target: return (i, j)\n"
                       "        if s < target: i += 1\n        else: j -= 1\n    return (-1, -1)\n"),
}
_ARBITRATE = ("def arbitrate_field(candidates, rank, threshold):\n    best = None; at = -1\n"
              "    for i, (e, c, v) in enumerate(candidates):\n        if {pass_} and (best is None or {key} {cmp} best):\n"
              "            best = {key}; at = {result}\n    return at\n")
BUGGY = {
    "gcd": {"negative results": "def gcd(a, b):\n    while b: a, b = b, a % b\n    return a\n"},
    "split_folds": {
        "a separator joins the fold before it": (
            "def split_folds(pages):\n    r = []; s = None\n    for i, c in enumerate(pages):\n"
            "        if c == 2:\n            if s is not None: r.append((s, i + 1)); s = None\n"
            "        elif c == 1:\n            if s is not None: r.append((s, i))\n            s = i\n"
            "        elif s is None: s = i\n    if s is not None: r.append((s, len(pages)))\n    return r\n"),
        "an empty fold between two separators": (
            "def split_folds(pages):\n    r = []; s = 0\n    for i, c in enumerate(pages):\n"
            "        if c == 2: r.append((s, i)); s = i + 1\n"
            "        elif c == 1 and i > s: r.append((s, i)); s = i\n"
            "    if s < len(pages): r.append((s, len(pages)))\n    return r\n"),
        "a leading continuation page is ignored": (
            "def split_folds(pages):\n    r = []; s = None\n    for i, c in enumerate(pages):\n"
            "        if c == 2 or c == 1:\n            if s is not None: r.append((s, i))\n            s = i if c == 1 else None\n"
            "    if s is not None: r.append((s, len(pages)))\n    return r\n"),
    },
    "arbitrate_field": {
        "> for >= on the threshold": _ARBITRATE.format(pass_="c > threshold", key="(-c, rank[e])", cmp="<", result="i"),
        "ties by engine index, not rank": _ARBITRATE.format(pass_="c >= threshold", key="(-c, e)", cmp="<", result="i"),
        "the last candidate, not the first": _ARBITRATE.format(pass_="c >= threshold", key="(-c, rank[e])", cmp="<=", result="i"),
        "the value, not the index": _ARBITRATE.format(pass_="c >= threshold", key="(-c, rank[e])", cmp="<", result="v"),
    },
    "transpose": {"a copy": "def transpose(m):\n    return [row[:] for row in m]\n"},
    "next_permutation": {"strict comparisons": (
        "def next_permutation(xs):\n    xs = list(xs); i = len(xs) - 2\n"
        "    while i >= 0 and xs[i] > xs[i + 1]: i -= 1\n    if i < 0: return xs[::-1]\n"
        "    j = len(xs) - 1\n    while xs[j] < xs[i]: j -= 1\n    xs[i], xs[j] = xs[j], xs[i]\n"
        "    return xs[:i + 1] + xs[:i:-1]\n")},
    "two_sum_sorted": {"a single index used twice": (
        "def two_sum_sorted(xs, target):\n    i, j = 0, len(xs) - 1\n    while i <= j:\n"
        "        s = xs[i] + xs[j]\n        if s == target: return (i, j)\n"
        "        if s < target: i += 1\n        else: j -= 1\n    return (-1, -1)\n")},
}


def selfcheck(n: int = 500, seed: int = 20260929) -> list[str]:
    """Every GOOD passes all the cases, every BUGGY fails one. The list of problems found."""
    from verifbench.tasks import hidden_cases, validate
    problems = []
    for task in HELDOUT_TASKS:
        cases = hidden_cases(task, seed, n)

        def failures(source: str) -> int:
            env: dict[str, Any] = {}
            exec(source, env)
            failed = 0
            for args in cases:
                try:
                    if validate(task, args, env[task.func](*args)) is not None:
                        failed += 1
                except Exception:
                    failed += 1
            return failed

        failed = failures(GOOD[task.id])
        print(f"{task.id:18} reference: {len(cases) - failed}/{len(cases)}")
        if failed:
            problems.append(f"{task.id}: the reference fails {failed}")
        for label, source in BUGGY[task.id].items():
            failed = failures(source)
            print(f"{task.id:18} {label}: passes {len(cases) - failed}/{len(cases)}")
            if failed == 0:
                problems.append(f"{task.id}: not caught: {label}")
    return problems


if __name__ == "__main__":
    found = selfcheck()
    print("problems:", found or "none")
