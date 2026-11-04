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


# --- 2. merge_sorted --------------------------------------------------------

def _merge_sorted_rand(r: random.Random) -> tuple:
    return (sorted(r.randint(-20, 20) for _ in range(r.randint(0, 25))),
            sorted(r.randint(-20, 20) for _ in range(r.randint(0, 25))))


# --- 3. majority_element ----------------------------------------------------

def _majority_oracle(xs):
    for x in set(xs):
        if 2 * xs.count(x) > len(xs):
            return x
    return -1


def _majority_rand(r: random.Random) -> tuple:
    n = r.randint(0, 30)
    if r.random() < 0.5 and n > 0:  # a value at, or just above, half
        v = r.randint(0, 5)
        k = n // 2 + r.randint(0, 1)
        xs = [v] * min(k, n) + [r.randint(0, 5) for _ in range(n - min(k, n))]
        r.shuffle(xs)
        return (xs,)
    return ([r.randint(0, 5) for _ in range(n)],)


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
    if len(xs) >= 2 and r.random() < 0.6:
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
        id="merge_sorted",
        func="merge_sorted",
        suite="heldout",
        spec=(
            "Given two lists of integers, each sorted in non-decreasing order (possibly empty, "
            "duplicates allowed), return one list sorted in non-decreasing order that contains the "
            "elements of both, each with the number of occurrences it has in total. "
            "Must run in O(n + m)."
        ),
        py_signature="def merge_sorted(xs: list[int], ys: list[int]) -> list[int]",
        dfy_signature="method merge_sorted(xs: seq<int>, ys: seq<int>) returns (r: seq<int>)",
        oracle=lambda xs, ys: sorted(xs + ys),
        edge_cases=[([], []), ([1], []), ([], [1]), ([1, 1], [1]), ([1, 2], [3, 4]), ([3, 4], [1, 2]),
                    ([1, 3], [2, 4]), ([-2, 0], [-1, 0, 0])],
        random_case=_merge_sorted_rand,
    ),
    Task(
        id="majority_element",
        func="majority_element",
        suite="heldout",
        spec=(
            "Given a list of non-negative integers (possibly empty), return the value that occurs in "
            "strictly more than half of the positions, or -1 if there is none. "
            "Must run in O(n) time."
        ),
        py_signature="def majority_element(xs: list[int]) -> int",
        dfy_signature="method majority_element(xs: seq<int>) returns (r: int)",
        oracle=_majority_oracle,
        edge_cases=[([],), ([0],), ([1, 2],), ([1, 1],), ([1, 1, 2],), ([1, 2, 1, 2],), ([0, 0, 0, 1, 1],),
                    ([2, 1, 2, 1, 2],), ([1, 2, 3],), ([3, 3, 1, 1, 2, 2],)],
        random_case=_majority_rand,
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
            "`xs[i] + xs[j] == target`, or `(-1, -1)` if there is none. Any such pair will do. "
            "Must run in O(n)."
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

# Reference and plausibly wrong solutions, for the self-check of the suite only.
GOOD = {
    "gcd": "def gcd(a, b):\n    a, b = abs(a), abs(b)\n    while b: a, b = b, a % b\n    return a\n",
    "merge_sorted": ("def merge_sorted(xs, ys):\n    i = j = 0; r = []\n    while i < len(xs) and j < len(ys):\n"
                     "        if xs[i] <= ys[j]: r.append(xs[i]); i += 1\n        else: r.append(ys[j]); j += 1\n"
                     "    return r + xs[i:] + ys[j:]\n"),
    "majority_element": ("def majority_element(xs):\n    c = v = 0\n    for x in xs:\n        if c == 0: v = x\n"
                         "        c += 1 if x == v else -1\n    return v if xs and 2 * xs.count(v) > len(xs) else -1\n"),
    "transpose": "def transpose(m):\n    return [list(c) for c in zip(*m)]\n",
    "next_permutation": ("def next_permutation(xs):\n    xs = list(xs); i = len(xs) - 2\n"
                         "    while i >= 0 and xs[i] >= xs[i + 1]: i -= 1\n    if i < 0: return xs[::-1]\n"
                         "    j = len(xs) - 1\n    while xs[j] <= xs[i]: j -= 1\n    xs[i], xs[j] = xs[j], xs[i]\n"
                         "    return xs[:i + 1] + xs[:i:-1]\n"),
    "two_sum_sorted": ("def two_sum_sorted(xs, target):\n    i, j = 0, len(xs) - 1\n    while i < j:\n"
                       "        s = xs[i] + xs[j]\n        if s == target: return (i, j)\n"
                       "        if s < target: i += 1\n        else: j -= 1\n    return (-1, -1)\n"),
}
BUGGY = {
    "gcd": "def gcd(a, b):\n    while b: a, b = b, a % b\n    return a\n",  # negative results
    "merge_sorted": "def merge_sorted(xs, ys):\n    return sorted(set(xs + ys))\n",  # loses duplicates
    "majority_element": ("def majority_element(xs):\n    c = v = 0\n    for x in xs:\n        if c == 0: v = x\n"
                         "        c += 1 if x == v else -1\n    return v if xs else -1\n"),  # no second pass
    "transpose": "def transpose(m):\n    return [row[:] for row in m]\n",  # right only for symmetric matrices
    "next_permutation": ("def next_permutation(xs):\n    xs = list(xs); i = len(xs) - 2\n"
                         "    while i >= 0 and xs[i] > xs[i + 1]: i -= 1\n    if i < 0: return xs[::-1]\n"
                         "    j = len(xs) - 1\n    while xs[j] < xs[i]: j -= 1\n    xs[i], xs[j] = xs[j], xs[i]\n"
                         "    return xs[:i + 1] + xs[:i:-1]\n"),  # strict comparisons: wrong with duplicates
    "two_sum_sorted": ("def two_sum_sorted(xs, target):\n    i, j = 0, len(xs) - 1\n    while i <= j:\n"
                       "        s = xs[i] + xs[j]\n        if s == target: return (i, j)\n"
                       "        if s < target: i += 1\n        else: j -= 1\n    return (-1, -1)\n"),  # may use one index twice
}


def selfcheck(n: int = 500, seed: int = 0) -> list[str]:
    """Every GOOD passes all the cases, every BUGGY fails one. The list of problems found."""
    from verifbench.tasks import hidden_cases, validate
    problems = []
    for task in HELDOUT_TASKS:
        for label, source in (("good", GOOD[task.id]), ("buggy", BUGGY[task.id])):
            env: dict[str, Any] = {}
            exec(source, env)
            failed = 0
            cases = hidden_cases(task, seed, n)
            for args in cases:
                try:
                    if validate(task, args, env[task.func](*args)) is not None:
                        failed += 1
                except Exception:
                    failed += 1
            print(f"{task.id:18} {label:5} {len(cases) - failed}/{len(cases)}")
            if (label == "good") != (failed == 0):
                problems.append(f"{task.id} {label}: {failed} failed of {len(cases)}")
    return problems


if __name__ == "__main__":
    found = selfcheck()
    print("problems:", found or "none")
