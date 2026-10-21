"""Task registry: natural-language spec, signatures per arm, oracle, hidden-case generators.

The spec text is identical for both arms; only the target language changes.
"""
from __future__ import annotations

import random
from collections import deque
from dataclasses import dataclass
from typing import Any, Callable

I32_MIN, I32_MAX = -(2**31), 2**31 - 1


@dataclass(frozen=True)
class Task:
    id: str
    func: str
    spec: str
    py_signature: str
    dfy_signature: str
    oracle: Callable[..., Any] | None
    edge_cases: list[tuple]
    random_case: Callable[[random.Random], tuple]
    # Custom validator (args, normalized_output) -> error message or None.
    # When absent, output must equal normalize(oracle(*args)).
    check: Callable[[tuple, Any], str | None] | None = None
    suite: str = "base"


def normalize(v: Any) -> Any:
    """Canonical form for comparison: tuples -> lists, recursively."""
    if isinstance(v, (list, tuple)):
        return [normalize(x) for x in v]
    return v


# --- 1. binary_search -------------------------------------------------------

def _bs_check(args: tuple, out: Any) -> str | None:
    xs, t = args
    if not isinstance(out, int) or isinstance(out, bool):
        return f"expected int, got {type(out).__name__}"
    if t in xs:
        if not (0 <= out < len(xs) and xs[out] == t):
            return f"target present but returned {out}"
    elif out != -1:
        return f"target absent, expected -1, got {out}"
    return None


def _bs_rand(r: random.Random) -> tuple:
    xs = sorted(r.randint(-20, 20) for _ in range(r.randint(0, 30)))
    t = r.choice(xs) if xs and r.random() < 0.5 else r.randint(-25, 25)
    return (xs, t)


# --- 2. merge_intervals -----------------------------------------------------

def _merge_oracle(iv):
    out: list[list[int]] = []
    for a, b in sorted(iv):
        if out and a <= out[-1][1]:
            out[-1][1] = max(out[-1][1], b)
        else:
            out.append([a, b])
    return out


def _merge_rand(r: random.Random) -> tuple:
    iv = []
    for _ in range(r.randint(0, 10)):
        a = r.randint(-10, 10)
        iv.append((a, a + r.randint(0, 6)))
    return (iv,)


# --- 3. rle_encode ----------------------------------------------------------

def _rle_oracle(xs):
    out: list[list[int]] = []
    for x in xs:
        if out and out[-1][0] == x:
            out[-1][1] += 1
        else:
            out.append([x, 1])
    return out


def _rle_rand(r: random.Random) -> tuple:
    return ([r.randint(-1, 2) for _ in range(r.randint(0, 25))],)


# --- 4. parse_int -----------------------------------------------------------

def _parse_oracle(s: str):
    if not s:
        return (False, 0)
    i, neg = 0, False
    if s[0] in "+-":
        neg, i = s[0] == "-", 1
    digits = s[i:]
    if not digits or any(c not in "0123456789" for c in digits):
        return (False, 0)
    v = -int(digits) if neg else int(digits)
    if not (I32_MIN <= v <= I32_MAX):
        return (False, 0)
    return (True, v)


def _parse_rand(r: random.Random) -> tuple:
    roll = r.random()
    if roll < 0.25:
        base = r.choice([I32_MAX, I32_MIN])
        return (str(base + r.randint(-2, 2)),)
    sign = r.choice(["", "", "+", "-"])
    body = "".join(r.choice("0123456789") for _ in range(r.randint(0, 12)))
    if roll > 0.8 and body:
        pos = r.randrange(len(body) + 1)
        body = body[:pos] + r.choice(" x_.+-٣") + body[pos:]
    return (sign + body,)


# --- 5. bounded_queue -------------------------------------------------------

def _queue_oracle(capacity: int, ops):
    q: deque[int] = deque()
    out = []
    for op in ops:
        if op == 0:
            out.append(q.popleft() if q else -1)
        else:
            if len(q) == capacity:
                q.popleft()
            q.append(op)
    return out


def _queue_rand(r: random.Random) -> tuple:
    ops = [0 if r.random() < 0.4 else r.randint(1, 9) for _ in range(r.randint(0, 25))]
    return (r.randint(1, 4), ops)


# --- 6. max_subarray --------------------------------------------------------

def _maxsub_oracle(xs):
    return max(sum(xs[i:j]) for i in range(len(xs)) for j in range(i + 1, len(xs) + 1))


def _maxsub_rand(r: random.Random) -> tuple:
    hi = 10 if r.random() < 0.8 else -1  # sometimes all-negative
    return ([r.randint(-10, hi) for _ in range(r.randint(1, 20))],)


# --- 7. rotate --------------------------------------------------------------

def _rotate_oracle(xs, k: int):
    if not xs:
        return []
    k %= len(xs)
    return xs[len(xs) - k:] + xs[: len(xs) - k]


def _rotate_rand(r: random.Random) -> tuple:
    return ([r.randint(0, 9) for _ in range(r.randint(0, 10))], r.randint(-25, 25))


# --- 8. balanced ------------------------------------------------------------

_PAIRS = {")": "(", "]": "[", "}": "{"}


def _balanced_oracle(s: str) -> bool:
    st: list[str] = []
    for c in s:
        if c in "([{":
            st.append(c)
        elif c in _PAIRS:
            if not st or st.pop() != _PAIRS[c]:
                return False
    return not st


def _balanced_rand(r: random.Random) -> tuple:
    def gen(depth: int) -> str:
        if depth == 0 or r.random() < 0.3:
            return r.choice(["", "a", " "])
        o, c = r.choice([("(", ")"), ("[", "]"), ("{", "}")])
        return o + gen(depth - 1) + c + gen(depth - 1)
    s = gen(4)
    roll = r.random()
    if len(s) >= 2 and roll < 0.3:  # swap two brackets: keeps counts, breaks nesting order
        i, j = sorted(r.sample(range(len(s)), 2))
        s = s[:i] + s[j] + s[i + 1:j] + s[i] + s[j + 1:]
    elif s and roll < 0.6:  # substitute one char
        i = r.randrange(len(s))
        s = s[:i] + r.choice("()[]{}") + s[i + 1:]
    return (s,)


TASKS: dict[str, Task] = {t.id: t for t in [
    Task(
        id="binary_search",
        func="binary_search",
        spec=(
            "Given a list of integers `xs` sorted in non-decreasing order (duplicates allowed, "
            "possibly empty) and an integer `target`, return an index `i` such that "
            "`xs[i] == target`, or -1 if `target` does not occur in `xs`. "
            "Must run in O(log n)."
        ),
        py_signature="def binary_search(xs: list[int], target: int) -> int",
        dfy_signature="method binary_search(xs: seq<int>, target: int) returns (r: int)",
        oracle=None,
        check=_bs_check,
        edge_cases=[([], 5), ([1], 1), ([1], 0), ([1], 2), ([1, 1, 1], 1), ([1, 2], 2),
                    ([1, 2], 1), ([1, 2], 3), ([-5, -3, 0], -4), ([2, 2, 2, 2, 3], 3)],
        random_case=_bs_rand,
    ),
    Task(
        id="merge_intervals",
        func="merge_intervals",
        spec=(
            "Given a list of closed integer intervals `(a, b)` with `a <= b`, in any order "
            "(possibly empty, possibly with duplicates), return the union as a list of disjoint "
            "intervals sorted by start. Two intervals are merged when they overlap or touch at "
            "an endpoint (e.g. (1,3) and (3,5) -> (1,5)); (1,2) and (3,4) are NOT merged."
        ),
        py_signature="def merge_intervals(iv: list[tuple[int, int]]) -> list[tuple[int, int]]",
        dfy_signature="method merge_intervals(iv: seq<(int, int)>) returns (r: seq<(int, int)>)",
        oracle=_merge_oracle,
        edge_cases=[([],), ([(1, 1)],), ([(1, 3), (3, 5)],), ([(1, 2), (3, 4)],),
                    ([(5, 6), (1, 10)],), ([(1, 4), (2, 3)],), ([(0, 0), (0, 0)],),
                    ([(3, 5), (1, 2), (2, 3)],)],
        random_case=_merge_rand,
    ),
    Task(
        id="rle_encode",
        func="rle_encode",
        spec=(
            "Run-length encode a list of integers: return a list of `(value, count)` pairs, one "
            "per maximal run of equal consecutive values, in order. Counts are >= 1. "
            "Empty input gives empty output."
        ),
        py_signature="def rle_encode(xs: list[int]) -> list[tuple[int, int]]",
        dfy_signature="method rle_encode(xs: seq<int>) returns (r: seq<(int, int)>)",
        oracle=_rle_oracle,
        edge_cases=[([],), ([7],), ([7, 7],), ([1, 2],), ([1, 1, 2, 2, 2, 1],), ([-1, -1, 0],)],
        random_case=_rle_rand,
    ),
    Task(
        id="parse_int",
        func="parse_int",
        spec=(
            "Parse a string as a signed 32-bit decimal integer. A valid string is an optional "
            "single sign (`+` or `-`) followed by one or more ASCII digits `0`-`9` and nothing "
            "else (no whitespace, no other characters; leading zeros are allowed). The value "
            "must lie in [-2147483648, 2147483647]. Return `(True, value)` if valid, "
            "otherwise `(False, 0)`."
        ),
        py_signature="def parse_int(s: str) -> tuple[bool, int]",
        dfy_signature="method parse_int(s: string) returns (ok: bool, v: int)",
        oracle=_parse_oracle,
        edge_cases=[("",), ("0",), ("-0",), ("+0",), ("-",), ("+",), ("+-1",), ("007",),
                    ("2147483647",), ("2147483648",), ("-2147483648",), ("-2147483649",),
                    (" 1",), ("1 ",), ("12a",), ("٣",), ("99999999999999999999",),
                    ("1_000",)],
        random_case=_parse_rand,
    ),
    Task(
        id="bounded_queue",
        func="bounded_queue",
        spec=(
            "Simulate a FIFO queue with fixed `capacity` (>= 1), initially empty, over a list of "
            "operations `ops` (all >= 0). An op `x > 0` pushes `x`; if the queue is already full, "
            "the oldest element is dropped first. An op `0` pops the oldest element and appends "
            "it to the output, or appends -1 if the queue is empty. Return the output list."
        ),
        py_signature="def bounded_queue(capacity: int, ops: list[int]) -> list[int]",
        dfy_signature="method bounded_queue(capacity: int, ops: seq<int>) returns (out: seq<int>)",
        oracle=_queue_oracle,
        edge_cases=[(1, []), (1, [0]), (1, [5, 6, 0, 0]), (2, [1, 2, 3, 0, 0, 0]),
                    (3, [1, 0, 2, 0, 0])],
        random_case=_queue_rand,
    ),
    Task(
        id="max_subarray",
        func="max_subarray",
        spec=(
            "Given a non-empty list of integers, return the maximum sum over all non-empty "
            "contiguous sublists. Must run in O(n)."
        ),
        py_signature="def max_subarray(xs: list[int]) -> int",
        dfy_signature="method max_subarray(xs: seq<int>) returns (m: int)",
        oracle=_maxsub_oracle,
        edge_cases=[([-3],), ([-3, -1, -2],), ([0],), ([5, -10, 5],), ([1, 2, 3],),
                    ([-1, 3, -1, 3, -1],)],
        random_case=_maxsub_rand,
    ),
    Task(
        id="rotate",
        func="rotate",
        spec=(
            "Rotate a list to the right by `k` positions and return the new list "
            "(e.g. [1,2,3] with k=1 -> [3,1,2]). `k` may be any integer: negative values rotate "
            "left, values larger than the length wrap around. An empty list returns an empty list."
        ),
        py_signature="def rotate(xs: list[int], k: int) -> list[int]",
        dfy_signature="method rotate(xs: seq<int>, k: int) returns (r: seq<int>)",
        oracle=_rotate_oracle,
        edge_cases=[([], 3), ([1], -7), ([1, 2, 3], 0), ([1, 2, 3], 1), ([1, 2, 3], -1),
                    ([1, 2, 3], 3), ([1, 2, 3], -4), ([1, 2, 3], 1000000007)],
        random_case=_rotate_rand,
    ),
    Task(
        id="balanced",
        func="balanced",
        spec=(
            "Return True iff the brackets `()`, `[]`, `{}` in string `s` are balanced and "
            "properly nested. All other characters are ignored. The empty string is balanced."
        ),
        py_signature="def balanced(s: str) -> bool",
        dfy_signature="method balanced(s: string) returns (b: bool)",
        oracle=_balanced_oracle,
        edge_cases=[("",), ("()",), ("(]",), ("([)]",), ("{[]}",), (")(",), ("(((",),
                    ("a(b)c",), ("}{",), ("([]{})",)],
        random_case=_balanced_rand,
    ),
]}


from verifbench.tasks_hard import HARD_TASKS  # noqa: E402 - needs Task defined above

TASKS.update({t.id: t for t in HARD_TASKS})


def validate(task: Task, args: tuple, out: Any) -> str | None:
    out = normalize(out)
    if task.check is not None:
        return task.check(args, out)
    expected = normalize(task.oracle(*args))
    if out != expected:
        return f"expected {expected!r}, got {out!r}"
    return None


def hidden_cases(task: Task, seed: int, n: int) -> list[tuple]:
    r = random.Random(f"{seed}:{task.id}")
    return list(task.edge_cases) + [task.random_case(r) for _ in range(n)]
