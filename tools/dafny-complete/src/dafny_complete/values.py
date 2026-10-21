"""Dafny value types supported by the witness search: parsing type strings, writing literals,
generating small inputs and neighbouring outputs, printing values from Dafny and reading them back.

Supported: int, nat, bool, char, string, seq<T>, array<T>, tuples (T1, ..., Tn), and the
datatypes declared in the checked file (see registry()).
"""
from __future__ import annotations

import itertools
import re
import threading
from dataclasses import dataclass, field
from typing import Any, Iterator

Type = Any  # 'int' | 'nat' | 'bool' | 'char' | 'string' | ('seq', T) | ('array', T)
#              | ('tuple', [T...]) | ('dt', written_name, (type arg strings...))
SCALARS = ("int", "nat", "bool", "char", "string")


class Unsupported(Exception):
    pass


# --- datatypes ---------------------------------------------------------------------

@dataclass
class DatatypeInfo:
    name: str
    tparams: list[str]
    ctors: list[tuple[str, list[str]]]  # (constructor, field type strings)


_tls = threading.local()  # one registry per thread: several files may be checked in parallel


def registry() -> dict[str, DatatypeInfo]:
    """Datatypes of the file being checked (by this thread)."""
    if not hasattr(_tls, "dt"):
        _tls.dt = {}
    return _tls.dt


@dataclass(frozen=True)
class DVal:
    """A datatype value: constructor name and arguments."""
    ctor: str
    args: tuple = field(default=())

    def __repr__(self) -> str:
        return self.ctor + (f"({', '.join(map(repr, self.args))})" if self.args else "")


def _subst(type_str: str, tparams: list[str], targs: tuple) -> str:
    if not tparams:
        return type_str
    m = dict(zip(tparams, targs))
    return re.sub(r"\b(" + "|".join(map(re.escape, tparams)) + r")\b", lambda g: m[g.group(1)], type_str)


def ctor_fields(t: Type) -> list[tuple[str, list[str]]]:
    """Constructors of datatype type t, with field types instantiated (as Dafny strings)."""
    info = registry()[t[1].split(".")[-1]]
    return [(c, [_subst(f, info.tparams, t[2]) for f in fs]) for c, fs in info.ctors]


def _ctor_types(fs: list[str]) -> list[Type] | None:
    try:
        return [parse_type(f) for f in fs]
    except Unsupported:
        return None


def _split_top(s: str) -> list[str]:
    parts, depth, cur = [], 0, ""
    for c in s:
        depth += c in "(<["
        depth -= c in ")>]"
        if c == "," and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += c
    parts.append(cur)
    return [p.strip() for p in parts]


def parse_type(t: str) -> Type:
    t = " ".join(t.split())
    if t in SCALARS:
        return t
    if t.startswith("seq<") and t.endswith(">"):
        return ("seq", parse_type(t[4:-1]))
    if t.startswith("array<") and t.endswith(">"):
        inner = parse_type(t[6:-1])
        if is_array(inner) or (isinstance(inner, tuple) and any(is_array(x) for x in iter_types(inner))):
            raise Unsupported(t)  # arrays of arrays: not supported
        return ("array", inner)
    if t.startswith("(") and t.endswith(")"):
        parts = _split_top(t[1:-1])
        if len(parts) == 1:
            return parse_type(parts[0])
        return ("tuple", [parse_type(p) for p in parts])
    m = re.fullmatch(r"([A-Za-z_][\w.']*)\s*(?:<(.*)>)?", t)
    if m and m.group(1).split(".")[-1] in registry():
        info = registry()[m.group(1).split(".")[-1]]
        targs = tuple(_split_top(m.group(2))) if m.group(2) else ()
        if len(targs) != len(info.tparams):
            raise Unsupported(t)
        return ("dt", m.group(1), targs)
    raise Unsupported(t)


def is_dt(t: Type) -> bool:
    return isinstance(t, tuple) and t[0] == "dt"


def is_array(t: Type) -> bool:
    return isinstance(t, tuple) and t[0] == "array"


def supported(t: str) -> bool:
    try:
        parse_type(t)
        return True
    except Unsupported:
        return False


# --- literals ------------------------------------------------------------------

def _char_body(c: str) -> str:
    if c in "\\\"'":
        return "\\" + c
    if c == "\n":
        return "\\n"
    if not c.isprintable() or ord(c) > 0x7E:
        return "\\U{%X}" % ord(c)
    return c


def lit(v: Any, t: Type) -> str:
    if t == "bool":
        return "true" if v else "false"
    if t in ("int", "nat"):
        return f"({v})" if v < 0 else str(v)
    if t == "char":
        return "'" + _char_body(v) + "'"
    if t == "string":
        return '"' + "".join(_char_body(c) for c in v) + '"'
    if t[0] == "seq":
        return "[" + ", ".join(lit(x, t[1]) for x in v) + "]"
    if t[0] == "tuple":
        if any(is_array(x) for x in iter_types(t)):
            raise Unsupported("array inside a tuple")
        return "(" + ", ".join(lit(x, s) for x, s in zip(v, t[1])) + ")"
    if t[0] == "dt":
        fs = dict(ctor_fields(t))[v.ctor]
        qual = t[1].split("<")[0] + "." + v.ctor  # qualified: avoids clashes with other names
        if not v.args:
            return qual
        return qual + "(" + ", ".join(lit(a, parse_type(f)) for a, f in zip(v.args, fs)) + ")"
    raise Unsupported(t)  # arrays are not expressions: use bind()


def elem_dafny_type(dafny_type: str) -> str:
    d = " ".join(dafny_type.split())
    return d[d.index("<") + 1:-1]


def bind(vals: list[Any], types: list[Type], dafny_types: list[str], prefix: str
         ) -> tuple[list[str], list[str]]:
    """Statements allocating array arguments, and the argument expressions to use.
    Arrays need `new`, which only methods can do: the caller must place the statements
    in a method body."""
    stmts, args = [], []
    for j, (v, t, d) in enumerate(zip(vals, types, dafny_types)):
        if is_array(t):
            name = f"{prefix}{j}"
            e = elem_dafny_type(d)
            stmts.append(f"var {name} := new {e}[0];" if not v else
                         f"var {name} := new {e}[] [{', '.join(lit(x, t[1]) for x in v)}];")
            # Mention every element: quantifiers like `exists i :: a[i] == x` need a term
            # a[k] to instantiate, and an allocation alone does not provide one.
            stmts.extend(f"assert {name}[{k}] == {lit(x, t[1])};" for k, x in enumerate(v))
            args.append(name)
        else:
            args.append(lit(v, t))
    return stmts, args


# --- small inputs ----------------------------------------------------------------

def small_values(t: Type, depth: int = 0) -> list[Any]:
    if t in ("int", "nat"):
        return [0, 1, 2, -1, 3]
    if t == "bool":
        return [False, True]
    if t == "char":
        return ["a", "0", " "]
    if t == "string":
        return ["", "a", "ab", "0", "10", "-1", "a/b", "aa"]
    if t[0] == "dt":
        return _small_dt(t, depth)
    if t[0] in ("seq", "array"):
        e = small_values(t[1], depth)
        if not e:
            return [[]]
        e0, e1, e2, e3 = e[0], e[1 % len(e)], e[2 % len(e)], e[3 % len(e)]
        # e3 is a negative int, or a second element of the same size as e2 for sequences:
        # it gives inputs with negatives, and ties (two different elements of equal length).
        return [[], [e1], [e0, e1], [e1, e0], [e1, e1], [e0, e1, e2], [e1, e3], [e2, e3],
                [e0, e0, e1]]
    if t[0] == "tuple":
        return [tuple(c) for c in itertools.islice(
            itertools.product(*(small_values(s, depth)[:3] for s in t[1])), 8)]
    raise Unsupported(t)


def _small_dt(t: Type, depth: int) -> list[Any]:
    """A few values per constructor, round-robin so every constructor shows up early.
    Recursion (trees, lists) is cut at depth 2 by keeping only constructors whose fields
    are not datatypes."""
    per_ctor = []
    for c, fs in ctor_fields(t):
        types = _ctor_types(fs)
        if types is None:
            continue  # a field type we cannot generate: leave this constructor out
        if depth >= 2 and any(is_dt(x) or (isinstance(x, tuple) and any(is_dt(y) for y in iter_types(x)))
                              for x in types):
            continue
        pools = [small_values(x, depth + 1)[:2] for x in types]
        per_ctor.append([DVal(c, tuple(args)) for args in itertools.islice(itertools.product(*pools), 3)])
    out = []
    for k in range(3):
        out.extend(vals[k] for vals in per_ctor if k < len(vals))
    return out[:8]


def input_tuples(types: list[Type], limit: int) -> list[tuple]:
    """At most `limit` small argument tuples. Greedy: each pick brings as many values not seen
    yet (per argument) as possible, smaller tuples first on ties, so that unusual values
    (negatives, ties, duplicates) are not crowded out by the many tiny combinations."""
    pools = [small_values(t) for t in types]
    combos = list(itertools.islice(itertools.product(*pools), 4000))
    combos.sort(key=lambda c: len(repr(c)))
    seen: list[set] = [set() for _ in types]
    picked, rest = [], combos
    while rest and len(picked) < limit:
        best = max(rest, key=lambda c: sum(repr(v) not in s for v, s in zip(c, seen)))
        rest = [c for c in rest if c is not best]
        picked.append(best)
        for v, s in zip(best, seen):
            s.add(repr(v))
    return picked


# --- neighbours of a result ------------------------------------------------------

def _alt_char(c: str) -> str:
    if c.isdigit():
        return str((int(c) + 1) % 10)
    if c == " ":
        return "x"
    return "b" if c != "b" else "c"


def neighbours(v: Any, t: Type) -> list[Any]:
    if t == "bool":
        return [not v]
    if t in ("int", "nat"):
        return [v + 1, v - 1, 0, -v]
    if t == "char":
        return [_alt_char(v)]
    if t == "string":
        out = [v + "x", v + "1", v[:-1], "", v[::-1], v + v[-1:]]
        for i in sorted({0, len(v) // 2, len(v) - 1}):
            if 0 <= i < len(v):
                out.append(v[:i] + _alt_char(v[i]) + v[i + 1:])
        return out
    if t[0] in ("seq", "array"):
        v = list(v)
        out = [[], v[:-1], v[::-1]]
        if v:
            out.append(v + [v[-1]])
            for i in sorted({0, len(v) - 1}):
                for alt in neighbours(v[i], t[1])[:2]:
                    out.append(v[:i] + [alt] + v[i + 1:])
        return out
    if t[0] == "tuple":
        out = []
        for i, s in enumerate(t[1]):
            for alt in neighbours(v[i], s)[:2]:
                out.append(tuple(v[:i]) + (alt,) + tuple(v[i + 1:]))
        return out
    if t[0] == "dt":
        out = [x for x in _small_dt(t, 1) if x.ctor != v.ctor]  # another constructor
        fs = dict(ctor_fields(t)).get(v.ctor, [])
        types = _ctor_types(fs) or []
        for i, ft in enumerate(types):  # same constructor, one argument changed
            for alt in neighbours(v.args[i], ft)[:2]:
                out.append(DVal(v.ctor, v.args[:i] + (alt,) + v.args[i + 1:]))
        return out
    raise Unsupported(t)


def from_inputs(args: tuple, arg_types: list[Type], out_type: Type) -> list[Any]:
    """Candidate results taken from the input itself: an argument of the result's type, or an
    element of a sequence/array argument whose elements have the result's type (a 'pick one of
    the inputs' contract often leaves the choice open)."""
    out = []
    for v, t in zip(args, arg_types):
        if t == out_type or (is_array(t) and out_type == ("seq", t[1])):
            out.append(list(v) if is_array(t) else v)
        if isinstance(t, tuple) and t[0] in ("seq", "array") and t[1] == out_type:
            out.extend(v)
        if t == "string" and out_type == "char":
            out.extend(v)
    return out


def canon(v: Any) -> Any:
    if isinstance(v, DVal):
        return ("#dt", v.ctor, canon(v.args))
    if isinstance(v, (list, tuple)):
        return tuple(canon(x) for x in v)
    return v


# --- printing from Dafny, reading back -------------------------------------------

class Printers:
    """Generates Dafny methods that print values in a format `read_value` can parse."""

    def __init__(self, prefix: str, static: str):
        self.prefix, self.static, self.names, self.code = prefix, static, {}, []

    def name(self, t: Type, dafny_type: str) -> str:
        key = repr(t)
        if key in self.names:
            return self.names[key]
        n = f"{self.prefix}P{len(self.names)}"
        self.names[key] = n
        s = self.static
        if t in ("int", "nat", "bool"):
            body = "print v;"
        elif t == "char":
            body = 'print "\'"; QC__PC(v); print "\'";'
            self._need_char()
        elif t == "string":
            body = 'print "\\""; for i := 0 to |v| { QC__PC(v[i]); } print "\\"";'
            self._need_char()
        elif t[0] == "seq":
            inner = self.name(t[1], seq_elem_type(dafny_type))
            body = (f'print "["; for i := 0 to |v| {{ if i > 0 {{ print ", "; }} {inner}(v[i]); }} '
                    f'print "]";')
        elif t[0] == "dt":
            cases = []
            for c, fs in ctor_fields(t):
                types = _ctor_types(fs)
                if not fs:
                    cases.append(f'case {c} => {{ print "{c}"; }}')
                elif types is None:  # a field we cannot print: the reader will reject "?"
                    cases.append(f'case {c}({", ".join("_" for _ in fs)}) => {{ print "?"; }}')
                else:
                    names = [f"f{k}" for k in range(len(fs))]
                    calls = []
                    for k, (ft, fd) in enumerate(zip(types, fs)):
                        if k:
                            calls.append('print ", ";')
                        calls.append(f"{self.name(ft, fd)}({names[k]});")
                    cases.append(f'case {c}({", ".join(names)}) => {{ print "{c}("; '
                                 + " ".join(calls) + ' print ")"; }')
            body = "match v { " + " ".join(cases) + " }"
        else:  # tuple
            comps = tuple_comp_types(dafny_type)
            calls = []
            for k, (ct, cd) in enumerate(zip(t[1], comps)):
                if k:
                    calls.append('print ", ";')
                calls.append(f"{self.name(ct, cd)}(v.{k});")
            body = 'print "("; ' + " ".join(calls) + ' print ")";'
        self.code.append(f"  {s}method {n}(v: {dafny_type}) {{ {body} }}")
        return n

    def _need_char(self) -> None:
        if "char" not in self.names:
            self.names["char"] = "QC__PC"
            s = self.static
            # Escape quotes and backslashes; non-ASCII as \U{decimal} so the reader stays simple.
            # A char is printed as the one-char string [c]: `print c` quotes it on some targets.
            self.code.append(
                f"  {s}method QC__PC(c: char) {{ if c == '\\\\' || c == '\"' || c == '\\'' "
                f"{{ print \"\\\\\", [c]; }} else if 32 <= c as int < 127 {{ print [c]; }} "
                f"else {{ print \"\\\\U{{\", c as int, \"}}\"; }} }}")


def seq_elem_type(dafny_type: str) -> str:
    d = " ".join(dafny_type.split())
    if d == "string":
        return "char"
    return d[4:-1]


def tuple_comp_types(dafny_type: str) -> list[str]:
    d = " ".join(dafny_type.split())
    return _split_top(d[1:-1])


_TOKEN = re.compile(r'\s*(-?\d+|"(?:[^"\\]|\\.|\\U\{\d+\})*"|\'(?:[^\'\\]|\\.|\\U\{\d+\})\'|'
                    r"[A-Za-z_][\w']*|[\[\](),])")


def _unescape(body: str) -> str:
    out, i = [], 0
    while i < len(body):
        if body[i] == "\\":
            if body.startswith("\\U{", i):
                j = body.index("}", i)
                out.append(chr(int(body[i + 3:j])))
                i = j + 1
            else:
                out.append(body[i + 1])
                i += 2
        else:
            out.append(body[i])
            i += 1
    return "".join(out)


def read_value(text: str) -> Any:
    toks = []
    pos = 0
    while pos < len(text.rstrip()):
        m = _TOKEN.match(text, pos)
        if not m:
            raise ValueError(f"cannot read value at {text[pos:pos + 20]!r}")
        toks.append(m.group(1))
        pos = m.end()

    def parse(i: int) -> tuple[Any, int]:
        tok = toks[i]
        if tok == "[" or tok == "(":
            close = "]" if tok == "[" else ")"
            items, i = [], i + 1
            while toks[i] != close:
                v, i = parse(i)
                items.append(v)
                if toks[i] == ",":
                    i += 1
            return (items if tok == "[" else tuple(items)), i + 1
        if tok in ("true", "false"):
            return tok == "true", i + 1
        if tok[0].isalpha() or tok[0] == "_":  # a datatype constructor, with or without args
            if i + 1 < len(toks) and toks[i + 1] == "(":
                args, j = [], i + 2
                while toks[j] != ")":
                    v, j = parse(j)
                    args.append(v)
                    if toks[j] == ",":
                        j += 1
                return DVal(tok, tuple(args)), j + 1
            return DVal(tok), i + 1
        if tok[0] == '"':
            return _unescape(tok[1:-1]), i + 1
        if tok[0] == "'":
            return _unescape(tok[1:-1]), i + 1
        return int(tok), i + 1

    v, _ = parse(0)
    return v


def iter_types(t: Type) -> Iterator[Type]:
    """t and its component types (not looking inside datatypes, which may be recursive)."""
    yield t
    if isinstance(t, tuple) and t[0] != "dt":
        for s in (t[1] if t[0] == "tuple" else [t[1]]):
            yield from iter_types(s)
