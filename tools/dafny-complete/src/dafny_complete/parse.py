"""Locate methods and their contracts in Dafny source.

Not a full Dafny parser: it masks comments, string/char literals and attributes (keeping every
offset and newline), then works on bracket structure. Expressions are always copied verbatim
from the comment-free source, so nothing is rewritten.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field

_CHAR_LIT = re.compile(r"'(\\U\{[0-9a-fA-F_]+\}|\\u[0-9a-fA-F]{4}|\\.|[^'\\\n])'")


def _blank(buf: list[str], a: int, b: int) -> None:
    for k in range(a, b):
        if buf[k] != "\n":
            buf[k] = " "


def mask(src: str, literals: bool) -> str:
    """Blank comments; with literals=True also string/char literals and {:attributes}."""
    buf, i, n = list(src), 0, len(src)
    while i < n:
        c = src[i]
        if src.startswith("//", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            _blank(buf, i, j)
            i = j
        elif src.startswith("/*", i):
            depth, j = 0, i
            while j < n:
                if src.startswith("/*", j):
                    depth, j = depth + 1, j + 2
                elif src.startswith("*/", j):
                    depth, j = depth - 1, j + 2
                    if depth == 0:
                        break
                else:
                    j += 1
            _blank(buf, i, j)
            i = j
        elif c == '"' or (c == "@" and src.startswith('@"', i)):
            verbatim = c == "@"
            j = i + (2 if verbatim else 1)
            while j < n:
                if verbatim and src[j] == '"':
                    if src.startswith('""', j):
                        j += 2
                        continue
                    j += 1
                    break
                if not verbatim and src[j] == "\\":
                    j += 2
                    continue
                if not verbatim and src[j] == '"':
                    j += 1
                    break
                j += 1
            if literals:
                _blank(buf, i, j)
            i = j
        elif c == "'":
            prev = src[i - 1] if i else " "
            m = None if (prev.isalnum() or prev in "_'?") else _CHAR_LIT.match(src, i)
            if m:
                if literals:
                    _blank(buf, i, m.end())
                i = m.end()
            else:
                i += 1  # a prime in an identifier such as x'
        else:
            i += 1
    out = "".join(buf)
    if literals:  # attributes {: ... } can sit anywhere in a declaration header
        res = list(out)
        for m in re.finditer(r"\{:", out):
            depth = 0
            for j in range(m.start(), len(out)):
                if out[j] == "{":
                    depth += 1
                elif out[j] == "}":
                    depth -= 1
                    if depth == 0:
                        _blank(res, m.start(), j + 1)
                        break
        out = "".join(res)
    return out


def match_close(s: str, i: int, open_: str = "(", close: str = ")") -> int:
    depth = 0
    for j in range(i, len(s)):
        if s[j] == open_:
            depth += 1
        elif s[j] == close:
            depth -= 1
            if depth == 0:
                return j
    raise ValueError(f"unbalanced {open_}{close}")


def split_params(text: str) -> list[tuple[str, str]]:
    parts, depth, cur = [], 0, ""
    for c in text:
        depth += c in "(<["
        depth -= c in ")>]"
        if c == "," and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += c
    if cur.strip():
        parts.append(cur)
    out = []
    for p in parts:
        p = re.sub(r"^\s*(ghost|nameonly|older)\s+", "", p.strip())
        name, typ = p.split(":", 1)
        typ = re.sub(r":=.*$", "", typ)  # default values
        out.append((name.strip(), " ".join(typ.split())))
    return out


@dataclass
class Scope:
    kind: str  # module | class | trait | datatype | block
    name: str
    start: int
    end: int


@dataclass
class Method:
    name: str
    line: int
    static: bool
    ghost: bool
    type_params: str  # e.g. "<T(==)>" or ""
    params: list[tuple[str, str]]
    outs: list[tuple[str, str]]
    requires: list[str]
    ensures: list[str]
    other_clauses: list[str]  # modifies / reads / decreases keywords seen
    insert_at: int  # offset where generated declarations go (after the method)
    name_pos: int   # offset of the method name
    has_body: bool
    indent: str
    scope_chain: list[Scope] = field(default_factory=list)

    @property
    def in_type(self) -> Scope | None:
        types = [s for s in self.scope_chain if s.kind in ("class", "trait", "datatype")]
        return types[-1] if types else None

    @property
    def qualifier(self) -> str:
        names = [s.name for s in self.scope_chain if s.kind != "block"]
        return ".".join(names)


_SCOPE_HEAD = re.compile(
    r"\b(module|class|trait|datatype|codatatype|newtype)\s+([A-Za-z_][\w.]*)")
_DECL = re.compile(r"\b(method|function|lemma|predicate|constructor|class|module|datatype|"
                   r"codatatype|const|type|trait|iterator|newtype|import)\b")


def scopes(s: str) -> list[Scope]:
    out, stack = [], []
    for m in re.finditer(r"[{}]", s):
        if m.group() == "{":
            k = m.start()
            back = max(s.rfind(";", 0, k), s.rfind("{", 0, k), s.rfind("}", 0, k))
            header = s[back + 1:k]
            # The last keyword wins: a brace-less declaration (`newtype Odd = ... witness 3`)
            # can precede `trait T {` in the same header text.
            heads = list(_SCOPE_HEAD.finditer(header))
            h = heads[-1] if heads else None
            if h and not re.search(r"\b(method|function|lemma|predicate)\b", header):
                kind = "datatype" if h.group(1) in ("codatatype", "newtype") else h.group(1)
                stack.append(Scope(kind, h.group(2), k, -1))
            else:
                stack.append(Scope("block", "", k, -1))
        elif stack:
            sc = stack.pop()
            sc.end = m.start()
            out.append(sc)
    return out


def _body_start(s: str, i: int) -> tuple[int | None, int]:
    """Find a method body '{' from offset i. Returns (brace offset or None, end of spec)."""
    depth, j = 0, i
    while j < len(s):
        c = s[j]
        if c in "([":
            depth += 1
        elif c in ")]":
            depth -= 1
        elif c == "{" and depth > 0:
            j = match_close(s, j, "{", "}")  # set/map display inside parentheses
        elif depth == 0 and c == "}":
            return None, j  # end of enclosing scope: bodiless method
        elif depth == 0 and c == "{":
            prev = s[:j].rstrip()
            # After an operator, '{' opens a set/map display. A single '|' closes a
            # cardinality |xs| (a value), whereas '||' is the boolean operator.
            after_op = bool(prev) and (prev[-1] in "=<>+-*&!,(:" or prev.endswith("||")
                                       or re.search(r"(^|[^\w])!?in$", prev) is not None)
            if after_op:
                j = match_close(s, j, "{", "}")  # set/map display in a clause, not a body
            else:
                return j, j
        elif depth == 0 and _DECL.match(s, j) and (j == 0 or not (s[j - 1].isalnum() or s[j - 1] == "_")):
            return None, j  # next declaration: bodiless method
        j += 1
    return None, len(s)


def find_methods(src: str) -> list[Method]:
    code = mask(src, literals=False)  # comments gone, literals kept: source of expressions
    s = mask(src, literals=True)      # structure only
    all_scopes = scopes(s)
    found = []
    for m in re.finditer(r"\bmethod\s+([A-Za-z_][\w']*)", s):
        try:
            found.extend(_one_method(src, code, s, m, all_scopes))
        except ValueError:
            continue  # a header we do not understand: leave that method out
    return found


def _one_method(src: str, code: str, s: str, m: re.Match, all_scopes: list[Scope]) -> list[Method]:
    """Parse one method header and contract. Raises ValueError on a header it does not
    understand (e.g. refinement syntax `method Foo...`)."""
    name, k = m.group(1), m.end()
    line_start = s.rfind("\n", 0, m.start()) + 1
    mods = s[line_start:m.start()]
    indent = re.match(r"[ \t]*", src[line_start:]).group(0)
    tp = ""
    rest = s[k:]
    if rest.lstrip().startswith("<"):
        a = k + (len(rest) - len(rest.lstrip()))
        b = match_close(s, a, "<", ">")
        tp, k = code[a:b + 1], b + 1
    if not s[k:].lstrip().startswith("("):
        raise ValueError(f"method {name}: no parameter list (refinement syntax?)")
    p_open = s.index("(", k)
    p_close = match_close(s, p_open)
    params = split_params(code[p_open + 1:p_close])
    outs, spec_from = [], p_close + 1
    r = re.compile(r"\s*returns\s*\(").match(s, p_close + 1)
    if r:
        r_close = match_close(s, r.end() - 1)
        outs = split_params(code[r.end():r_close])
        spec_from = r_close + 1
    body, spec_end = _body_start(s, spec_from)
    insert_at = match_close(s, body, "{", "}") + 1 if body is not None else spec_end
    clauses: list[tuple[str, str]] = []
    depth, last_kw, last_pos = 0, None, 0
    region = s[spec_from:spec_end]
    for mm in re.finditer(r"[()\[\]]|\b(requires|ensures|modifies|decreases|reads)\b", region):
        tok = mm.group(0)
        if tok in "([":
            depth += 1
        elif tok in ")]":
            depth -= 1
        elif depth == 0:
            if last_kw:
                clauses.append((last_kw, code[spec_from + last_pos:spec_from + mm.start()]))
            last_kw, last_pos = tok, mm.end()
    if last_kw:
        clauses.append((last_kw, code[spec_from + last_pos:spec_end]))
    # Drop clause labels (`requires L: e`) and the trailing ';' of older Dafny syntax.
    clean = lambda e: re.sub(r"^\s*\w+\s*:(?!=)", "", " ".join(e.split())).rstrip(";").rstrip()  # noqa: E731
    chain = sorted((sc for sc in all_scopes if sc.start < m.start() < sc.end),
                   key=lambda sc: sc.start)
    return [Method(
        name=name, line=src.count("\n", 0, m.start()) + 1,
        static="static" in mods.split(), ghost="ghost" in mods.split(),
        type_params=tp, params=params, outs=outs,
        requires=[clean(e) for kw, e in clauses if kw == "requires"],
        ensures=[clean(e) for kw, e in clauses if kw == "ensures"],
        other_clauses=sorted({kw for kw, _ in clauses if kw in ("modifies", "reads")}),
        insert_at=insert_at, name_pos=m.start(1), has_body=body is not None,
        indent=indent, scope_chain=chain)]
