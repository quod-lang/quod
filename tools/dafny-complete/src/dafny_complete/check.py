"""The four Dafny passes: uniqueness (U), valid inputs (R), execution (run), witnesses (W)."""
from __future__ import annotations

import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from dafny_complete import values as V
from dafny_complete.parse import Method, find_datatypes, find_methods

MAX_CANDIDATE_INPUTS, MAX_INPUTS, MAX_NEIGHBOURS = 60, 24, 14


@dataclass
class Result:
    method: str
    line: int
    status: str  # determined | underspecified | inconclusive | skipped | error
    reason: str = ""
    witness: dict[str, Any] | None = None
    notes: list[str] = field(default_factory=list)


class Dafny:
    def __init__(self, exe: str, src: Path, time_limit: int, keep: bool):
        self.exe, self.src, self.time_limit, self.keep = exe, src, time_limit, keep
        self.files: list[Path] = []

    def _write(self, tag: str, text: str) -> Path:
        p = self.src.with_name(f".{self.src.stem}.dafny-complete.{tag}.dfy")
        p.write_text(text, encoding="utf-8")
        self.files.append(p)
        return p

    def verify(self, tag: str, text: str, symbol: str) -> tuple[str, set[int]]:
        p = self._write(tag, text)
        out = self._run(["verify", p.name, "--allow-warnings", "--filter-symbol", symbol,
                         "--verification-time-limit", str(self.time_limit)], p)
        lines = {int(m.group(1)) for m in re.finditer(rf"{re.escape(p.name)}\((\d+),\d+\): Error", out)}
        return out, lines

    def run(self, tag: str, text: str, main: str) -> str:
        p = self._write(tag, text)
        return self._run(["run", p.name, "--no-verify", "--allow-warnings", "-t", "py",
                          "--main-method", main], p, timeout=300)

    def _run(self, args: list[str], p: Path, timeout: int = 3600) -> str:
        try:
            r = subprocess.run([self.exe, *args], cwd=p.parent, capture_output=True, text=True,
                               encoding="utf-8", errors="replace", timeout=timeout)
            return r.stdout + r.stderr
        except subprocess.TimeoutExpired:
            return "TIMEOUT"

    def cleanup(self) -> None:
        if self.keep:
            return
        for p in self.files:
            p.unlink(missing_ok=True)
            build = p.with_name(p.stem + "-py")
            if build.is_dir():
                import shutil
                shutil.rmtree(build, ignore_errors=True)


def _insert(src: str, chunks: dict[int, list[str]]) -> str:
    for pos in sorted(chunks, reverse=True):
        src = src[:pos] + "\n" + "\n".join(chunks[pos]) + "\n" + src[pos:]
    return src


def _line_of(text: str, needle: str) -> int:
    return text.count("\n", 0, text.index(needle)) + 1


class Checker:
    def __init__(self, path: Path, dafny: str = "dafny", time_limit: int = 30,
                 keep: bool = False, only: list[str] | None = None):
        self.path, self.src = path, path.read_text(encoding="utf-8")
        self.d = Dafny(dafny, path, time_limit, keep)
        self.only = only

    # --- generated declarations -------------------------------------------------
    @staticmethod
    def _static(m: Method) -> str:
        # Generated members mirror the method: static next to a static method, instance members
        # (which see `this` and its fields) next to an instance method.
        return "static " if m.in_type and m.static else ""

    @staticmethod
    def _instance(m: Method) -> bool:
        return m.in_type is not None and not m.static

    def _contract_decls(self, i: int, m: Method) -> list[str]:
        s, tp, ind = self._static(m), m.type_params, m.indent
        ps = ", ".join(f"{n}: {t}" for n, t in m.params)
        pn = ", ".join(n for n, _ in m.params)
        sep = ", " if ps else ""
        a = [(f"{n}__a", t) for n, t in m.outs]
        b = [(f"{n}__b", t) for n, t in m.outs]
        req = " && ".join(f"({r})" for r in m.requires) or "true"
        ens = " && ".join(f"({e})" for e in m.ensures) or "true"
        outs = ", ".join(f"{n}: {t}" for n, t in m.outs)
        ab = ", ".join(f"{n}: {t}" for n, t in a + b)
        call = lambda o: ", ".join([n for n, _ in m.params] + [n for n, _ in o])  # noqa: E731
        # Arrays live on the heap: the predicates must declare that they read them, and two
        # array results are the same result when their contents are equal.
        eq = " && ".join(f"{x}[..] == {y}[..]" if _is_array1(t) else f"{x} == {y}"
                         for (x, t), (y, _) in zip(a, b))
        pre_reads = _reads([n for n, t in m.params if _is_array(t)])
        post_reads = _reads([n for n, t in m.params + m.outs if _is_array(t)])
        if self._instance(m) and m.in_type.kind in ("class", "trait"):
            # The contract may read any field, or call Valid()-style predicates over a
            # representation set: let the generated predicates read the whole heap.
            pre_reads = post_reads = " reads *"
        u = f"QuodCkU{i}_"
        return [
            f"{ind}{s}ghost predicate {u}Pre{tp}({ps}){pre_reads} {{ {req} }}",
            f"{ind}{s}ghost predicate {u}Post{tp}({ps}{sep}{outs}){post_reads} "
            f"requires {u}Pre({pn}) {{ {ens} }}",
            f"{ind}{s}lemma {u}Uniq{tp}({ps}{sep}{ab}) requires {u}Pre({pn}) "
            f"requires {u}Post({call(a)}) && {u}Post({call(b)}) ensures {eq} {{ }}",
        ]

    # --- passes -----------------------------------------------------------------
    def run(self, witness: bool = True) -> list[Result]:
        methods = find_methods(self.src)
        reg = V.registry()
        reg.clear()
        for name, (tps, ctors) in find_datatypes(self.src).items():
            reg[name] = V.DatatypeInfo(name, tps, ctors)
        if self.only:
            methods = [m for m in methods if m.name in self.only]
        results: dict[int, Result] = {}
        todo: dict[int, Method] = {}
        for i, m in enumerate(methods):
            r = Result(m.name, m.line, "")
            if not m.outs:
                r.status, r.reason = "skipped", "no outputs"
            elif not m.ensures:
                r.status, r.reason = "skipped", "no ensures clause"
            elif m.other_clauses or any(re.search(r"\b(old|fresh|unchanged|allocated)\s*\(", e)
                                        for e in m.ensures):
                r.status, r.reason = "skipped", ("modifies state: the contract relates the state "
                                                 "before and after the call (not supported yet)")
            else:
                todo[i] = m
            results[i] = r
        try:
            undetermined = self._pass_uniqueness(todo, results)
            searched: set[int] = set()
            if witness and undetermined:
                searched = self._pass_witness(undetermined, results)
            for i in undetermined:
                if not results[i].status:
                    results[i].status = "inconclusive"
                    results[i].reason = results[i].reason or (
                        "uniqueness not proved (witness search disabled)" if not witness else
                        "uniqueness not proved, no witness found" if i in searched else
                        "uniqueness not proved; no witness search possible (see note)")
        finally:
            self.d.cleanup()
        return [results[i] for i in sorted(results)]

    def _pass_uniqueness(self, todo: dict[int, Method], results: dict[int, Result]) -> dict[int, Method]:
        live = dict(todo)
        for _attempt in range(len(todo) + 1):
            if not live:
                return {}
            chunks: dict[int, list[str]] = {}
            for i, m in live.items():
                chunks.setdefault(m.insert_at, []).extend(self._contract_decls(i, m))
            text = _insert(self.src, chunks)
            out, err_lines = self.d.verify("uniq", text, "QuodCkU")
            spans = {i: {k: _line_of(text, f"QuodCkU{i}_{k}") for k in ("Pre", "Post", "Uniq")}
                     for i in live}
            if "resolution/type errors" in out or "parse errors" in out:
                bad = {i for i, sp in spans.items() if any(l in err_lines for l in sp.values())}
                if not bad:  # error outside generated code: the file itself does not resolve
                    for i in live:
                        results[i].status, results[i].reason = "error", "the file does not resolve: " + _first_error(out)
                    return {}
                for i in bad:
                    results[i].status = "error"
                    results[i].reason = "generated check does not typecheck: " + _first_error(out)
                    live.pop(i)
                continue
            undetermined = {}
            for i, m in live.items():
                sp = spans[i]
                if sp["Pre"] in err_lines or sp["Post"] in err_lines:
                    results[i].status = "error"
                    results[i].reason = "contract is not well-formed on its own: " + _first_error(out)
                elif sp["Uniq"] in err_lines or "TIMEOUT" in out:
                    undetermined[i] = m
                else:
                    results[i].status = "determined"
            return undetermined
        return {}

    def _plan(self, m: Method, res: Result) -> "_Plan | None":
        """How to search witnesses for m, or None (with a note) when it is not possible."""
        if m.ghost:
            res.notes.append("ghost method: cannot run it to search witnesses")
            return None
        try:
            pt = [V.parse_type(t) for _, t in m.params]
            ot = [V.parse_type(t) for _, t in m.outs]
        except V.Unsupported as e:
            res.notes.append(f"witness search skipped: unsupported type {e}")
            return None
        names = [n for n, _ in m.params]
        pd = [t for _, t in m.params]
        if not self._instance(m):
            return _Plan(m, pt, pd, names, ot, False, m.insert_at, self._static(m), m.indent,
                         m.qualifier)
        sc = m.in_type
        info = V.registry().get(sc.name)
        if sc.kind != "datatype" or info is None or info.tparams:
            res.notes.append("instance method: witness search would need to build objects "
                             "(supported for non-generic datatypes only)")
            return None
        # Instance method of a datatype: the receiver is one more input. The helper methods go
        # right after the datatype, at module level, and call `self.M(...)`.
        modules = ".".join(s.name for s in m.scope_chain if s.kind == "module")
        return _Plan(m, [V.parse_type(sc.name)] + pt, [sc.name] + pd, ["this"] + names, ot,
                     True, sc.end + 1, "", "", modules)

    def _pass_witness(self, und: dict[int, Method], results: dict[int, Result]) -> set[int]:
        """Search witnesses; returns the methods for which a search could actually run."""
        eligible: dict[int, _Plan] = {}
        for i, m in und.items():
            p = self._plan(m, results[i])
            if p is not None:
                eligible[i] = p
        if not eligible:
            return set()

        # R: which small inputs satisfy the precondition (proved, not assumed)?
        cands: dict[int, list[tuple]] = {}
        chunks: dict[int, list[str]] = {}
        for i, p in eligible.items():
            cands[i] = V.input_tuples(p.pt, MAX_CANDIDATE_INPUTS)
            chunks.setdefault(p.m.insert_at, []).extend(self._contract_decls(i, p.m)[:2])
            if p.m.requires:
                for k, x in enumerate(cands[i]):
                    stmts, recv, args = p.bind(x, "qa")
                    chunks.setdefault(p.at, []).append(
                        f"{p.indent}{p.static}method QuodCkR{i}_{k}() {{ " + " ".join(stmts)
                        + f" assert {recv}QuodCkU{i}_Pre({', '.join(args)}); }}")
        text = _insert(self.src, chunks)
        _, err = self.d.verify("pre", text, "QuodCkR")
        inputs: dict[int, list[tuple]] = {}
        for i, p in eligible.items():
            if p.m.requires:
                ok = [x for k, x in enumerate(cands[i])
                      if _line_of(text, f"QuodCkR{i}_{k}()") not in err]
            else:
                ok = cands[i]
            inputs[i] = _diverse(ok, MAX_INPUTS)
            if not inputs[i]:
                results[i].notes.append("no small input satisfies the precondition")

        # run: execute the method itself on those inputs to get a real answer
        answers: dict[int, list[tuple[tuple, Any]]] = {}
        for i, p in eligible.items():
            if not inputs[i]:
                continue
            got = self._execute(i, p, inputs[i], results[i]) if p.m.has_body else []
            if not p.m.has_body:
                results[i].notes.append("no body to run: candidate results are small values of "
                                        "the output type")
            # Without an answer from the method, candidates come from the output type alone; a
            # witness still needs two distinct values proved accepted, so it stays certain.
            answers[i] = got or [(x, None) for x in inputs[i][:6]]

        # W: prove Post(x, v) for the method's answer a and for candidates v != a (neighbours of
        # a, and values taken from the input). Two distinct values proved accepted = a witness.
        chunks, meta = {}, {}
        for i, p in eligible.items():
            chunks.setdefault(p.m.insert_at, []).extend(self._contract_decls(i, p.m)[:2])
            otype = p.ot[0] if len(p.ot) == 1 else ("tuple", p.ot)
            for xi, (x, a) in enumerate(answers.get(i, [])):
                in_stmts, recv, args = p.bind(x, "qa")
                if a is None:  # no answer from the method: try small values of the output type
                    seen: set = set()
                    pool = V.small_values(otype)[:MAX_NEIGHBOURS] + V.from_inputs(x, p.pt, otype)
                    vals = [b for b in pool if not (V.canon(b) in seen or seen.add(V.canon(b)))]
                else:
                    seen = {V.canon(a)}
                    pool = V.neighbours(a, otype)[:MAX_NEIGHBOURS] + V.from_inputs(x, p.pt, otype)
                    vals = [a] + [b for b in pool if not (V.canon(b) in seen or seen.add(V.canon(b)))]
                for ci, val in enumerate(vals):
                    name = f"QuodCkW{i}_{xi}_{ci}"
                    out_stmts, outs = V.bind([val] if len(p.ot) == 1 else list(val), p.ot,
                                             [t for _, t in p.m.outs], "qo")
                    chunks.setdefault(p.at, []).append(
                        f"{p.indent}{p.static}method {name}() {{ " + " ".join(in_stmts + out_stmts)
                        + f" assert {recv}QuodCkU{i}_Post({', '.join(args + outs)}); }}")
                    meta[name] = (i, xi, val)
        if not meta:
            return set(eligible)
        text = _insert(self.src, chunks)
        _, err = self.d.verify("witness", text, "QuodCkW")
        accepted: dict[tuple[int, int], list[Any]] = {}
        for name, (i, xi, val) in meta.items():
            if _line_of(text, f"method {name}()") not in err:
                accepted.setdefault((i, xi), []).append(val)
        for (i, xi), vals in sorted(accepted.items(), key=lambda kv: kv[0]):
            if results[i].status or len({V.canon(v) for v in vals}) < 2:
                continue
            x, a = answers[i][xi]
            first = a if a is not None and any(V.canon(v) == V.canon(a) for v in vals) else vals[0]
            second = next(v for v in vals if V.canon(v) != V.canon(first))
            p = eligible[i]
            results[i].status = "underspecified"
            results[i].witness = {
                "input": dict(zip(p.names, x)),
                "result_a": first, "result_b": second, "method_returns": a,
                "outputs": [n for n, _ in p.m.outs]}
        return set(eligible)

    def _execute(self, i: int, p: "_Plan", xs: list[tuple], res: Result) -> list[tuple[tuple, Any]]:
        pr = V.Printers(f"QuodCkP{i}_", p.static)
        body = []

        def show(t: Any, dt: str, var: str) -> str:
            if V.is_array(t):  # print an array as the sequence of its elements
                return f"{pr.name(('seq', t[1]), 'seq<' + V.elem_dafny_type(dt) + '>')}({var}[..]);"
            return f"{pr.name(t, dt)}({var});"

        for k, x in enumerate(xs):
            stmts, recv, args = p.bind(x, f"q{k}_", self_name=f"self{k}")
            outs = [f"r{k}_{j}" for j in range(len(p.ot))]
            body.extend(stmts)
            body.append(f"var {', '.join(outs)} := {recv}{p.m.name}({', '.join(args)});")
            body.append(f'print "QCOUT {k} ";')
            if len(p.ot) == 1:
                body.append(show(p.ot[0], p.m.outs[0][1], outs[0]))
            else:
                body.append('print "(";')
                for j, ((_, dt), t) in enumerate(zip(p.m.outs, p.ot)):
                    if j:
                        body.append('print ", ";')
                    body.append(show(t, dt, outs[j]))
                body.append('print ")";')
            body.append('print "\\n";')
        main = f"{p.indent}{p.static}method QuodCkM{i}() {{ " + " ".join(body) + " }"
        text = _insert(self.src, {p.at: [*pr.code, main]})
        # A bodiless method anywhere in the file would stop the whole program from compiling:
        # mark them {:extern} for this run only (they are never called).
        for b in sorted((x for x in find_methods(text) if not x.has_body and not x.ghost),
                        key=lambda x: x.name_pos, reverse=True):
            text = text[:b.name_pos] + "{:extern} " + text[b.name_pos:]
        qual = (p.qual + "." if p.qual else "") + f"QuodCkM{i}"
        out = self.d.run(f"run{i}", text, qual)
        got = {}
        for line in out.splitlines():
            mm = re.match(r"QCOUT (\d+) (.*)$", line)
            if mm:
                try:
                    got[int(mm.group(1))] = V.read_value(mm.group(2))
                except (ValueError, IndexError, KeyError):
                    pass
        if not got:
            res.notes.append("could not run the method to obtain reference answers: "
                             + _first_error(out))
        return [(xs[k], got[k]) for k in sorted(got)]


@dataclass
class _Plan:
    """Everything the witness search needs to know about one method."""
    m: Method
    pt: list           # input types; for a datatype instance method, the receiver comes first
    pd: list[str]      # the same as Dafny type strings
    names: list[str]   # input names shown in the witness ("this" for the receiver)
    ot: list           # output types
    recv: bool         # True: x[0] is the receiver, calls are `self.M(...)`
    at: int            # where helper methods are inserted
    static: str        # "static " when helpers live next to a static method
    indent: str
    qual: str          # qualifier of the helpers' scope, for --main-method

    def bind(self, x: tuple, prefix: str, self_name: str = "self") -> tuple[list[str], str, list[str]]:
        """Statements, receiver prefix ("self." or ""), and argument expressions for input x."""
        stmts, args = V.bind(list(x), self.pt, self.pd, prefix)
        if not self.recv:
            return stmts, "", args
        return stmts + [f"var {self_name} := {args[0]};"], f"{self_name}.", args[1:]


def _is_array(dafny_type: str) -> bool:
    return re.match(r"array\d*\s*<", dafny_type) is not None


def _is_array1(dafny_type: str) -> bool:
    return re.match(r"array\s*<", dafny_type) is not None


def _reads(names: list[str]) -> str:
    return f" reads {', '.join(names)}" if names else ""


def _diverse(xs: list[tuple], k: int) -> list[tuple]:
    """Pick up to k inputs, greedily preferring ones that bring values not seen yet
    (inputs are sorted smallest first, so ties keep the small ones)."""
    seen: list[set] = [set() for _ in (xs[0] if xs else ())]
    pool, out = list(xs), []
    while pool and len(out) < k:
        best = max(pool, key=lambda x: sum(repr(v) not in s for v, s in zip(x, seen)))
        pool.remove(best)
        out.append(best)
        for v, s in zip(best, seen):
            s.add(repr(v))
    return out


def _first_error(out: str) -> str:
    for line in out.splitlines():
        if line.startswith("Prover error:"):  # Z3 model-parsing noise, not the actual error
            continue
        if "Error" in line or "error" in line:
            return line.strip()[:200]
    return out.strip().splitlines()[-1][:200] if out.strip() else "no output"
