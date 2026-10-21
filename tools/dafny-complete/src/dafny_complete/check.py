"""The four Dafny passes: uniqueness (U), valid inputs (R), execution (run), witnesses (W)."""
from __future__ import annotations

import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from dafny_complete import values as V
from dafny_complete.parse import Method, find_methods

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
        return "static " if m.in_type else ""

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
            elif m.in_type and not m.static:
                r.status, r.reason = "skipped", "instance method (heap state not supported yet)"
            elif m.other_clauses or any(re.search(r"\b(old|fresh|unchanged|allocated)\s*\(", e)
                                        for e in m.ensures):
                r.status, r.reason = "skipped", "touches the heap (modifies/reads/old)"
            else:
                todo[i] = m
            results[i] = r
        try:
            undetermined = self._pass_uniqueness(todo, results)
            if witness and undetermined:
                self._pass_witness(undetermined, results)
            for i in undetermined:
                if not results[i].status:
                    results[i].status = "inconclusive"
                    results[i].reason = results[i].reason or (
                        "uniqueness not proved, no witness found" if witness
                        else "uniqueness not proved (witness search disabled)")
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

    def _pass_witness(self, und: dict[int, Method], results: dict[int, Result]) -> None:
        eligible: dict[int, tuple[Method, list, list]] = {}
        for i, m in und.items():
            if m.ghost:
                results[i].notes.append("ghost method: cannot run it to search witnesses")
                continue
            try:
                pt = [V.parse_type(t) for _, t in m.params]
                ot = [V.parse_type(t) for _, t in m.outs]
            except V.Unsupported as e:
                results[i].notes.append(f"witness search skipped: unsupported type {e}")
                continue
            eligible[i] = (m, pt, ot)
        if not eligible:
            return

        # R: which small inputs satisfy the precondition (proved, not assumed)?
        cands: dict[int, list[tuple]] = {}
        chunks: dict[int, list[str]] = {}
        for i, (m, pt, _) in eligible.items():
            cands[i] = V.input_tuples(pt, MAX_CANDIDATE_INPUTS)
            decls = self._contract_decls(i, m)[:2]
            if m.requires:
                for k, x in enumerate(cands[i]):
                    stmts, args = V.bind(list(x), pt, [t for _, t in m.params], "qa")
                    decls.append(f"{m.indent}{self._static(m)}method QuodCkR{i}_{k}() {{ "
                                 + " ".join(stmts)
                                 + f" assert QuodCkU{i}_Pre({', '.join(args)}); }}")
            chunks.setdefault(m.insert_at, []).extend(decls)
        text = _insert(self.src, chunks)
        _, err = self.d.verify("pre", text, "QuodCkR")
        inputs: dict[int, list[tuple]] = {}
        for i, (m, _, _) in eligible.items():
            if m.requires:
                ok = [x for k, x in enumerate(cands[i])
                      if _line_of(text, f"QuodCkR{i}_{k}()") not in err]
            else:
                ok = cands[i]
            inputs[i] = _diverse(ok, MAX_INPUTS)
            if not inputs[i]:
                results[i].notes.append("no small input satisfies the precondition")

        # run: execute the method itself on those inputs to get a real answer
        answers: dict[int, list[tuple[tuple, Any]]] = {}
        for i, (m, pt, ot) in eligible.items():
            if not inputs[i]:
                continue
            answers[i] = self._execute(i, m, pt, ot, inputs[i], results[i])

        # W: prove Post(x, v) for the method's answer a and for candidates v != a (neighbours of
        # a, and values taken from the input). Two distinct values proved accepted = a witness.
        chunks, meta = {}, {}
        for i, (m, pt, ot) in eligible.items():
            decls = self._contract_decls(i, m)[:2]
            otype = ot[0] if len(ot) == 1 else ("tuple", ot)
            for xi, (x, a) in enumerate(answers.get(i, [])):
                in_stmts, args = V.bind(list(x), pt, [t for _, t in m.params], "qa")

                def check_method(name: str, val: Any) -> str:
                    vals = [val] if len(ot) == 1 else list(val)
                    out_stmts, outs = V.bind(vals, ot, [t for _, t in m.outs], "qo")
                    return (f"{m.indent}{self._static(m)}method {name}() {{ "
                            + " ".join(in_stmts + out_stmts)
                            + f" assert QuodCkU{i}_Post({', '.join(args + outs)}); }}")
                seen = {V.canon(a)}
                pool = V.neighbours(a, otype)[:MAX_NEIGHBOURS] + V.from_inputs(x, pt, otype)
                cands = [a] + [b for b in pool if not (V.canon(b) in seen or seen.add(V.canon(b)))]
                for ci, val in enumerate(cands):
                    name = f"QuodCkW{i}_{xi}_{ci}"
                    decls.append(check_method(name, val))
                    meta[name] = (i, xi, x, a, val)
            chunks.setdefault(m.insert_at, []).extend(decls)
        if not meta:
            return
        text = _insert(self.src, chunks)
        _, err = self.d.verify("witness", text, "QuodCkW")
        accepted: dict[tuple[int, int], list[Any]] = {}
        for name, (i, xi, x, a, val) in meta.items():
            if _line_of(text, f"method {name}()") not in err:
                accepted.setdefault((i, xi), []).append(val)
        for (i, xi), vals in sorted(accepted.items(), key=lambda kv: kv[0]):
            if results[i].status or len({V.canon(v) for v in vals}) < 2:
                continue
            x, a = answers[i][xi]
            first = a if any(V.canon(v) == V.canon(a) for v in vals) else vals[0]
            second = next(v for v in vals if V.canon(v) != V.canon(first))
            m = eligible[i][0]
            results[i].status = "underspecified"
            results[i].witness = {
                "input": {n: v for (n, _), v in zip(m.params, x)},
                "result_a": first, "result_b": second, "method_returns": a,
                "outputs": [n for n, _ in m.outs]}

    def _execute(self, i: int, m: Method, pt: list, ot: list, xs: list[tuple],
                 res: Result) -> list[tuple[tuple, Any]]:
        s = self._static(m)
        pr = V.Printers(f"QuodCkP{i}_", s)
        body = []
        def show(t: Any, dt: str, var: str) -> str:
            if V.is_array(t):  # print an array as the sequence of its elements
                return f"{pr.name(('seq', t[1]), 'seq<' + V.elem_dafny_type(dt) + '>')}({var}[..]);"
            return f"{pr.name(t, dt)}({var});"

        for k, x in enumerate(xs):
            stmts, args = V.bind(list(x), pt, [t for _, t in m.params], f"q{k}_")
            outs = [f"r{k}_{j}" for j in range(len(ot))]
            body.extend(stmts)
            body.append(f"var {', '.join(outs)} := {m.name}({', '.join(args)});")
            body.append(f'print "QCOUT {k} ";')
            if len(ot) == 1:
                body.append(show(ot[0], m.outs[0][1], outs[0]))
            else:
                body.append('print "(";')
                for j, ((_, dt), t) in enumerate(zip(m.outs, ot)):
                    if j:
                        body.append('print ", ";')
                    body.append(show(t, dt, outs[j]))
                body.append('print ")";')
            body.append('print "\\n";')
        main = f"{m.indent}{s}method QuodCkM{i}() {{ " + " ".join(body) + " }"
        text = _insert(self.src, {m.insert_at: [*pr.code, main]})
        # A bodiless method anywhere in the file would stop the whole program from compiling:
        # mark them {:extern} for this run only (they are never called).
        for b in sorted((x for x in find_methods(text) if not x.has_body and not x.ghost),
                        key=lambda x: x.name_pos, reverse=True):
            text = text[:b.name_pos] + "{:extern} " + text[b.name_pos:]
        qual = (m.qualifier + "." if m.qualifier else "") + f"QuodCkM{i}"
        out = self.d.run(f"run{i}", text, qual)
        got = {}
        for line in out.splitlines():
            mm = re.match(r"QCOUT (\d+) (.*)$", line)
            if mm:
                try:
                    got[int(mm.group(1))] = V.read_value(mm.group(2))
                except (ValueError, IndexError):
                    pass
        if not got:
            res.notes.append("could not run the method to obtain reference answers: "
                             + _first_error(out))
        return [(xs[k], got[k]) for k in sorted(got)]


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
        if "Error" in line or "error" in line:
            return line.strip()[:200]
    return out.strip().splitlines()[-1][:200] if out.strip() else "no output"
