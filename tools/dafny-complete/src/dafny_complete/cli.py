"""dafny-complete: does your Dafny contract pin down a single result?

    dafny-complete file.dfy [--method NAME ...] [--json] [--no-witness] [--keep]

Exit code: 0 = no underspecified method found, 1 = at least one underspecified, 2 = tool error.
"""
from __future__ import annotations

import argparse
import json
import shutil
import sys
from pathlib import Path

from dafny_complete import __version__
from dafny_complete.check import Checker, Result
from dafny_complete.values import DVal

TAG = {"determined": "[OK]   ", "underspecified": "[UNDER]", "inconclusive": "[?]    ",
       "skipped": "[skip] ", "error": "[ERR]  "}


def _fmt(v) -> str:
    return json.dumps(v, ensure_ascii=False) if isinstance(v, str) else repr(v)


def render(path: Path, results: list[Result]) -> str:
    lines = [f"dafny-complete {__version__}: spec completeness of {path.name}", ""]
    width = max((len(r.method) for r in results), default=0)
    for r in results:
        head = f"  {TAG[r.status]} {r.method:<{width}}  line {r.line:<5}"
        if r.status == "determined":
            lines.append(f"{head} the contract determines a unique result")
        elif r.status == "underspecified":
            w = r.witness
            args = ", ".join(f"{k}={_fmt(v)}" for k, v in w["input"].items())
            outs = ", ".join(w["outputs"])
            lines.append(f"{head} the contract accepts two different results")
            lines.append(f"  {'':8} {'':{width}}  input  : {args}")
            returned = w.get("method_returns", w["result_a"])
            is_answer = returned is not None and returned == w["result_a"]
            label_a = "(what the method returns)" if is_answer else "(satisfies every ensures)"
            lines.append(f"  {'':8} {'':{width}}  {outs} = {_fmt(w['result_a'])}   {label_a}")
            lines.append(f"  {'':8} {'':{width}}  {outs} = {_fmt(w['result_b'])}   (also satisfies every ensures)")
            if returned is not None and not is_answer:
                lines.append(f"  {'':8} {'':{width}}  (the method returns {_fmt(returned)})")
        else:
            lines.append(f"{head} {r.reason}")
        for n in r.notes:
            lines.append(f"  {'':8} {'':{width}}  note: {n}")
    counts = {s: sum(r.status == s for r in results) for s in TAG}
    lines += ["", "  " + ", ".join(f"{n} {s}" for s, n in counts.items() if n)]
    if counts["underspecified"]:
        lines.append("  An underspecified method can be verified and still be wrong: add ensures "
                     "clauses until only the intended result is allowed.")
    if counts["inconclusive"]:
        lines.append("  Inconclusive: no uniqueness proof and no witness. The contract may well be "
                     "complete; proving it may need a lemma.")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(prog="dafny-complete", description=__doc__.split("\n")[0])
    p.add_argument("file", type=Path)
    p.add_argument("--method", action="append", help="check only this method (repeatable)")
    p.add_argument("--json", action="store_true", help="machine-readable output")
    p.add_argument("--no-witness", action="store_true", help="skip the witness search")
    p.add_argument("--time-limit", type=int, default=30, help="seconds per proof (default 30)")
    p.add_argument("--dafny", default="dafny", help="dafny executable (default: dafny on PATH)")
    p.add_argument("--keep", action="store_true", help="keep the generated .dfy files")
    p.add_argument("--version", action="version", version=f"dafny-complete {__version__}")
    a = p.parse_args(argv)

    if not a.file.is_file():
        print(f"error: {a.file} not found", file=sys.stderr)
        return 2
    if shutil.which(a.dafny) is None:
        print(f"error: '{a.dafny}' not found; install Dafny 4.x or pass --dafny", file=sys.stderr)
        return 2
    results = Checker(a.file.resolve(), a.dafny, a.time_limit, a.keep, a.method).run(
        witness=not a.no_witness)
    if a.json:
        def encode(o):  # datatype values: {"ctor": ..., "args": [...]}
            if isinstance(o, DVal):
                return {"ctor": o.ctor, "args": list(o.args)}
            raise TypeError(type(o).__name__)
        print(json.dumps([r.__dict__ for r in results], indent=2, ensure_ascii=False, default=encode))
    else:
        try:
            sys.stdout.reconfigure(encoding="utf-8")
        except (AttributeError, ValueError):
            pass
        print(render(a.file, results))
    return 1 if any(r.status == "underspecified" for r in results) else 0


if __name__ == "__main__":
    sys.exit(main())
