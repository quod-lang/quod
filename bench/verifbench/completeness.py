"""Spec-completeness check (Quod pillar 5) applied to Dafny solutions.

For each verified Dafny solution, extract the target method's requires/ensures and generate:

    predicate Post__(params, outs) requires R { E1 && E2 && ... }
    lemma Uniq__(params, outs_a, outs_b)
      requires R && Post__(params, outs_a) && Post__(params, outs_b)
      ensures outs_a == outs_b
    {}

Dafny then tries to prove the lemma with no help. The contract is copied verbatim (outputs are
predicate parameters with their original names), so no expression rewriting is needed.

    python -m verifbench.completeness runs/pass1 runs/hard1
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
import time
from pathlib import Path

from verifbench.tasks import TASKS

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "completeness"


def _match_paren(s: str, i: int) -> int:
    """Index of the ')' matching the '(' at s[i]."""
    depth = 0
    for j in range(i, len(s)):
        if s[j] == "(":
            depth += 1
        elif s[j] == ")":
            depth -= 1
            if depth == 0:
                return j
    raise ValueError("unbalanced parentheses")


def _split_params(text: str) -> list[tuple[str, str]]:
    """'a: int, b: seq<(int, int)>' -> [('a', 'int'), ('b', 'seq<(int, int)>')]"""
    parts, depth, cur = [], 0, ""
    for c in text:
        if c in "(<[":
            depth += 1
        elif c in ")>]":
            depth -= 1
        if c == "," and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += c
    if cur.strip():
        parts.append(cur)
    out = []
    for p in parts:
        name, typ = p.split(":", 1)
        out.append((name.strip(), typ.strip()))
    return out


def extract_contract(src: str, func: str) -> dict:
    m = re.search(rf"\bmethod\s+{re.escape(func)}\s*\(", src)
    if not m:
        raise ValueError(f"method {func} not found")
    p_open = m.end() - 1
    p_close = _match_paren(src, p_open)
    params = _split_params(src[p_open + 1:p_close])
    r = re.compile(r"\s*returns\s*\(").match(src, p_close + 1)
    if not r:
        raise ValueError("no returns clause")
    r_open = r.end() - 1
    r_close = _match_paren(src, r_open)
    outs = _split_params(src[r_open + 1:r_close])

    # Spec runs until the body: the first '{' that begins a line, outside parentheses.
    depth, i, body = 0, r_close + 1, None
    while i < len(src):
        c = src[i]
        if c in "([":
            depth += 1
        elif c in ")]":
            depth -= 1
        elif c == "{" and depth == 0 and src[src.rfind("\n", 0, i) + 1:i].strip() == "":
            body = i
            break
        i += 1
    if body is None:
        raise ValueError("method body not found")
    spec = re.sub(r"//[^\n]*", "", src[r_close + 1:body])

    # Split into clauses at depth-0 keywords.
    clauses: list[tuple[str, str]] = []
    depth, last_kw, last_pos = 0, None, 0
    for mm in re.finditer(r"[()\[\]]|\b(requires|ensures|modifies|decreases|reads)\b", spec):
        tok = mm.group(0)
        if tok in "([":
            depth += 1
        elif tok in ")]":
            depth -= 1
        elif depth == 0:
            if last_kw:
                clauses.append((last_kw, spec[last_pos:mm.start()].strip()))
            last_kw, last_pos = tok, mm.end()
    if last_kw:
        clauses.append((last_kw, spec[last_pos:].strip()))
    return {
        "params": params,
        "outs": outs,
        "requires": [c for k, c in clauses if k == "requires"],
        "ensures": [c for k, c in clauses if k == "ensures"],
    }


def build_check(src: str, c: dict) -> str:
    ps = ", ".join(f"{n}: {t}" for n, t in c["params"])
    os_ = ", ".join(f"{n}: {t}" for n, t in c["outs"])
    pnames = ", ".join(n for n, _ in c["params"])
    req = " && ".join(f"({r})" for r in c["requires"]) or "true"
    ens = " && ".join(f"({e})" for e in c["ensures"]) or "true"
    a = [(f"{n}__a", t) for n, t in c["outs"]]
    b = [(f"{n}__b", t) for n, t in c["outs"]]
    sig_ab = ", ".join(f"{n}: {t}" for n, t in a + b)
    call = lambda outs: ", ".join([n for n, _ in c["params"]] + [n for n, _ in outs])  # noqa: E731
    eq = " && ".join(f"{x} == {y}" for (x, _), (y, _) in zip(a, b))
    gen = f"""
  // ---- generated: spec-completeness check (Quod pillar 5) ----
  ghost predicate Post__({ps}{", " if ps else ""}{os_})
    requires {req}
  {{
    {ens}
  }}

  lemma Uniq__({ps}{", " if ps else ""}{sig_ab})
    requires {req}
    requires Post__({call(a)}) && Post__({call(b)})
    ensures {eq}
  {{
  }}
"""
    end = src.rstrip().rfind("}")  # closing brace of `module Solution`
    return src[:end] + gen + src[end:]


def check(dfy: Path, timeout_s: int) -> dict:
    t0 = time.monotonic()
    try:
        p = subprocess.run(
            ["dafny", "verify", dfy.name, "--allow-warnings", "--filter-symbol", "Uniq__",
             "--verification-time-limit", str(timeout_s)],
            cwd=dfy.parent, capture_output=True, text=True, timeout=timeout_s * 4,
            encoding="utf-8", errors="replace")
        out = p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return {"status": "timeout", "secs": timeout_s * 4, "tail": ""}
    secs = round(time.monotonic() - t0, 1)
    if p.returncode == 0:
        status = "determined"
    elif "timed out" in out:
        status = "timeout"
    elif re.search(r"Error: (a postcondition could not be proved|could not prove)", out) or \
            "postcondition" in out:
        status = "not_proved"
    else:
        status = "gen_error"  # generated code does not resolve/typecheck
    return {"status": status, "secs": secs, "tail": out[-700:]}


def main() -> None:
    runs = [Path(a) for a in sys.argv[1:]]
    OUT.mkdir(exist_ok=True)
    rows = []
    for run in runs:
        for line in (run / "results.jsonl").read_text(encoding="utf-8").splitlines():
            r = json.loads(line)
            if r["arm"] != "dafny" or not r["accepted"]:
                continue
            model = r.get("model", "default")
            src = (run / "work" / Path(r["workdir"]).name / "solution.dfy").read_text(encoding="utf-8")
            dst = OUT / f"{run.name}__{r['task']}__{model}.dfy"
            row = {"run": run.name, "task": r["task"], "model": model,
                   "all_pass": r["all_pass"], "file": dst.name}
            try:
                c = extract_contract(src, TASKS[r["task"]].func)
                dst.write_text(build_check(src, c), encoding="utf-8")
                row.update(n_ensures=len(c["ensures"]), **check(dst, 60))
            except ValueError as e:
                row.update(status="extract_error", tail=str(e))
            rows.append(row)
            print(f"{row['run']:6} {row['task']:16} {model:8} {row['status']:13} "
                  f"{row.get('secs', '')}", flush=True)
    (OUT / "results.json").write_text(json.dumps(rows, indent=1), encoding="utf-8")


if __name__ == "__main__":
    main()
