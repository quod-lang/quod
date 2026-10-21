"""Orchestrate agent runs: for each task x arm x trial, prompt an agent in an isolated
workdir, then evaluate what it produced. Results are appended to <out>/results.jsonl.

    python -m verifbench.run --arms python,dafny --trials 3
    python -m verifbench.run --tasks rotate,parse_int --agent-cmd "claude -p --output-format json ..."
    python -m verifbench.run --evaluate-only <out>/work   # re-score existing workdirs

The agent command reads the prompt on stdin and runs with cwd = the workdir.
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any

from verifbench.tasks import TASKS, Task

ROOT = Path(__file__).resolve().parent.parent

DEFAULT_AGENT_CMD = (
    'claude -p --output-format json --permission-mode acceptEdits '
    '--allowedTools "Read,Write,Edit,Glob,Grep,Bash(python *),Bash(dafny *),'
    'PowerShell(python *),PowerShell(dafny *)"'
)

# Same for both arms: tells the agent how to run its tool without tripping the permission rules.
SHELL_HINT = "Run commands directly in the current directory (no `cd`, no chained commands)."

PROMPT_PY = """\
Implement the function below in Python 3, in the file `solution.py` in the current directory.

## Specification
{spec}

## Required signature
```python
{sig}
```

## Rules
- Standard library only. The function must be defined at module top level in `solution.py`.
- You may write and run your own tests (`python` is available). {hint}
- When you are confident the implementation is correct, stop.
  It will be evaluated against hidden tests.
"""

PROMPT_DFY = """\
Implement the method below in Dafny, in the file `solution.dfy` in the current directory,
inside `module Solution {{ ... }}`.

## Specification
{spec}

## Required signature (add the contracts yourself)
```dafny
{sig}
```

## Rules
- Add `requires` clauses expressing ONLY the input guarantees stated in the specification,
  and `ensures` clauses that fully capture the specified result.
  Add loop invariants and `decreases` clauses as needed.
- The file must verify: `dafny verify solution.dfy`. {hint}
- Forbidden: `assume`, `{{:axiom}}`, `{{:verify false}}`, `{{:extern}}`, and bodiless
  methods, functions or lemmas. Helper functions, predicates and lemmas are allowed.
- When it verifies and you are confident it is correct, stop.
  It will be compiled to Python and evaluated against hidden tests.
"""

CHEATS = [r"\bassume\b", r"\{:\s*axiom", r"\{:\s*verify\s+false", r"\{:\s*extern"]


def build_prompt(task: Task, arm: str) -> str:
    if arm == "python":
        return PROMPT_PY.format(spec=task.spec, sig=task.py_signature, hint=SHELL_HINT)
    return PROMPT_DFY.format(spec=task.spec, sig=task.dfy_signature, hint=SHELL_HINT)


def _sh(cmd: str | list[str], cwd: Path, timeout: int, stdin: str | None = None) -> dict[str, Any]:
    t0 = time.monotonic()
    try:
        p = subprocess.run(cmd, cwd=cwd, input=stdin, capture_output=True, text=True,
                           timeout=timeout, shell=isinstance(cmd, str), encoding="utf-8",
                           errors="replace")
        return {"code": p.returncode, "out": p.stdout, "err": p.stderr,
                "secs": round(time.monotonic() - t0, 1)}
    except subprocess.TimeoutExpired:
        return {"code": None, "out": "", "err": "timeout", "secs": timeout}


def run_agent(cmd: str, workdir: Path, prompt: str, timeout: int) -> dict[str, Any]:
    r = _sh(cmd, workdir, timeout, stdin=prompt)
    (workdir / "agent_stdout.txt").write_text(r["out"], encoding="utf-8")
    (workdir / "agent_stderr.txt").write_text(r["err"], encoding="utf-8")
    metrics: dict[str, Any] = {"exit": r["code"], "secs": r["secs"]}
    try:  # claude -p --output-format json
        j = json.loads(r["out"])
        usage = j.get("usage") or {}
        metrics.update(
            turns=j.get("num_turns"),
            cost_usd=j.get("total_cost_usd"),
            in_tokens=sum(usage.get(k) or 0 for k in (
                "input_tokens", "cache_creation_input_tokens", "cache_read_input_tokens")),
            out_tokens=usage.get("output_tokens"),
            agent_error=j.get("is_error"),
            denials=len(j.get("permission_denials") or []),
        )
    except (json.JSONDecodeError, AttributeError):
        pass
    return metrics


def hidden(task_id: str, arm: str, path: Path, timeout: int = 120) -> dict[str, Any]:
    cmd = [sys.executable, "-m", "verifbench.hidden", "--task", task_id, "--arm", arm,
           "--dir", str(path)]
    r = _sh(cmd, ROOT, timeout)
    if r["code"] is None:
        return {"loaded": True, "total": None, "passed": None, "error": "hidden tests timed out"}
    try:
        return json.loads(r["out"].strip().splitlines()[-1])
    except (json.JSONDecodeError, IndexError):
        return {"loaded": False, "error": (r["err"] or r["out"])[-800:]}


def evaluate(task: Task, arm: str, workdir: Path) -> dict[str, Any]:
    workdir = workdir.resolve()  # subprocesses run with cwd=workdir: relative paths would nest
    res: dict[str, Any] = {}
    if arm == "python":
        res["submitted"] = (workdir / "solution.py").exists()
        if res["submitted"]:
            res["hidden"] = hidden(task.id, arm, workdir)
        return res

    src = workdir / "solution.dfy"
    res["submitted"] = src.exists()
    if not res["submitted"]:
        return res
    text = src.read_text(encoding="utf-8", errors="replace")
    res["cheats"] = [c for c in CHEATS if re.search(c, text)]
    res["ensures_count"] = len(re.findall(r"\bensures\b", text))
    v = _sh(["dafny", "verify", "solution.dfy", "--allow-warnings"], workdir, 600)
    res["verified"] = v["code"] == 0
    res["verify_tail"] = (v["out"] + v["err"])[-600:]
    build = workdir / "_build"
    shutil.rmtree(build, ignore_errors=True)
    t = _sh(["dafny", "translate", "py", "solution.dfy", "--no-verify", "--include-runtime", "--allow-warnings",
             "--output", str(build / "solution")], workdir, 600)
    pydirs = [p.parent for p in build.rglob("Solution.py")] if build.exists() else []
    if t["code"] != 0 or not pydirs:
        res["hidden"] = {"loaded": False, "error": "translate failed: " + (t["out"] + t["err"])[-600:]}
        return res
    res["hidden"] = hidden(task.id, arm, pydirs[0])
    return res


def score(res: dict[str, Any]) -> dict[str, Any]:
    """Derive the headline flags from a raw evaluation."""
    h = res.get("hidden") or {}
    all_pass = bool(h.get("loaded")) and h.get("total") is not None and h["passed"] == h["total"]
    # "accepted" = what the agent would ship: a file exists and, for Dafny, it verifies cleanly.
    accepted = res.get("submitted", False)
    if "verified" in res:
        accepted = accepted and res["verified"] and not res["cheats"]
    return {"accepted": accepted, "all_pass": all_pass,
            "escaped_bug": accepted and not all_pass}


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--tasks", default="all", help="'all' or comma-separated task ids")
    p.add_argument("--suite", default=None, help="restrict 'all' to one suite (base, hard)")
    p.add_argument("--arms", default="python,dafny")
    p.add_argument("--models", default="default",
                   help="comma-separated; each non-default one is passed as --model to the agent")
    p.add_argument("--trials", type=int, default=1)
    p.add_argument("--agent-cmd", default=DEFAULT_AGENT_CMD)
    p.add_argument("--agent-timeout", type=int, default=1800)
    p.add_argument("--out", type=Path, default=None)
    p.add_argument("--evaluate-only", type=Path, default=None,
                   help="re-score existing workdirs named <task>__<arm>__<trial>")
    a = p.parse_args()

    if a.evaluate_only:
        out_dir = a.evaluate_only.parent
        jobs = []
        for wd in sorted(p for p in a.evaluate_only.iterdir() if p.is_dir()):
            parts = wd.name.split("__")  # task__arm[__model]__trial
            model = parts[2] if len(parts) == 4 else "default"
            jobs.append((TASKS[parts[0]], parts[1], model, int(parts[-1]), wd))
    else:
        out_dir = a.out or ROOT / "runs" / time.strftime("%Y%m%d-%H%M%S")
        if a.tasks == "all":
            task_ids = sorted(t for t in TASKS if a.suite in (None, TASKS[t].suite))
        else:
            task_ids = a.tasks.split(",")
        # Workdirs live outside the repo so the agent has no path to the hidden tests.
        work_root = Path(tempfile.mkdtemp(prefix="verifbench-"))
        jobs = [(TASKS[t], arm, m, i, work_root / f"{t}__{arm}__{m}__{i}")
                for i in range(a.trials) for m in a.models.split(",")
                for t in task_ids for arm in a.arms.split(",")]
    out_dir.mkdir(parents=True, exist_ok=True)
    results = out_dir / "results.jsonl"

    for task, arm, model, trial, wd in jobs:
        rec: dict[str, Any] = {"task": task.id, "suite": task.suite, "arm": arm, "model": model,
                               "trial": trial, "workdir": str(wd)}
        if not a.evaluate_only:
            wd.mkdir(parents=True)
            prompt = build_prompt(task, arm)
            (wd / "PROMPT.md").write_text(prompt, encoding="utf-8")
            print(f"[agent] {task.id} / {arm} / {model} / #{trial} ...", flush=True)
            cmd = a.agent_cmd if model == "default" else f"{a.agent_cmd} --model {model}"
            rec["agent"] = run_agent(cmd, wd, prompt, a.agent_timeout)
        rec["eval"] = evaluate(task, arm, wd)
        rec.update(score(rec["eval"]))
        if not a.evaluate_only:  # keep the agent's artifacts next to the results
            shutil.copytree(wd, out_dir / "work" / wd.name, dirs_exist_ok=True,
                            ignore=shutil.ignore_patterns("_build", "__pycache__"))
        with results.open("a", encoding="utf-8") as f:
            f.write(json.dumps(rec) + "\n")
        h = rec["eval"].get("hidden") or {}
        print(f"   accepted={rec['accepted']} all_pass={rec['all_pass']} "
              f"hidden={h.get('passed')}/{h.get('total')}", flush=True)

    print(f"\nresults: {results}\nreport:  python -m verifbench.report {results}")


if __name__ == "__main__":
    main()
