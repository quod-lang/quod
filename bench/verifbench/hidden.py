"""Run the hidden test cases of one task against one candidate solution.

Meant to be run in a fresh subprocess (module caches, infinite loops):
    python -m verifbench.hidden --task rotate --arm python --dir path/to/workdir
    python -m verifbench.hidden --task rotate --arm dafny  --dir path/to/translated-py-dir

Prints a single JSON object on stdout.
"""
from __future__ import annotations

import argparse
import copy
import importlib
import importlib.util
import json
import sys
import traceback
from pathlib import Path
from typing import Any, Callable

from verifbench.tasks import TASKS, hidden_cases, validate


def _key(name: str) -> str:
    return name.replace("_", "").lower()


def load_python(workdir: Path, func: str) -> Callable[..., Any]:
    spec = importlib.util.spec_from_file_location("solution", workdir / "solution.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return getattr(mod, func)


def load_dafny(pydir: Path, func: str) -> Callable[..., Any]:
    """Load a method from `dafny translate py` output (module `Solution`, class `default__`).

    Dafny may mangle identifiers containing underscores, so the method is matched on a
    normalized name. Inputs are converted to Dafny runtime values, outputs back to Python.
    """
    sys.path.insert(0, str(pydir))
    dafny_rt = importlib.import_module("_dafny")
    mod = importlib.import_module("Solution")
    cls = getattr(mod, "default__")
    matches = [getattr(cls, n) for n in dir(cls) if _key(n) == _key(func)]
    if not matches:
        raise LookupError(f"no method matching {func!r} in Solution.default__: {dir(cls)}")
    method = matches[0]

    def to_dafny(v: Any) -> Any:
        if isinstance(v, str):
            cp = getattr(dafny_rt, "CodePoint", None)
            chars = [cp(c) for c in v] if cp else list(v)
            try:
                return dafny_rt.Seq(chars, isStr=True)
            except TypeError:
                return dafny_rt.Seq(chars)
        if isinstance(v, list):
            return dafny_rt.Seq([to_dafny(x) for x in v])
        if isinstance(v, tuple):
            return tuple(to_dafny(x) for x in v)
        return v

    def from_dafny(v: Any) -> Any:
        if isinstance(v, (bool, int, str)) or v is None:
            return v
        if isinstance(v, tuple):
            return tuple(from_dafny(x) for x in v)
        if getattr(v, "isStr", False) and hasattr(v, "VerbatimString"):
            return v.VerbatimString(False)
        try:
            items = [from_dafny(x) for x in v]
        except TypeError:
            return v
        # A seq<char> built without the isStr flag: all elements are CodePoints.
        cp = getattr(dafny_rt, "CodePoint", None)
        if items and cp and all(isinstance(x, cp) for x in v):
            return "".join(items)
        return items

    def call(*args: Any) -> Any:
        return from_dafny(method(*(to_dafny(a) for a in args)))

    return call


def run(task_id: str, arm: str, path: Path, seed: int, n: int) -> dict[str, Any]:
    task = TASKS[task_id]
    try:
        fn = load_python(path, task.func) if arm == "python" else load_dafny(path, task.func)
    except Exception as e:  # noqa: BLE001 - any load failure is a result, not a crash
        return {"loaded": False, "error": f"{type(e).__name__}: {e}"}

    cases = hidden_cases(task, seed, n)
    failures = []
    for args in cases:
        try:
            out = fn(*copy.deepcopy(args))
            err = validate(task, args, out)
        except Exception:  # noqa: BLE001
            err = "exception: " + traceback.format_exc(limit=2).strip().splitlines()[-1]
        if err:
            failures.append({"args": repr(args), "error": err})
    return {
        "loaded": True,
        "total": len(cases),
        "passed": len(cases) - len(failures),
        "failures": failures[:5],
    }


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--task", required=True, choices=sorted(TASKS))
    p.add_argument("--arm", required=True, choices=["python", "dafny"])
    p.add_argument("--dir", required=True, type=Path)
    p.add_argument("--seed", type=int, default=20260929)
    p.add_argument("--n", type=int, default=500)
    a = p.parse_args()
    print(json.dumps(run(a.task, a.arm, a.dir.resolve(), a.seed, a.n)))


if __name__ == "__main__":
    main()
