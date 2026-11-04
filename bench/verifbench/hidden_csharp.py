"""The hidden tests of a task, through the C# that `quod build --target csharp` generates:

    python -m verifbench.hidden_csharp --task rotate --file quod/rotate/solution.quod

A small program calls the public method on every case and prints JSON; the results go through the
same `validate` as the other arms. Prints a single JSON object on stdout, as verifbench.hidden does.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

from verifbench.tasks import TASKS, hidden_cases, validate

QUOD_EXE = os.environ.get("QUOD_EXE", "quod")

PROJECT = """<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup><OutputType>Exe</OutputType><TargetFramework>net10.0</TargetFramework><LangVersion>7.3</LangVersion>
  <InvariantGlobalization>true</InvariantGlobalization></PropertyGroup>
</Project>
"""

RUNNER = """using System;
using System.Collections;
using System.Collections.Generic;
using System.Numerics;
using System.Runtime.CompilerServices;

static class Runner
{
    static string Json(object v)
    {
        if (v is bool) return (bool)v ? "true" : "false";
        if (v is ITuple) { var t = (ITuple)v; var ps = new string[t.Length]; for (int i = 0; i < t.Length; i++) ps[i] = Json(t[i]); return "[" + string.Join(",", ps) + "]"; }
        if (v is IEnumerable) { var ps = new List<string>(); foreach (var x in (IEnumerable)v) ps.Add(Json(x)); return "[" + string.Join(",", ps) + "]"; }
        return v.ToString();
    }

    static void Case(Func<object> f)
    {
        try { Console.WriteLine(Json(f())); } catch (Exception e) { Console.WriteLine("\\"!" + e.GetType().Name + "\\""); }
    }

    static void Main()
    {
%s
    }
}
"""


def params_of(signature: str) -> list[str]:
    """The Python types of a task's parameters, from its signature."""
    inside = signature[signature.index("(") + 1:signature.rindex(")")]
    parts, depth, current = [], 0, ""
    for c in inside:
        if c == "," and depth == 0:
            parts.append(current)
            current = ""
            continue
        depth += c == "["
        depth -= c == "]"
        current += c
    parts.append(current)
    return [p.split(":", 1)[1].strip() for p in parts if p.strip()]


def cs_type(t: str) -> str:
    if t == "int":
        return "BigInteger"
    if t == "bool":
        return "bool"
    m = re.fullmatch(r"list\[(.*)\]", t)
    if m:
        return "IReadOnlyList<" + cs_type(m.group(1)) + ">"
    m = re.fullmatch(r"tuple\[(.*)\]", t)
    if m:
        return "(" + ", ".join(cs_type(x) for x in params_of("(a: " + m.group(1).replace(", ", ", a: ") + ")")) + ")"
    raise ValueError(t)


def literal(t: str, v) -> str:
    if t == "int":
        return f"new BigInteger({v})"
    if t == "bool":
        return "true" if v else "false"
    m = re.fullmatch(r"list\[(.*)\]", t)
    if m:
        return "new " + cs_type(m.group(1)) + "[] { " + ", ".join(literal(m.group(1), x) for x in v) + " }"
    m = re.fullmatch(r"tuple\[(.*)\]", t)
    if m:
        ts = params_of("(a: " + m.group(1).replace(", ", ", a: ") + ")")
        return "(" + ", ".join(literal(x, y) for x, y in zip(ts, v)) + ")"
    raise ValueError(t)


def pascal(name: str) -> str:
    return "".join(p[:1].upper() + p[1:] for p in name.split("_") if p)


def run(task_id: str, file: Path, seed: int, n: int) -> dict:
    task = TASKS[task_id]
    work = Path(tempfile.mkdtemp(prefix="quod-hidden-cs-"))
    try:
        built = subprocess.run([QUOD_EXE, "build", str(file), "--target", "csharp", "--namespace", "Solved", "-o", str(work)],
                               capture_output=True, text=True, encoding="utf-8", errors="replace")
        if built.returncode != 0:
            return {"loaded": False, "error": "build failed: " + (built.stdout + built.stderr)[-600:]}
        generated = next(work.glob("*.g.cs"))
        cls = re.search(r"public static class (\w+)", generated.read_text(encoding="utf-8")).group(1)
        types = params_of(task.py_signature)
        cases = hidden_cases(task, seed, n)
        calls = "\n".join(
            "        Case(() => Solved." + cls + "." + pascal(task.func) + "("
            + ", ".join(literal(t, v) for t, v in zip(types, args)) + "));"
            for args in cases)
        (work / "T.csproj").write_text(PROJECT, encoding="utf-8")
        (work / "Runner.cs").write_text(RUNNER % calls, encoding="utf-8")
        b = subprocess.run(["dotnet", "build", "-c", "Release", "--nologo", "-v", "q", "-o", "out"], cwd=work,
                           capture_output=True, text=True, encoding="utf-8", errors="replace")
        if b.returncode != 0:
            return {"loaded": False, "error": "the generated C# does not compile: " + b.stdout[-800:]}
        exe = work / "out" / ("T.exe" if os.name == "nt" else "T")
        r = subprocess.run([str(exe)], capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=300)
        lines = r.stdout.splitlines()
        if len(lines) != len(cases):
            return {"loaded": False, "error": f"{len(lines)} results for {len(cases)} cases: {r.stderr[-400:]}"}
        failures = []
        for args, line in zip(cases, lines):
            out = json.loads(line)
            err = out if isinstance(out, str) and out.startswith("!") else validate(task, args, out)
            if err:
                failures.append({"args": repr(args), "error": err})
        return {"loaded": True, "total": len(cases), "passed": len(cases) - len(failures), "failures": failures[:5]}
    finally:
        shutil.rmtree(work, ignore_errors=True)


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--task", required=True, choices=sorted(TASKS))
    p.add_argument("--file", required=True, type=Path)
    p.add_argument("--seed", type=int, default=20260929)
    p.add_argument("--n", type=int, default=500)
    a = p.parse_args()
    print(json.dumps(run(a.task, a.file.resolve(), a.seed, a.n)))


if __name__ == "__main__":
    main()
