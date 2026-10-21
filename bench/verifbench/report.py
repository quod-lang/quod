"""Aggregate results.jsonl into a Markdown report.

    python -m verifbench.report runs/<stamp>/results.jsonl
"""
from __future__ import annotations

import json
import statistics
import sys
from collections import defaultdict
from pathlib import Path


def _mean(xs: list) -> str:
    xs = [x for x in xs if isinstance(x, (int, float))]
    return f"{statistics.mean(xs):.2f}" if xs else "–"


def _pct(n: int, d: int) -> str:
    return f"{100 * n / d:.0f}% ({n}/{d})" if d else "–"


def main(path: Path) -> None:
    recs = [json.loads(l) for l in path.read_text(encoding="utf-8").splitlines() if l.strip()]
    # Group key "arm" or "model / arm" when several models are present.
    def key(r: dict) -> str:
        return f"{r.get('model', 'default')} / {r['arm']}" if multi else r["arm"]
    multi = len({r.get("model", "default") for r in recs}) > 1
    by_arm: dict[str, list] = defaultdict(list)
    for r in recs:
        by_arm[key(r)].append(r)

    print("## Summary by arm\n")
    print("| Arm | Runs | Accepted | All hidden tests | **Escaped bug** | Turns | Cost $ | Time s "
          "| Tokens in | Tokens out | Perm. denials |")
    print("|---|---|---|---|---|---|---|---|---|---|---|")
    for arm, rs in sorted(by_arm.items()):
        n = len(rs)
        acc = sum(r["accepted"] for r in rs)
        ok = sum(r["all_pass"] for r in rs)
        esc = sum(r["escaped_bug"] for r in rs)
        ag = [r.get("agent", {}) for r in rs]
        print(f"| {arm} | {n} | {_pct(acc, n)} | {_pct(ok, n)} | **{_pct(esc, acc)}** | "
              f"{_mean([x.get('turns') for x in ag])} | {_mean([x.get('cost_usd') for x in ag])} | "
              f"{_mean([x.get('secs') for x in ag])} | {_mean([x.get('in_tokens') for x in ag])} | "
              f"{_mean([x.get('out_tokens') for x in ag])} | {_mean([x.get('denials') for x in ag])} |")

    print("\n*Escaped bug* = accepted solution (file present and, for Dafny, verified with no "
          "cheat) that still fails at least one hidden test. Percentage of accepted ones.\n")

    print("## Per task\n")
    arms = sorted(by_arm)
    print("| Task | " + " | ".join(arms) + " |")
    print("|---|" + "---|" * len(arms))
    cells: dict[tuple[str, str], list[str]] = defaultdict(list)
    for r in recs:
        h = r["eval"].get("hidden") or {}
        if not r["eval"].get("submitted"):
            mark = "∅"
        elif r["eval"].get("cheats"):
            mark = "⛔"
        elif r["arm"] == "dafny" and not r["eval"].get("verified"):
            mark = "✗v"
        else:
            mark = "✓" if r["all_pass"] else f"✗{h.get('passed')}/{h.get('total')}"
        cells[(r["task"], key(r))].append(mark)
    for t in sorted({r["task"] for r in recs}):
        print(f"| {t} | " + " | ".join(" ".join(cells[(t, a)]) or "–" for a in arms) + " |")
    print("\n✓ all hidden tests pass · ✗p/t partial failure · ✗v not verified · "
          "⛔ cheat detected · ∅ no file")

    fails = [r for r in recs if r["escaped_bug"]]
    if fails:
        print("\n## Escaped bugs (first failure)\n")
        for r in fails:
            f = (r["eval"].get("hidden") or {}).get("failures") or [{}]
            print(f"- **{r['task']} / {key(r)} #{r['trial']}**: `{f[0].get('args')}` → {f[0].get('error')}")


if __name__ == "__main__":
    main(Path(sys.argv[1]))
