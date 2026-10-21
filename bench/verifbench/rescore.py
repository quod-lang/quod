"""Re-evaluate selected records of a results.jsonl in place (keeps the agent metrics).
Use after fixing the harness itself, never to give an agent a second attempt.

    python -m verifbench.rescore runs/hard1/results.jsonl --where task=topo_sort,model=opus,arm=dafny
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from verifbench.run import evaluate, score
from verifbench.tasks import TASKS


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("results", type=Path)
    p.add_argument("--where", required=True, help="comma-separated key=value filters")
    a = p.parse_args()
    cond = dict(kv.split("=", 1) for kv in a.where.split(","))

    recs = [json.loads(l) for l in a.results.read_text(encoding="utf-8").splitlines() if l.strip()]
    for r in recs:
        if all(str(r.get(k)) == v for k, v in cond.items()):
            wd = a.results.parent / "work" / Path(r["workdir"]).name
            r["eval"] = evaluate(TASKS[r["task"]], r["arm"], wd)
            r.update(score(r["eval"]))
            r["rescored"] = True
            h = r["eval"].get("hidden") or {}
            print(f"{r['task']} / {r['model']} / {r['arm']}: accepted={r['accepted']} "
                  f"hidden={h.get('passed')}/{h.get('total')}")
    a.results.write_text("".join(json.dumps(r) + "\n" for r in recs), encoding="utf-8")


if __name__ == "__main__":
    main()
