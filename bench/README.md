# VerifBench, Phase 0

*English · [Français](README.fr.md)*

**Question:** when an agent writes code, does forcing it to *prove* the code (contracts + an SMT
verifier) reduce the bugs that slip through, and at what cost?

Before designing a verification-first, agent-first language, we test the hypothesis with an
existing tool: **Dafny** (Z3-based verification, compiles to Python), against plain **Python**.

## Protocol

- **Two suites of 8 short algorithmic tasks**, rich in edge cases
  ([tasks.py](verifbench/tasks.py), [tasks_hard.py](verifbench/tasks_hard.py)):
  - *base*: `binary_search`, `merge_intervals`, `rle_encode`, `parse_int`, `bounded_queue`,
    `max_subarray`, `rotate`, `balanced`;
  - *hard*, chosen because LLMs classically stumble on them: `days_between` (Gregorian leap
    rules), `utf8_valid` (overlongs, surrogates), `glob_match` (escapes), `lru_cache`,
    `topo_sort` (lexicographically smallest), `justify`, `add_big` (borrows, `-0`),
    `normalize_path`.
- **Same natural-language specification** for both arms; only the target language changes.
- **`python` arm**: the agent writes `solution.py` and may run its own tests.
- **`dafny` arm**: the agent writes `solution.dfy` with `requires` / `ensures` / invariants and
  must get `dafny verify` to pass. Detected cheats: `assume`, `{:axiom}`, `{:verify false}`,
  `{:extern}`.
- **Identical hidden tests**: about 500 cases per task (edge cases + seeded random cases),
  compared with an oracle. The Dafny solution is compiled to Python and goes through the same
  harness.
- The agent works in a temporary folder outside the repository, with no access to the tests.
- Agent: Claude Code (`claude -p`); models Opus and Haiku. The harness accepts any CLI agent that
  reads its prompt on stdin (`--agent-cmd`).

## Metrics

| Metric | Meaning |
|---|---|
| **Accepted** | what the agent would ship: the file exists (and, for Dafny, verifies with no cheat) |
| **Escaped bug** | accepted but fails at least one hidden test: *the key metric* |
| Turns, cost, time | the price paid for verification (cost = API-equivalent estimate) |

## Results

One trial per (task, arm, model): read them as signals, not statistics.

**Base suite** (`runs/pass1`, default model): 16/16 runs pass every hidden test, in both arms.
Ceiling effect: the tasks were too easy to tell the arms apart. Dafny cost about 1.6× and 2.8×
the time.

**Hard suite** (`runs/hard1`):

| Model / arm | Accepted | All hidden tests pass | **Escaped bug** | Turns | Cost | Time |
|---|---|---|---|---|---|---|
| Opus / Python | 8/8 | 8/8 | **0** | 3.5 | $0.14 | 17 s |
| Opus / Dafny | 8/8 | 8/8 | **0** | 3.9 | $0.22 | 46 s |
| Haiku / Python | 8/8 | 7/8 | **1** | 11.1 | $0.15 | 106 s |
| Haiku / Dafny | 8/8 | 7/8 | **1** | 35.6 | $0.45 | 255 s |

- Haiku / Python: `normalize_path("a/..")` returned `".."` instead of `"."`.
- Haiku / Dafny: `lru_cache` was **verified and wrong**. Its only postcondition was
  `|out| == CountGets(ops, |ops|)`: the length of the output, nothing about its content.

That last case led to the completeness check below, and to Quod's pillar 5.

## Spec completeness (pillar 5)

`python -m verifbench.completeness runs/pass1 runs/hard1` generates, for each solution, a lemma
`ensures(a) ∧ ensures(b) ⇒ a == b` and asks Dafny to prove it unaided.
`python -m verifbench.witness` then searches witnesses: on small concrete inputs, it takes the
correct answer `a` and neighbouring answers `b`, and has Dafny **prove** `Post(x, a)` and
`Post(x, b)`. A witness found is therefore certain.

| Verdict | Count | Cases |
|---|---|---|
| Uniqueness proved | 15 | Opus: 7/8 on the hard suite; base: 5/8 |
| **Underspecified, witness found** | 5 | all Haiku: `lru_cache` (real bug), `add_big`, `justify`, `normalize_path`, `topo_sort` |
| Legitimately free (would use `loose`) | 1 | `binary_search` (duplicates) |
| Inconclusive (complete, but uniqueness needs induction) | 3 | `merge_intervals`, `rle_encode`, `add_big` Opus |

| Underspecified | Witness: one input, two accepted results |
|---|---|
| `binary_search` | `([1,1,1], 1)`: `1` and `2` |
| `add_big` Haiku | `"0" + "0"`: `"0"` and `"1"` |
| `justify` Haiku | `(["a"], 1)`: `["a"]` and `[]` |
| `lru_cache` Haiku | a `get` on an empty cache: `[-1]` and `[0]` |
| `normalize_path` Haiku | `""`: `"."` and `".x"` |
| `topo_sort` Haiku | one node, no edge: `[0]` and `[]` |

Clean separation: the 6 truly underspecified contracts all have a witness, the 3 inconclusive
ones have none. Four of Haiku's five near-empty contracts sat on *correct* code: the proofs
were green but guaranteed almost nothing. These scripts became the standalone tool
[dafny-complete](../tools/dafny-complete/), which works on any `.dfy` file and finds the same
verdicts without an oracle (it runs the method itself).

## Usage

```bash
python -m verifbench.selfcheck                        # do the hidden tests discriminate?
python -m verifbench.run --suite hard --models opus,haiku --trials 3
python -m verifbench.run --tasks rotate --arms dafny --agent-cmd "<any agent reading stdin>"
python -m verifbench.report runs/<stamp>/results.jsonl
python -m verifbench.rescore runs/<stamp>/results.jsonl --where task=X,model=Y,arm=dafny
```

`rescore` re-evaluates existing runs after a fix *to the harness*; it never gives an agent a
second attempt.

Requirements: Python ≥ 3.10; for the Dafny arm, Dafny 4.x (`dotnet tool install --global dafny`)
with Z3; a CLI agent reading its prompt on stdin (default `claude -p`).

## Self-check

Each task has a correct solution (must pass 100%) and a buggy "typical agent" solution
(off-by-one, all-negative case, over-permissive `int()`, forgotten modulo, century leap years,
`-0`...) that must be caught: **32/32**. The Dafny arm is validated end to end (verify, translate
to Python, hidden tests) with proved reference solutions in [reference/dafny/](reference/dafny/).

Windows note: the `dafny` .NET tool does not bundle Z3; put `z3-4.12.1.exe` in
`<folder of Dafny.dll>/z3/bin/`.
