# Held-out tasks: what is fixed before the first run

The six base tasks of VerifBench shaped the compiler: writing them changed the verifier and its
messages. They cannot also measure it without bias. The suite `heldout`
([tasks_heldout.py](verifbench/tasks_heldout.py)) exists for that. This file records the protocol,
and its history shows that it is dated before any run.

## The question

The base tasks show no measured gain in how often a contract determines the result
([reading of the undecided contracts](runs/t6-haiku/undecided-review.md)), and two proved, determined and wrong
contracts. So: **on tasks that did not shape the compiler, does checking completeness while the agent writes
change how often an accepted contract says what the task asks, and at what cost?**

## The tasks

| Task | Why it is here | A contract by properties in Quod 0.1 | Prediction, before any run |
|---|---|---|---|
| `gcd` | Divisibility, negatives, zero | Expressible, with a bounded `forall`; divisibility is mostly beyond Z3 | Contracts by a model (Euclid), or proofs that time out |
| `split_folds` | Document capture; a canonical form | Yes | Written, but completeness not decided, as for `rle_encode` |
| `arbitrate_field` | Document capture; a lexicographic tie-break | Yes | Determined and decided when the proof passes; the tie-break is where contracts go wrong |
| `transpose` | Nested sequences | Yes | Determined and decided |
| `next_permutation` | A minimum over rearrangements | **No:** it quantifies over permutations, so only a model can determine it | Weak or wrong contracts by properties; few accepted and adequate |
| `two_sum_sorted` | A freedom to declare with `loose` | Yes | Determined with `loose` in Quod; underspecified by dafny-complete in Dafny, which cannot declare it |

These tasks can say what the language cannot express as well as what an agent cannot do, and the table says which is expected
where. Predictions are not goals: they are reported next to the results, right or wrong.

**Where they come from.** `gcd`, `transpose`, `next_permutation` and `two_sum_sorted` are classics, chosen by the assistant that works on
the compiler. `split_folds` and `arbitrate_field` come from a document capture chain, written by another conversation that had reviewed the
compiler but not worked on it. They say nothing about domains with amounts, dates or rounding, which Quod 0.1 does not have.

## What is fixed

- **Model:** `claude-haiku-5-5`, through Claude Code.
- **Arms:** `quod` (shell), `quod-mcp`, `dafny` (shell, `dafny verify`, then dafny-complete afterwards), and `dafny-loop` (the same, with dafny-complete
  available to the agent and required by its prompt). Their prompts are recorded here before the first run.
- **Trials:** three per task and arm: 72 runs.
- **Compiler:** frozen at the tag recorded below, for all the runs. Dafny 4.11.0, z3 4.12.1.
- **Quod options:** `--require-contracts`, in the check and the build, as the bench does. The reference served is the one of the tag, without any solution.
- **Limits:** 1800 s per run; the other limits are the agent's defaults, unchanged between arms. A run stopped by a usage limit is not recorded, and is run again.
- **Accepted:** the final file verifies, has a contract, has no cheat, and has no `loose` that accepts every result.

## What is measured

**Main measure: adequate contracts among the 18 runs of each arm.** An accepted contract is adequate when it accepts exactly the results the task allows.

- Judged by a stronger model (the most capable available at the time), with the statement of the task and the contract with its helper functions, without the code, the
  run or the hidden test results. Each contract gets a fresh conversation.
- A contract judged inadequate comes with an input and a result the contract wrongly accepts or rejects. Without one, the verdict is "unsure" and it is reported as such.
- **The language shows:** Quod and Dafny syntax cannot be hidden from the judge, so this is blind to the run and to the results, not to the language. The author reads a sample of 10 contracts per arm, after the
  judge, and any disagreement is reported.

**Also reported, for each arm and task:** accepted; passing all the hidden tests; escaped bugs; decided by the tool; determined after reading the undecided ones; contract style; time; cost. Every wrong
solution of the self-check is reported with the share of hidden tests it passes, which is the sensitivity of the escaped-bug measure.

**What would count.** Six tasks and three trials can only show large differences, and the trials of one task are not independent, so no significance test is run. Between `quod` and `dafny`, and between
`dafny-loop` and `dafny`, a gap of at least 4 of 18 adequate contracts, spread over at least 3 tasks, is reported as a direction. Anything smaller is reported as no difference. The comparison `dafny-loop`
against `quod` separates the effect of the check from that of the language.

## The rules

1. **Before the first run,** no Quod program for these tasks is written, checked or read by anyone working on the compiler, and they are not used to test it.
2. **The compiler is frozen** at one tagged version for all the runs of this suite.
3. **Every arm runs the same tasks** with the same prompt rules, three trials per task, with the same model.
4. **Everything is reported,** including tasks no arm solves, and a bug found in a task's specification or oracle. A correction to a task after the first run is recorded here, with its reason.
5. **Afterwards, the suite is spent:** once its solutions have been read, a compiler change made because of it needs new held-out tasks to be measured.

## Limits of this protocol

- **The assistant that works on the compiler wrote part of the suite, and read it all.** No exclusion file can undo that. Rule 1 is what is left: it is a promise, not a guarantee.
- **The tasks are small.** Results hold for pure functions of this size, not for code in general.
- **One model.** Another vendor is not part of this measure.
- **One judge,** whose errors the sample read by the author only partly catches.

## Frozen version and prompts

- **Compiler:** tag `v0.1.5`, commit `0fa2df7`, the Windows package of its release. It is the compiler of all the runs.
- **Prompts:** those of `bench/verifbench/run.py` at the commit of the first run. The prompt of `dafny-loop` is the one of `dafny` with two
  changes: `ensures` clauses that fully capture the specified result, "`dafny-complete solution.dfy` reports a contract that accepts two
  different results for the same input (`[UNDER]`, with a witness). Fix it, unless that freedom is what the specification allows"; and the
  file must verify "and `dafny-complete solution.dfy` must report no `[UNDER]` that the specification does not allow. An undecided verdict is
  acceptable." As in the Quod arms, an undecided verdict does not stop the agent. Unlike them, a freedom is justified only by the statement:
  Dafny has no `loose`, so nothing declares or checks it.

## Corrections

All before any run; the first version of this suite is in commit 64c4872.

- 2026-11-04, after the review of 0.1.4: the protocol above completed (model, arms, version, option, limits, measures, predictions).
- `merge_sorted` and `majority_element` replaced by `split_folds` and `arbitrate_field`, the suite being otherwise only classics.
- `arbitrate_field`: a tie between two engines of equal rank was not settled by its first wording; "between equal confidences and equal ranks, the first one".
- "Must run in O(n)" removed from `two_sum_sorted`: the hidden tests have at most 25 elements and measure nothing of the kind.
- `two_sum_sorted`: the generator now also targets twice a value that occurs once. The wrong solution that uses one index twice failed 10 of 510 cases, and now fails 87.
