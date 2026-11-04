# Held-out tasks: what is fixed before the first run

The six base tasks of VerifBench shaped the compiler: writing them changed the verifier and its
messages. They cannot also measure it without bias. The suite `heldout`
([tasks_heldout.py](verifbench/tasks_heldout.py)) exists for that. This file records the protocol,
and its history shows that it is dated before any run.

## The question

The base tasks show no measured gain in how often a contract determines the result
([reading of the undecided contracts](runs/t6-haiku/undecided-review.md)), and two proved, determined and wrong
contracts. So: **on tasks that did not shape the compiler, does checking completeness while the agent writes
change how often an accepted contract is sound, that is lets through no result the task forbids, and at what cost?**

## The tasks

| Task | Why it is here | A contract by properties in Quod 0.1 | Prediction, before any run, of 3 trials per arm |
|---|---|---|---|
| `gcd` | Divisibility, negatives, zero | Expressible, with a bounded `forall`; divisibility is mostly beyond Z3 | At most 1 sound by properties in any arm; at least 2 sound in all, by a model (Euclid), in `quod` and `quod-mcp` |
| `split_folds` | Document capture; a canonical form | Yes | At least 2 sound in each arm; at most 1 decided by the tool, as for `rle_encode` |
| `arbitrate_field` | Document capture; a lexicographic tie-break | Yes | At least 2 sound in each arm; at least 2 decided in the Quod arms |
| `transpose` | Nested sequences | Yes | 3 sound in each arm; at least 2 decided |
| `next_permutation` | A minimum over rearrangements | **No:** it quantifies over permutations, so only a model can determine it | At most 1 sound by properties in any arm |
| `two_sum_sorted` | A freedom to declare with `loose` | Yes | At least 2 sound in each arm; at least 2 exact in the Quod arms, at most 1 in `dafny`, which cannot declare the freedom |

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
- **Limits:** 1800 s per run; the other limits are the agent's defaults, unchanged between arms. A run stopped by a usage limit is not recorded and is run again, at most twice, and every restart is reported.
- **Accepted:** the same script, for both languages: the final file verifies, its required function has at least one `ensures`, and it has no cheat.
- **A cheat:** `assume`, `{:axiom}`, `{:verify false}`, `{:extern}`, a body-less method, function or lemma. In Quod, also what `--require-contracts` refuses. A `requires` that reduces the task is not a cheat but fails the main measure below.

## What is measured

**Main measure: sound contracts among the 18 runs of each arm, by execution.** It is computed before any contract is read. For each task, a generator gives small valid inputs, the correct results by the oracle, and wrong results, by mutating them and by enumerating small outputs, each confirmed wrong by the oracle or the task's check. A contract is:

- **Sound** when its `requires` accept every valid input, and its `ensures` accept no wrong result. This is what protects from an escaped bug. A `requires` that reduces the function to a case fails here.
- **Exact** when it is sound and its `ensures` accept every result the task allows, including all of them where several are allowed. It is reported next to the main measure. Exactness is not asked for: the completeness check may push an agent to an over-specified contract rather than to a `loose`, and that is an effect to measure, not to punish twice.

Both are evaluated without the code of the solution, by the Quod evaluator for Quod. For Dafny, each pair is a lemma proved or not by Dafny, as `dafny-complete` does. Where a tool cannot tell (a value the evaluator cannot compute, a lemma it does not prove), the pair is *unknown*: never counted as accepted, always reported by arm, since it does not fall the same way in the two languages.

This is a finite test, and it cannot show that a contract is sound for all inputs, only that it is not, with a witness.

**The judge, second measure:** only for contracts with unknown pairs, and those that pass the main measure while proving little. `claude-opus-5-5`, with the prompt recorded below, a fresh conversation per contract, the statement of the task and the contract with its helpers, without the code, the run or the results. An inadequate verdict comes with an input and a result, then checked by the same machinery. Without one, it is "unsure": reported apart, and counted as sound in neither direction. An LLM judge is known to miss failures (Verus-SpecGym: 26% of those its evaluator caught), and this one belongs to the family of the agent. The language shows: Quod and Dafny syntax cannot be hidden.

**The author** reads 5 contracts per arm, and all the "unsure" ones; any disagreement is reported.

**Also reported, for each arm and task:** accepted; passing all the hidden tests; escaped bugs; decided by the tool; contract style; time; cost; turns. Every wrong solution of the self-check is reported with the share of hidden tests it passes, and with whether the generator's wrong results would catch it: the sensitivity of the measures.

**What would count.** Six tasks and three trials can only show large differences, and the trials of one task are not independent, so no significance test is run.

- **Main comparison, chosen before any run: `dafny-loop` against `dafny`.** Same language and model; the only difference is the verdict during writing, which is the question.
- **Secondary:** `quod` against `dafny-loop`, which separates language from check, and `quod` against `quod-mcp`.
- A gap of at least 4 of 18 sound contracts, spread over at least 3 tasks, is reported as a direction, for the main comparison. Anything smaller is reported as no difference. A secondary comparison is described, never concluded from, with three comparisons at one threshold.
- **Cost:** a gain counts for less if the median time or cost of a run more than doubles. Both are reported in any case.

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
- **A finite test.** Soundness by execution finds wrong results, it does not exclude them. The generator of wrong results is written by the assistant that wrote the suite.
- **Two evaluators.** Quod's contracts are run, Dafny's are proved case by case: unknown pairs may not fall alike.
- **Two authors of tasks.** The conversation that wrote `split_folds` and `arbitrate_field` has read the whole suite, though it wrote no solution.

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
- 2026-11-04, after the review of 0.1.5 and of the literature: the main measure is no longer a judge's verdict but soundness by execution, and exactness is apart from it (a judge misses failures, and "exactly" would have punished an over-specified contract that lets nothing wrong through). The main comparison is named; cheats and the acceptance rule are defined, the same for both languages; predictions have numbers; restarts are limited; the judge is fixed.
- A `requires` too strong now fails the main measure: the first wording looked only at results.
