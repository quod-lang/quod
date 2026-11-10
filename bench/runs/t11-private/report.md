# T11: does a sentence of the reference make agents hide their helpers?

**Question.** In [T9](../t9-billing/report.md), no agent wrote `private fn`, and the C# they generated had 19 to 30 public methods with a `BigInteger`, helpers that no caller needs. One sentence was added to the reference, and nothing else changed: "Make a helper private unless another module or a caller needs it". Do agents follow it?

> **Since 0.4.0** the generated C# has no `BigInteger`: the counts of public methods with a `BigInteger` below describe 0.3.2.

The `i64` variant of the T9 task and its scoring, Haiku and Sonnet, 3 runs each, 6 runs, 2.26 USD, through MCP with `--require-contracts`, on a build of 0.3.2, 2026-11-06.

## Result

**All 6 made helpers private, against none of 6 in T9. Nothing broke: all 6 verified, all pass 436 orders in Python and 235 in C#, all give the client its 4 properties.**

| Run | T9: public methods, of which with a `BigInteger` | T11: the same |
|---|---|---|
| Haiku 0 | 41, 29 | 1, 0 |
| Haiku 1 | 38, 30 | 20, 15 |
| Haiku 2 | 36, 28 | 15, 9 |
| Sonnet 0 | 34, 25 | 8, 3 |
| Sonnet 1 | 29, 19 | 1, 0 |
| Sonnet 2 | 32, 22 | 25, 17 |

Cost does not move: 2.26 USD against 2.10.

## What this does not show

- **Not all of it goes away.** A helper called from another module must stay public: Quod has no visibility in between. Runs that keep logic in `catalog` and `discounts` keep 3 to 17; the two at 0 put every function in `solution.quod`, which the task allows, and gave up the split into modules to do it. A visibility for a whole program would be the real answer.
- **The code inside does not change.** The generated files still hold 120 to 259 `BigInteger`, against 189 to 259: they are out of the API, not out of the code.
- 6 runs of one task, one model pair. Run rows are not paired: the same number is not the same agent.

## Files

`results.jsonl`, `work/*/*.quod`. The transcripts stay on the machine that ran them, and mention neither the oracle nor a reference. One Haiku run left a file of its own, `scratch_run.quod`, in its directory.
