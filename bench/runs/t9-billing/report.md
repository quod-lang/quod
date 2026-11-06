# T9: an agent on a billing engine

**Question.** Does Quod hold on a program of several hundred lines of business rules, written by an agent from a specification, and what does its C# give?

[billing.py](../../verifbench/billing.py): invented rules over three modules, about 25 rules, committed before any run. Volume discounts, customer discounts, coupons, a cap, shipping by weight, VAT by category with the discount taken category by category, reverse charge, validation with messages. Haiku and Sonnet (`claude-haiku-5-5`, `claude-sonnet-5-5`), through the MCP server with `--require-contracts`, on the released Quod 0.3.1, 2026-11-06. Two variants, 3 runs each: amounts in `i32`/`i64`, or in `int`. 12 runs, 4.03 USD. No usage limit.

**How it is scored:**

- A Python oracle written from the specification, on 436 orders: the generated Python. For the `i64` variant, 235 of them on the C# generated, compiled for .NET Framework 4.7.2 with C# 7.3, through the classes a C# caller uses.
- A client that must prove 4 properties of the specification from the contract of `price` alone.
- Before the runs, the hidden tests saw all of 24 wrong rules put into the reference solution, after boundary cases were added for 3 that they had missed.

## Result

**12 of 12 verified. 12 of 12 pass all 436 orders. 6 of 6 pass all 235 in C#. 12 of 12 give the client its 4 properties.**

| Model, variant | Lines | Lemmas | Time, s | Checks | Rejected | Failed proofs | "Fits in" among them | Cost, USD |
|---|---|---|---|---|---|---|---|---|
| Haiku, `i64` | 386, 478, 496 | 13, 5, 4 | 619, 304, 396 | 16 | 11 | 17 | 6 | 0.48 |
| Haiku, `int` | 289, 345, 309 | 2, 4, 2 | 216, 334, 192 | 13 | 9 | 5 | 0 | 0.40 |
| Sonnet, `i64` | 230, 265, 286 | 3, 8, 7 | 113, 231, 330 | 12 | 8 | 21 | 4 | 1.63 |
| Sonnet, `int` | 346, 224, 274 | 7, 4, 13 | 142, 147, 161 | 13 | 6 | 2 | 0 | 1.53 |

Lines are those of the three files, comments and blank lines included. Time is the agent's. The check of a finished program takes 1 to 14 s.

**What a passing test says here.** The final check of every run leaves no contract undecided, and each contract determines its result. So what is proved accepts one result only, the one the code returns, and on these 436 orders the oracle agrees with it. This is a test of the contract as well as of the code, on those orders, and not a proof that the contract matches the specification on all of them.

**`i64` has a cost here, which T8 could not see.** Failed proofs: 38 against 7 over 6 runs each, and medians of 396 s against 216 s for Haiku, 231 s against 147 s for Sonnet. The cost in money hardly moves. All of them got there, and they needed the bound of a sum, a lemma by induction, which the `int` variant does not. 3 runs per cell: read this as a direction.

## What this does not show

- **The rules were kept linear on purpose.** The discount is taken category by category, where a real invoice might share it in proportion. I chose that while designing the task, to avoid products of variables, which are the hard case for the solver. **The ceiling was not reached,** and this avoided what is most likely to reach it.
- **The same author wrote the compiler, the rules, the oracle and the tests.** The oracle was written apart from any Quod, but by the author of the reference solution, who had already read the rules as a program.
- **Three hundred lines is not a real application.** There are 25 rules, and no state over time.
- The C# driver covers orders of at most 6 lines, and the one of 1000 lines, not all 436.

## What the agents ran into

In runs, of 12, from their transcripts; a rejected check often repeats an error.

1. **A helper with a contract that only bounds its result.** `underspecified`, 82 times, and the style check `returns-argument`, 78 times, each in 6 runs. For example a bound on `coupon_discount`: it must become a function defined by its body, with the bound in a lemma. It is the rule of the language, and the most frequent error here.
2. **A proof given up on its time limit, 8 runs**, most often a precondition of a helper, or that a value fits in `i64`. All ended proved.
3. **`Category` used as a value, 2 runs.** `unknown variable 'Category'`: a case is not written through its type here, and the message does not say so.
4. **`expected an expression, found '{'`, 4 runs.**
5. **The time budget of the whole check used up, 1 run.** The message says what to do, and it did.

## Files

`results.jsonl`; `work/*/*.quod`, the solutions; `reference/`, the solution written by hand before the runs, kept away from the agents, with the C# it generates. The transcripts stay on the machine that ran them: they hold its configuration. No agent read the oracle or the reference: all their reads and commands were listed and checked. They had a shell they were not told of, used to look at their own directory, and mostly refused.

The scoring program crashed on a line of the transcripts after writing 5 results. All 12 agents had finished: the other 7 were scored from their files, without running them again, so their time is the one the agent reports.
