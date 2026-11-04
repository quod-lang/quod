# The contracts no tool could decide, read by hand

The review of 0.1.4 pointed out that "not decided" is a limit of the tool, not a property of the contract, yet
the T6 table counted such contracts as not determined. So each undecided contract of this run was read. The
reader is the assistant that works on the compiler, and knew the arms: this is not a blind review. Every
contract below is judged on one question only: can two different results satisfy it for the same input?

| Arm | Contract | Undecided by | Verdict |
|---|---|---|---|
| dafny | rle_encode #0, #1, #2 | dafny-complete | **Determined.** Counts >= 1, adjacent values distinct, and the expansion equals `xs`: the canonical encoding, unique by induction |
| dafny | merge_intervals #1, #2 | dafny-complete | **Determined.** Sorted, strictly separated, and the same cover over the **reals**: the connected components |
| dafny | merge_intervals #0 | dafny-complete | **Underspecified.** The same cover over the **integers**: for `[(1,2),(3,4)]` it accepts both that list and `[(1,4)]`, which the task forbids. [Proved by Dafny](undecided-witness.dfy). The code is right, and the contract does not say so |
| quod (shell) | rle_encode #2 | `quod check` | **Determined**, for the same reason as the Dafny ones |
| quod-mcp | rle_encode #0, #1 | `quod check` | **Determined**, likewise |
| quod-mcp | max_subarray #0, #2 | `quod check` | **Determined.** The result is a sum of a sublist and at least all of them: the maximum |

Only the witness is checked by a machine; the other verdicts are arguments on paper.

## Counts

Contracts of accepted solutions that determine the result, without binary_search (copied in the MCP arm):

| | quod (shell) | quod-mcp | dafny |
|---|---|---|---|
| Decided as determined by the tool | 14/15 | 9/15 | 9/15 |
| After this reading | 15/15 | 13/15 (2 rejected) | 14/15 |

With Haiku on these tasks, **the check does not show a gain in how often a contract determines the result**. These tasks
may leave little room: the model already writes such contracts without the check. What the tool changes is that the
verdict is known, and known while the agent writes. The only contract found wrong is one no tool flagged.
