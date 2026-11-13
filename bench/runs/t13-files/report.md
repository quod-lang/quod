# T13: can an agent write a program with files? (0.7 candidate, step 3)

Question: with the reference alone, does Haiku write verified programs that read and write files, and does it state what becomes of the files?

Setup: `claude-haiku-5-5` through MCP, the compiler of commit 1797415 frozen in `artifacts/t13` (a build that is not AOT), two tasks (`copy_file`; `append_line`: append a line to a file, creating it, with a newline added first when the file does not end with one), hidden tests in Python on a temporary directory, C# compiled on net472.

## Results

- `copy_file`, 3 trials: 3 of 3 verified, 3 of 3 pass the hidden tests (5 checks), 3 of 3 generate C# that compiles.
- `append_line`, first wording (`runs/t13-files`): 2 runs went through, both verified and determined, and both failed the same hidden check (4 of 5). **The wording of the task was wrong**, not the agents: it said that a file without a final newline gets the line "right after its last character", and my check expected a newline to be added first. The agents followed the sentence. I corrected the wording.
- `append_line`, corrected wording (`runs/t13b-append`, 3 trials): 2 runs went through, both verified, both pass 5 of 5. C# compiles for one; for the other, Quod does not generate C#: it has a `private fn` that takes a `map<string, string>` and is used by the contract only, and C# cannot hold string values in a map yet (a known limit of 0.5). A private function that only contracts call is still generated: that is what blocked the C#.
- Every submitted contract states `files.contents(result)`. No contract was refused as incomplete, and none was underspecified.

## What was lost

Of 12 runs launched, **5 were lost** because the Quod MCP server did not connect (`CONNECTION_CLOSED`): the agent had no tool and wrote nothing. They were started again, with the same command (3, then 1, then 1 that failed again); they are not counted above. The build used for the runs is `quod.exe` that is not AOT, whose start is slower; that is the likely cause, not established. An AOT build should be used for the next trial.

Cost: 0.147 USD in all, for the 12 runs (0.006 to 0.020 each).

## What this does not say

Easy tasks, a ceiling again. The reference says what the model is, so this measures that agents read and follow it. Haiku only, 2 or 3 runs per variant. The first wording of `append_line` was wrong, and is reported as it was.
