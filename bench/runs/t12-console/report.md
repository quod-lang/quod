# T12: can an agent write a program with a console? (0.6, steps 1 and 2)

Question: with the reference alone (which says that a contract must state what it does to `pending`), does Haiku write verified programs that write and read lines, and does it state `pending`?

Setup: `claude-haiku-5-5` through MCP, the compiler of commit 2af231b frozen in `artifacts/t12`, two tasks (`greet_two`: write two lines; `respond`: read one line and answer, or say there was nothing), 3 trials each, hidden tests in Python (output and what is left unread), C# compiled on net472.

Result: 6 of 6 verified by `quod check --require-contracts`, 6 of 6 pass the hidden tests (8 and 10 checks per run), 6 of 6 generate C# that compiles. All 6 contracts state `console.pending(result)`. No `check_rejected`, no underspecified contract on the way. Total cost 0.081 USD (0.008 to 0.020 per run, 9 to 20 turns).

One run (`greet_two` #1) was lost the first time because the Quod MCP server failed to connect (the agent had no tool); it was run again, same command, and is counted once. That is one restart.

What this does not say: the tasks are easy (a ceiling, as in T8 and T9); the reference tells the agent about `pending`, so this measures reading and following it, not finding it; a loop that writes lines, which proves in about twenty seconds, was not tried; Haiku only, 3 trials per task.
