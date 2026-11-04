# Held-out tasks: what is fixed before the first run

The six base tasks of VerifBench shaped the compiler: writing them changed the verifier and its
messages. They cannot also measure it without bias. The suite `heldout`
([tasks_heldout.py](verifbench/tasks_heldout.py)) exists for that. This file records the protocol,
and the commit that adds it is dated before any run.

## The tasks

`gcd`, `merge_sorted`, `majority_element`, `transpose`, `next_permutation`, `two_sum_sorted`: classic
tasks that Quod 0.1 can express (integers, sequences, tuples, no strings). They were chosen for their variety:
divisibility, multiset equality, a counting property, nested sequences, a lexicographic minimum, and a
freedom to declare. Their author also wrote the compiler, and knows what it can do: this limits the
independence of the choice, and it is stated here for that reason.

## The rules

1. **Before the first run,** no Quod program for these tasks is written, checked or read by anyone working on
   the compiler, and they are not used to test it.
2. **The compiler is frozen** at one tagged version for all the runs of this suite.
3. **Every arm runs the same tasks** with the same prompt rules, three trials per task, with the same model.
4. **Everything is reported,** including tasks no arm solves, and a bug found in a task's specification or
   oracle. A correction to a task after the first run is recorded here, with its reason.
5. **Afterwards, the suite is spent:** once its solutions have been read, a compiler change made because of it
   needs new held-out tasks to be measured.

## Corrections

None.
