# Quod 0.1: scope

*English · [Français](quod-0.1.fr.md)*

> Status: implemented, and released as Quod 0.1 (2026-11-03). The [kernel draft](kernel.md)
> describes where the language is going; this document is what the first version contains, and
> nothing more. `quod reference` prints its language part.

## Goal

**An agent writes 6 of the 8 base VerifBench tasks in Quod 0.1, from the grammar alone given in its
prompt. The programs verify, pass the completeness check, compile to Python, and pass the same
hidden tests as the Python and Dafny arms.**

This is the "agent first" test: if an agent cannot write Quod from a short grammar, the bet of the
language must be revisited at 0.1, not at 1.0.

The six tasks: `binary_search`, `merge_intervals`, `rle_encode`, `bounded_queue`, `max_subarray`,
`rotate` (the two others, `parse_int` and `balanced`, need strings: 0.3).

## Technical choices

- Compiler written in **F#**, shipped as a **Native AOT** binary: no .NET runtime to install.
- Solver: **Z3**, spoken to in **SMT-LIB** through one **persistent `z3` process** per compilation
  (`push` / `pop`). See the [prototype](../proto/z3-aot/README.md).
- First target: **Python**. Next: **C#**, to deliver proved functions into existing .NET code
  bases (0.2). C, towards native code and WASM, comes later.
- The compiler produces a verified intermediate representation; each target is a translator of it.

## The language

### Types

| Type | Meaning |
|---|---|
| `int` | mathematical integer, unbounded (no overflow exists in 0.1) |
| `nat` | `int` known to be `>= 0`; the only refinement type of 0.1 |
| `bool` | `true`, `false` |
| `seq<T>` | immutable finite sequence |
| `(T1, T2, ...)` | tuple, components `t.0`, `t.1`, ... |

Assigning an `int` expression to a `nat` creates a proof obligation.

### Functions

```rust
fn name(p1: T1, p2: T2) -> T
  requires P          // zero or more
  ensures Q           // zero or more; `result` is the returned value
  loose (r1, r2) => L // optional: declared freedom (pillar 5)
  decreases D         // required for recursive functions
{ body }
```

All functions are pure: no input/output, no mutation of their arguments. Multiple results are a
tuple (`-> (int, int)`, `result.0`).

There are two kinds of bodies, told apart by their content:

- **Expression functions**: the body is a single expression (possibly `if c { a } else { b }`).
  They can be used inside contracts, and the verifier knows their definition.
- **Statement functions**: the body contains statements. They can only be called from code, and
  callers know them through their contract only (modular verification).

A **lemma** is a proof, not a function: it has no result, its `ensures` is what it proves, and
its body is the proof steps. It is checked like a statement function, and **erased** from the
generated code.

```rust
lemma name(p1: T1, p2: T2)
  requires P          // zero or more
  ensures Q           // what it proves (no `result`)
  decreases D         // required for recursive lemmas
{ steps }             // asserts, lemma calls, `if` to split cases; no `return`
```

### Statements

```rust
let x: T = e;          // immutable binding (type optional when inferable)
let mut y = e;         // mutable local
y = e;                 // assignment to a mutable local
if c { ... } else { ... }
while c
  invariant I          // one or more
  decreases D          // required
{ ... }
assert P;              // proof hint, checked
lemma_name(a, b);      // lemma call: a proof step, erased from the generated code
return e;              // or a final expression at the end of the body
```

### Expressions

- Literals: integers, `true`, `false`, `[a, b, c]`, `[]` (typed by context), tuples `(a, b)`.
- Arithmetic: `+ - *`, and `/`, `%` with a proof that the divisor is not zero. **Division is
  Euclidean** (the remainder is always `>= 0`), as in SMT-LIB; the Python backend emits a helper,
  since Python's `//` rounds differently for negative divisors.
- Comparisons `== != < <= > >=`, which chain (`0 <= i < n`), logic `&& || !`, implications `==>`
  `<==>`, conditional `if c { a } else { b }` (an expression, `else if` allowed).
- Sequences: `s[i]` (with a proof that `0 <= i < len(s)`), `len(s)`, slices `s[a..b]`, `s[a..]`,
  `s[..b]` (from `a` included to `b` excluded, with a proof of the bounds), concatenation `s + t`,
  equality `s == t` (same length, same elements).
- Calls to other functions (with a proof of their `requires`).
- In contracts and assertions: `result`, and bounded quantifiers
  `forall i in a..b: P`, `exists i in a..b: P` (`a` included, `b` excluded).

### Structs, enums and generics

Since 0.3, a program can name its data.

```rust
enum Decision {
  Accepted(int),
  Rejected(string),
  ToReview,
}

struct Field {
  name: string,
  confidence: i32,
}

fn decide(f: Field, threshold: i32) -> Decision
  ensures match result {
    Accepted(c) => c == f.confidence && c >= threshold && c >= 0,
    Rejected(_) => f.confidence < 0,
    ToReview => 0 <= f.confidence && f.confidence < threshold,
  }
{
  if f.confidence < 0 {
    Rejected("invalid: " + f.name)
  } else {
    if f.confidence >= threshold { Accepted(f.confidence) } else { ToReview }
  }
}
```

- A case's fields may be named, `Accepted(value: int)`, for who reads them outside Quod; in a `match`, they are given in order. A value is built like a call, in the order of its fields: `Field("total", 80)`, `Accepted(3)`. A case without fields is its name: `ToReview`. A struct's fields are read with `f.name`; an enum's with `match`.
- **`match` is an expression, and covers every case:** a case forgotten is a compile error that names it. `_` covers those not named before it, and comes last. A new case then falls into it silently, so prefer naming them in a contract.
- `==` compares by value. A type cannot hold itself: recursive types are not in 0.3.
- **Generics:** `enum Option<T>`, `fn first<T>(xs: seq<T>) -> option.Option<T>`. Each use makes a copy for its types, which is checked and proved like any function: **a generic function is proved only for the types it is used with.** Types come from the arguments or from what is expected; if neither says, give a variable its type. There are no constraints on `T`.
- `import option` gives `Option<T>` (`None`, `Some`) and `Result<T, E>` (`Ok`, `Err`), `is_some`, `value_or`, `is_ok`.
- **Across modules:** `fields.Candidate`, `fields.Candidate("a", 1)`, `option.None`. In a `match`, the type is known, so a case is written by its short name: `Some(x)`.
- **In Python,** frozen dataclasses, which check what their fields' types promise when they are built; a copy of a generic has names of its own, such as `Option__int_Some`.
- **In C#,** immutable classes equal by value (`IEquatable<T>`, `==`, and a hash on what they hold), which copy the lists they are given and hand out views that cannot be cast back. An enum has a `Match` method with one function per case, which gives the caller the exhaustiveness of `match`. Nested in the class of the module: `Rules.Field`, and for an enum an abstract class with a sealed class per case: `Rules.Decision.Accepted`, whose fields are `Value`, or `F0`, `F1` if they have no name. Two underscores in a row are reserved for the compiler. A copy of a generic is a class of its own, `Option.Option_int`, and not a C# generic. A function whose name would be that of a type gets `Of`: `level` next to `Level` is `LevelOf`.

### Bounded integers

Since 0.3, `i32` and `i64` hold what fits in 32 and 64 bits. `int` stays the default: it is a mathematical integer, and nothing can overflow.

```rust
fn midpoint(lo: i32, hi: i32) -> i32
  requires 0 <= lo && lo <= hi
  ensures result == lo + (hi - lo) / 2
{
  lo + (hi - lo) / 2   // lo + hi would be refused: the sum can leave i32
}
```

- **In code,** every `+ - * / %` and unary `-` on bounded operands has an obligation: the result fits. It is neither a silent overflow nor an exception, but a proof not met, with its counterexample.
- **In contracts, invariants and assertions, arithmetic is mathematical:** `ensures result == a + b` means what it says, and cannot overflow.
- **What widens is implicit and exact:** `i32` to `i64`, to `int`. What narrows is written, and must be proved: `to_i32(x)`, `to_i64(x)`. A literal takes the type its context wants, if it fits.
- Under a sequence or a tuple there is no conversion: a `seq<i32>` is not a `seq<int>`.
- An operation between a bounded integer and an `int` or a `nat` is in `int`. `len(xs)` stays a `nat`, with no bound: `to_i32(len(xs))` needs `requires len(xs) <= 2147483647`, which is checked at the public boundary.
- **For C#, prefer `i32` and `i64`.** Quod's `int` and `nat` are mathematical integers, which C# can only hold in a `BigInteger`: `int` in Quod is not `int` in C#. `i32` is C#'s `int` and `i64` its `long`.
- `/` and `%` are Euclidean, as for `int`, in every backend.
- In Python, a parameter is checked against its bounds at the public boundary; the elements of a list only with `--check-requires all`, which the docstring says. In C#, they are `int` and `long`. A struct or a case checks all it holds when it is built, in depth.

### Characters and strings

Since 0.3, `char` is a Unicode scalar value, and `string` is `seq<char>`: `len`, indexing, slices, `+`, `==` and quantifiers work on it as on any sequence.

- A literal is `'a'` or `"text"`, with the escapes `\n \t \r \0 \\ \' \" \u{1F600}`.
- `len(s)` counts scalar values: an emoji is 1, and a letter with a combining accent is 2. Nothing is normalized, and nothing depends on a locale: normalize before the boundary.
- `char` is not an integer. `'a' + 1` is a type error. `code(c)` gives its number, and `char_of(n)` the char, with the obligation that `n` be a scalar value (0 to 10FFFF, without D800 to DFFF). Two chars compare with `<` by their scalar values.
- `import strings` gives the standard library, in Quod and proved with your program: `is_digit`, `is_space`, `is_letter` (ASCII), `starts_with`, `ends_with`, `occurs_at`, `find`, `trim`, `split`, `join`, `all_digits`, `is_int`, `parse_int`, `int_to_string`. A local file `strings.quod` hides it, with a warning.
- In Python, a string is a `str` and a char a one-character `str`. In C#, a string is a `string` and a char an `int`, its scalar value. Both refuse a lone surrogate at the boundary.

- **A long input:** a function ending by calling itself runs as a loop, whatever the length. Otherwise the depth of a recursion follows its input. For that case, `run_by`: contracts read a definition by recursion, and code runs a loop proved equal. The loop cannot require more than the function it runs for, nor call it back.

```rust
fn total(xs: seq<int>) -> int
  run_by total_loop
{
  total_upto(xs, len(xs))
}

fn total_loop(xs: seq<int>) -> int
  ensures result == total(xs)
{
  ...
}
```

### Modules

Since 0.3, a file is a module, named after the file. `import name`, at the top of a file, finds `name.quod` next to it.

```rust
// planning.quod
import intervals

fn free_slot(a: (int, int), b: (int, int)) -> bool
  ensures result == intervals.disjoint(a, b)
{
  intervals.disjoint(a, b)
}
```

- A function of another module is always called by its full name, `intervals.disjoint`. A function of the same module is called by its short name. There is no alias and no partial import.
- `private fn` or `private lemma` is called from its own module only, and has no public name in the generated code. Everything else is public. A public `ensures` may mention a private function of its module.
- A proof sees an imported function as it sees a local one: an expression function by its definition, a statement function by its contract only.
- `quod check` and `quod build` verify the file and all it imports, every time. An error in an imported module is reported in that file, and refuses the program. A cycle of imports is an error.
- In the MCP server, a program given as `source` finds its imports in the directory of the server.

### Comments

`// ...` to the end of the line.

## Verification

- Verification conditions are generated by weakest preconditions and sent to Z3 as SMT-LIB.
- Every obligation gets a status: ✅ proved, or ❌ refuted **with a counterexample**; a solver
  `unknown` or timeout is an error too.
- Obligations: `requires` of each call, `ensures` at each return, loop `invariant` (on entry and
  preserved), `decreases` (loops and recursion), sequence bounds, non-zero divisors, `nat`
  assignments, `assert`.
- **Arithmetic obligations, apart.** An obligation about integers and booleans only is also put
  to a second z3 process that holds none of the program's axioms (those of sequences are
  quantified, and with them z3 does not use its solver for nonlinear arithmetic): first briefly
  when all its facts are arithmetic, and again when the shared solver gives up. A bug like
  `a == b * b * b` gets the same verdict whatever else the file holds.
- **Counterexamples by execution.** Before asking the solver, the compiler runs each function on
  small inputs that satisfy its `requires`: zero values, each integer constant of the program and
  its neighbours (`c - 1`, `c`, `c + 1`), then random values (ints in -6..6 or a constant,
  sequences of 0 to 5 elements, or as long as a constant of the program, up to 50). A parameter that the `requires` define from the others, such as
  a table of prefix sums, is built from them. When few random inputs satisfy the `requires` (a
  quantified one: four strictly increasing values from 10 up), the solver finds some: for each
  length 0 to 6, a sequence is that many unknowns, the quantifiers of the `requires` unfold over
  the known range, and the formula, without quantifiers, is easy for it; random bounds on the
  unknowns vary the inputs, with the edge cases of an int parameter against the elements of a
  sequence (equal to one, above all, below all). Every obligation is checked on the way, including
  that each recursive call makes the `decreases` measure smaller (a call that does not would run
  forever). A broken obligation is reported with these inputs: a confirmed counterexample, in
  milliseconds. When the solver then fails on an obligation that no run broke, the message gives
  the facts: how many runs, out of how many inputs tried, that none broke it, and which
  branches of the function no run took (`no run took the 'if' at line 4 (condition true)`). That does not
  show the property holds (a bug may need other inputs); if it does, the proof needs a hint. When
  no input tried satisfies the `requires`, the message says that the function was not run.
- `--runtime-checks`: instead of refusing to build when an obligation is not proved, check the
  contracts of the functions concerned at run time in the generated Python, and list them in the
  report (the ⚠️ status of [principle 2](kernel.md)).

### Hints and lemmas

What a proof needs beyond the contracts is written in the code, and checked like the rest:

- `assert P;` proves P, then assumes it. It is the way to name a fact the solver does not find
  alone, typically about slices: `assert xs[..k + 1] == xs[..k] + [xs[k]];`.
- A **lemma** states a fact in its `ensures` and proves it in its body. Calling it, as a
  statement, gives the fact for its arguments: `sum_split(xs, i, j);`. A recursive lemma is a
  proof by induction: the recursive call is the induction hypothesis, and `decreases` makes it
  well-founded.

  ```rust
  lemma sum_split(xs: seq<int>, i: nat, j: nat)
    requires i <= j <= len(xs)
    ensures sum(xs, 0, j) == sum(xs, 0, i) + sum(xs, i, j)
    decreases j - i
  {
    if i < j { sum_split(xs, i, j - 1); }
  }
  ```

  Lemmas and their calls are erased from the generated code: a proof costs nothing at run time.
  A lemma has no value, so it cannot appear in an expression, and nothing it proves can change
  what the code computes. It is not subject to the completeness check (it has no result to
  determine), and the summary counts lemmas apart.
- An `exists` in an invariant or an `ensures` needs its witness: keep, in a variable, the index
  that makes it true, and state the fact for that index; the solver does not invent witnesses.
- Facts about `a % n` for an `n` the solver does not know are mostly beyond Z3 (nonlinear
  arithmetic); facts where `a` is known to lie in `0..2 * n` are within reach.

## Completeness (pillar 5), built in

- For every function with `ensures`, the compiler asks Z3 whether two different results can both
  satisfy the contract for the same valid input (or whether `loose` is violated when declared).
- `unsat`: ✅ determined. `sat`: ❌ underspecified, and **Z3's model is the witness** (the input
  and the two results), with no need to run the function. `unknown`: ⚠️ inconclusive (a warning,
  not an error).
- An underspecified function does not compile, unless its freedom is declared with `loose`.
- A `loose` that declares every result acceptable is a **warning** (`loose-accepts-all`): a
  relation that holds for any two results (`loose (a, b) => true`), or one whose parts each
  concern one result only (`a < len(xs) && b < len(xs)`, which the ensures already give). Either
  way the completeness check proves nothing. A relation says what two acceptable results have
  in common: `xs[a] == xs[b]` for two indices of a maximum.
- Each `loose` is shown with two different results it accepts on one input, in the JSON (`"kind": "loose"`, `"status":
  "witness"`) and in the summary: a reviewer reads what the freedom allows.
- When the result is an index (`xs[result]`, `0..result`), the quantifiers of the `ensures` are
  also given to the solver at both results: "the first index of a maximum" is then recognised
  as determined.

### Contract style

A determined contract can still say little: the shortest one is `ensures result == <the body>`,
and agents write it. Every contract is therefore classified, in the summary of `quod check` and
as a `note` in the JSON (`"kind": "contract"`):

- **properties**: what the result is (bounds, order, membership...), not how to compute it;
- **model**: `result == f(...)`, with `f` a function of the program (a model, or a reference
  implementation): the proof shows that the code computes what the model computes, so the model
  is what a reviewer reads;
- **restated**: `result == e` where `e` is, word for word, a value the body returns, or a call to a
  function whose definition reads as the body once unfolded. A **warning**:
  the proof then shows little more than the absence of errors. A small formula that is its own
  specification can stay as it is.
- **none**: a statement function without `ensures`. A **warning**: nothing is proved about its
  result, and its callers, who know it by its contract only, know nothing about it. (An expression
  function without `ensures` is not classified: the verifier knows its definition.) With
  `--require-contracts` (`check`, `build`, `mcp`) it is an **error**, as are an expression function
  without `ensures` that no other function calls, a `loose` that accepts every result, a lemma written
  as a function, a `requires` that fixes a parameter to one value or a sequence to a length of 0 or 1 (a fixed
  length of 2 or more is a record), and a `requires` that already gives the `ensures` for an argument returned unchanged,
  so `verified` means that something was proved about each result.
- **lemma written as a function** (`lemma-as-function`): a statement function returning `bool`
  that returns `true` on every path, or says `ensures result`, its other `ensures` being facts,
  and whose value the program never uses (`if feature_enabled() { ... }` uses it; a lemma could
  not). A **warning**: it verifies, but the generated code runs it at every call. Write it as a
  `lemma`, which is erased.

Lemmas are not classified: their `ensures` is what they prove.

## Diagnostics

Human-readable by default, JSON with `--json`. One entry per finding:

```json
{
  "file": "sums.quod", "fn": "sum_to", "line": 7, "col": 3, "endLine": 7, "endCol": 30,
  "kind": "proof | completeness | type | syntax | contract | loose | review",
  "status": "refuted | underspecified | inconclusive | not-attempted | error | ...",
  "severity": "error | warning | note",
  "property": "invariant #2 is preserved by the loop body",
  "counterexample": { "n": "2" },
  "witness": { "x": "0", "result_a": "0", "result_b": "-1" },
  "evidence": "run | solver | unconfirmed",
  "reason": "timeout | incomplete quantifiers | ...",
  "message": "..."
}
```

- `counterexample` (a proof obligation): the inputs that break it. `witness` (completeness): the
  input and the two different results the contract accepts.
- `evidence`, with a counterexample: `run` (the function was run on these inputs and the
  obligation broke: certain), `unconfirmed`, `solver`. A model the solver finds is run too: if the
  obligation breaks, the evidence is `run`; if the run breaks nothing, the model is a state the code
  does not reach (an invariant too weak to prove the obligation, typically), and the diagnostic is
  `inconclusive` and `unconfirmed`; `solver` when the model cannot be run. A candidate model of an
  `unknown` is `unconfirmed` too.
- `reason`, when the solver gave no verdict: `timeout`, or what it says (`incomplete
  quantifiers`, `incomplete (theory arithmetic)`...). In text mode, shown after `solver:`.
- Notes (`severity: note`, not printed in text mode) tell a reviewer what the proofs cannot vouch
  for: the style of each contract (`contract`), each `loose` and its relation (`loose`), and each
  function the contracts are stated with, directly or through the expression functions they call
  (`review`, with `property: "used by the contracts of f, g"`): a determined contract can still
  describe the wrong function. The summary line lists them:
  `...; loose: binary_search; to review with the contracts: sum (prefix_sums, range_sum)`.

## Command line

```
quod check file.quod [--json] [--z3 PATH] [--timeout SECONDS] [--budget SECONDS] [--require-contracts]
quod build file.quod [--target python|csharp] [--namespace NAME] [--check-requires all] [-o DIR] [--runtime-checks] [--require-contracts] [--json]
quod mcp [--require-contracts]  # check, build, run and the reference, served to an AI agent (MCP, stdio)
quod reference [SECTION]   # the language reference, or one section of it
quod contract file.quod cases.json --function NAME   # evaluate a contract on given arguments and results
```

`z3` is looked up next to `quod`, then in `QUOD_Z3`, then on `PATH`.

`--timeout` limits each try of the solver on a proof obligation (10 s by default; an obligation
gets a second try, on a fresh solver, only when the first gave up quickly, not after a timeout); `--budget` limits the whole check
(300 s by default, 0 for none), since an agent waits for the whole of it before going on.
Functions are checked in the order of the file. The obligations left when the budget is used
up are not sent to the solver: one diagnostic per function reports how many, with the status
`not-attempted` (and `reason: budget`), distinct from a solver timeout; a completeness check
left for lack of time is a warning with the same status. A termination proof left for lack
of time is not proved: the function's definition stays unknown to the solver.

## Python backend

- One Python module per Quod file. Each function is a public `def name`, which puts its arguments
  in shape once, and an implementation `_quod_f_name`, which Quod code calls (recursion included),
  type hints included. Lemmas are not generated.
- `seq<T>` is a Python `list` (accepted as any sequence on input), tuples are tuples, `int`/`nat`
  are `int`, `bool` is `bool`.
- `quod build` generates code only for a program that verifies. With `--runtime-checks`, a function
  whose proofs fail is still built, and its contracts (requires, ensures, invariants before each
  iteration and after the last one, asserts) are checked at run time, and so is what a type promises:
  an `i32` or `i64` result of an operation, the `nat` an `int` becomes, a conversion. They raise
  `AssertionError` and are not Python `assert`s, so `python -O` keeps them. So are the functions that
  rest on such a function, and those it calls. A contract found underspecified blocks the build: no
  run-time check can tell that a result is the intended one. When the solver cannot decide, it is a
  warning.
- **A Python caller proves nothing.** A public function checks its `requires` without quantifier or call, and
  that a `nat` parameter is `>= 0` (`ValueError`). A list of `nat` counts as quantified. The others stay the caller's duty, and its docstring says so; `--check-requires all` checks them
  too, at their cost. Calls between Quod functions check nothing.
- In such a function, indexing and slicing check their bounds (Python would wrap a negative index
  and clamp a slice), and a division by zero raises `ZeroDivisionError`. A `nat` that would be
  negative is not checked.
- Proved `ensures` produce no runtime code, only the function's docstring.
- Quod semantics where Python differs: Euclidean `/` and `%` (`_quod_div`, `_quod_mod`), and
  sequences that never change. A list argument is not copied (the generated code never mutates
  an argument): O(1) on entry, so a binary search stays O(log n). A tuple is converted to a list;
  a sequence of tuples or of sequences is rebuilt at the public boundary (O(n)), since its elements
  may come as lists. A mutable local extended with `x = x + [e]` becomes `x.append(e)` when no
  other variable, argument, tuple or sequence can share its list: a loop that builds a sequence
  stays O(n), not O(n²). As arguments are not copied, a function that returns an argument as it
  is (`fn id(xs: seq<int>) -> seq<int> { xs }`) gives the Python caller its own list back: changing
  it afterwards changes the caller's input too, as with any Python function. Builtins are aliased (`_quod_len`...), so a
  Quod function named `len` or `list` shadows nothing the generated code needs. A name that is a
  Python keyword gets a trailing `_`.
- Known limit: recursion is Python recursion (default depth 1000). **A valid input can give a different answer by
  backend:** a recursion too deep raises in Python at about 1000 calls, in the evaluator of `quod_run` at about the same depth, and in C# much further.

## C# backend

- One class per Quod file (`--namespace`, `Quod.Generated` by default), in `Name.g.cs`. The code stays
  within C# 7.3 and the standard library, for .NET Framework 4.7.2 as for .NET Core and later. A project
  on .NET Framework references `System.Numerics`.
- Each function is a public method in PascalCase and a private implementation `_quod_f_name`, which
  Quod code calls. Lemmas are not generated. Two functions with the same public name are refused.
- `int` and `nat` are `BigInteger`, `bool` is `bool`, `seq<T>` is `IReadOnlyList<T>` (not copied on entry),
  tuples are `ValueTuple`. Equality is structural; `/` and `%` are Euclidean.
- **A C# caller proves nothing.** A public method checks `null` for its sequences, its `requires` without
  quantifier or call, and that a `nat` parameter is `>= 0` (`ArgumentException`). A list of `nat` counts as quantified. The others stay the caller's duty, and its comment says so;
  `--check-requires all` checks them too, at their cost, and so does defining `QUOD_CHECK_REQUIRES` in the calling
  project. Calls between Quod functions check nothing.
- A method with a list of integers has two more forms, for `int` and `long`: the list is seen as Quod's, not copied.
  The result stays a `BigInteger`.
- A recursive function calls `EnsureSufficientExecutionStack`: too deep a recursion raises an exception
  instead of ending the process.
- With `--runtime-checks`, unproved contracts and what a type promises raise `QuodContractException` (an operation on `i32` or `i64` is computed without bounds, then checked), and the bounds of a list always raise.
- The generator is not proved. The generated code is tested against the evaluator on the programs of the
  repository, for both targets, and against the hidden tests of VerifBench.

## Example

```rust
fn binary_search(xs: seq<int>, target: int) -> int
  requires forall i in 0..len(xs): forall j in i..len(xs): xs[i] <= xs[j]   // sorted
  ensures -1 <= result && result < len(xs)
  ensures result >= 0 ==> xs[result] == target
  ensures result == -1 ==> forall i in 0..len(xs): xs[i] != target
  loose (r1, r2) => (r1 == -1) == (r2 == -1)   // any index of a duplicate will do
{
  let mut lo = 0;
  let mut hi = len(xs);
  while lo < hi
    invariant 0 <= lo && lo <= hi && hi <= len(xs)
    invariant forall i in 0..lo: xs[i] < target
    invariant forall i in hi..len(xs): xs[i] > target
    decreases hi - lo
  {
    let mid = lo + (hi - lo) / 2;
    if xs[mid] < target { lo = mid + 1; }
    else if xs[mid] > target { hi = mid; }
    else { return mid; }
  }
  return -1;
}
```

## Not in 0.1

| Version | Planned content |
|---|---|
| 0.2 | what a .NET project needs beyond the C# backend and `Quod.Build`, which came with 0.1.5 |
| 0.4 | general refinement types |
| 0.4 | capabilities and input/output, sealed contracts, maps and sets |
| later | C backend (native code, WASM); what a compiler needs, for 2.0 |

**Quod 2.0 will be written in Quod.** Self-hosting needs strings, algebraic types (syntax trees),
maps, and files: those are the milestones between 0.1 and 2.0. Until then the F# compiler is kept
simple and cleanly split into stages, so that it can be rewritten.

## Implementation steps

1. Parser: F# syntax tree, error messages with positions.
2. Type checker.
3. Verification conditions, persistent Z3 session.
4. Completeness check, witnesses from Z3 models.
5. Python backend.
6. The six VerifBench tasks in Quod: first written by hand to validate, then by an agent from the
   grammar alone.
7. JSON diagnostics, Native AOT release (Windows, Linux, macOS).

## Done when

1. The six tasks, written by hand, verify, pass the completeness check (or declare `loose`), and
   pass the VerifBench hidden tests once compiled to Python.
2. An agent given only this language description writes them; the results are reported next to
   the Python and Dafny arms of VerifBench.
3. `quod` runs as a self-contained binary on Windows and Linux.
