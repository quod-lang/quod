module Quod.Tests.VerifyTests

open System
open System.IO
open Xunit
open Quod.Diagnostics

/// z3 for the tests: QUOD_Z3 or PATH (as the compiler does), else the one a Dafny install
/// ships, for convenience on a development machine.
let z3Path =
    match Quod.Smt.findZ3 None with
    | Some p -> p
    | None ->
        let store = Path.Combine(Environment.GetFolderPath Environment.SpecialFolder.UserProfile, ".dotnet", "tools", ".store", "dafny")
        let found =
            if Directory.Exists store then Directory.GetFiles(store, "z3*", SearchOption.AllDirectories) |> Array.tryFind (fun f -> Path.GetFileName(f).StartsWith "z3")
            else None
        match found with
        | Some p -> p
        | None -> failwith "z3 not found: set QUOD_Z3 to the z3 executable to run the verification tests"

/// Parse, type-check and verify; type errors fail the test.
let verifyAll (src: string) : Diagnostic list =
    let prog = Quod.Parser.parseProgram "test.quod" src
    let typed, errs = Quod.Typecheck.check "test.quod" prog
    Assert.True(errs.IsEmpty, "type errors: " + String.concat " | " (errs |> List.map (fun d -> d.Message)))
    use z3 = new Quod.Smt.Session(z3Path, 10000, None)
    (Quod.Vcgen.verify "test.quod" typed z3).Diagnostics

/// The proof diagnostics only (these tests are about proofs; completeness has its own tests).
let verify (src: string) : Diagnostic list = verifyAll src |> List.filter (fun d -> d.Kind = "proof")

let assertProved (src: string) =
    let ds = verify src
    Assert.True(ds.IsEmpty, "unexpected failures: " + String.concat " | " (ds |> List.map toText))

/// Exactly one failure, whose property contains `label`; returns it.
let assertRefuted (label: string) (src: string) : Diagnostic =
    let ds = verify src
    Assert.True(ds |> List.exists (fun d -> d.Property |> Option.exists (fun p -> p.Contains label)),
                "expected a failure on '" + label + "', got: " + String.concat " | " (ds |> List.map toText))
    ds |> List.find (fun d -> d.Property |> Option.exists (fun p -> p.Contains label))

[<Fact>]
let ``the examples verify`` () =
    let rec up (d: DirectoryInfo) =
        if Directory.Exists(Path.Combine(d.FullName, "examples")) then Path.Combine(d.FullName, "examples")
        else up d.Parent
    for f in Directory.GetFiles(up (DirectoryInfo AppContext.BaseDirectory), "*.quod") do
        assertProved (File.ReadAllText f)

[<Fact>]
let ``the VerifBench solutions written in Quod verify`` () =
    let rec up (d: DirectoryInfo) =
        if Directory.Exists(Path.Combine(d.FullName, "bench", "quod")) then Path.Combine(d.FullName, "bench", "quod")
        else up d.Parent
    let files = Directory.GetFiles(up (DirectoryInfo AppContext.BaseDirectory), "solution.quod", SearchOption.AllDirectories)
    Assert.NotEmpty(files)
    for f in files do
        let ds = verifyAll (File.ReadAllText f) |> List.filter (fun d -> d.Severity = Error)
        Assert.True(ds.IsEmpty, f + ": " + String.concat " | " (ds |> List.map toText))

[<Fact>]
let ``assert false is refuted, with a counterexample on the parameters`` () =
    let d = assertRefuted "assertion" "fn f(x: int) -> int { assert false; return x; }"
    Assert.Equal("refuted", d.Status)
    Assert.Equal<string list>([ "x" ], d.Counterexample |> List.map fst)

[<Fact>]
let ``postconditions: proved and refuted`` () =
    assertProved "fn f(x: int) -> int ensures result > x { x + 1 }"
    let d = assertRefuted "postcondition (ensures #1)" "fn f(x: int) -> int ensures result > x { x - 1 }"
    Assert.NotEmpty(d.Counterexample)

[<Fact>]
let ``division needs a non-zero divisor, and is Euclidean`` () =
    assertRefuted "divisor is not zero" "fn f(a: int, b: int) -> int { a / b }" |> ignore
    assertProved "fn f(a: int, b: int) -> int requires b != 0 { a / b }"
    // Euclidean: the remainder is never negative, even for a negative divisor
    assertProved "fn f(a: int, b: int) -> int requires b != 0 ensures 0 <= result { a % b }"

[<Fact>]
let ``sequence bounds and slices`` () =
    assertRefuted "index in bounds" "fn f(xs: seq<int>) -> int { xs[0] }" |> ignore
    assertProved "fn f(xs: seq<int>) -> int requires len(xs) > 0 { xs[0] }"
    assertRefuted "slice bounds" "fn f(xs: seq<int>, k: int) -> seq<int> { xs[k..] }" |> ignore
    assertProved "fn f(xs: seq<int>, k: nat) -> seq<int> requires k <= len(xs) ensures len(result) == len(xs) - k { xs[k..] }"

[<Fact>]
let ``guards: the right operand of && is checked only when the left one holds`` () =
    assertProved "fn f(xs: seq<int>, i: int) -> bool { 0 <= i && i < len(xs) && xs[i] > 0 }"
    assertProved "fn f(xs: seq<int>) -> int { if len(xs) > 0 { xs[0] } else { 0 } }"

[<Fact>]
let ``nat values must be proved non-negative`` () =
    assertRefuted "value is a nat" "fn f(x: int) -> nat { x }" |> ignore
    assertProved "fn f(x: int) -> nat requires x >= 0 { x }"
    assertProved "fn f(xs: seq<int>) -> nat { len(xs) }"

[<Fact>]
let ``calls: the precondition is checked, the postcondition is known`` () =
    let lib = "fn half(n: int) -> int requires n % 2 == 0 ensures result * 2 == n { let h = n / 2; return h; }\n"
    assertRefuted "precondition of 'half'" (lib + "fn g(x: int) -> int { half(x) }") |> ignore
    assertProved (lib + "fn g(x: int) -> int ensures result == x { half(2 * x) }")

[<Fact>]
let ``expression functions are known by their definition`` () =
    assertProved "fn double(x: int) -> int { 2 * x } fn g(x: int) -> int ensures result == x + x { double(x) }"

[<Fact>]
let ``recursion must decrease`` () =
    assertProved "fn fact(n: nat) -> nat decreases n { if n == 0 { 1 } else { n * fact(n - 1) } }"
    assertRefuted "recursive call decreases" "fn loop(n: nat) -> nat decreases n { if n == 0 { 0 } else { loop(n) } }" |> ignore

[<Fact>]
let ``loops: entry, preservation, termination`` () =
    let good =
        "fn sum_to(n: nat) -> int ensures result == n * (n + 1) / 2 {\n"
        + "  let mut i = 0; let mut s = 0;\n"
        + "  while i < n invariant 0 <= i <= n invariant s == i * (i + 1) / 2 decreases n - i\n"
        + "  { i = i + 1; s = s + i; }\n"
        + "  return s; }"
    assertProved good
    assertRefuted "holds on entry" (good.Replace("let mut s = 0;", "let mut s = 1;")) |> ignore
    assertRefuted "is preserved" (good.Replace("s = s + i;", "s = s + 1;")) |> ignore
    assertRefuted "gets smaller" (good.Replace("decreases n - i", "decreases n + i")) |> ignore

[<Fact>]
let ``if statements merge their branches`` () =
    assertProved
        "fn abs(x: int) -> int ensures result >= 0 ensures result == x || result == -x { let mut r = x; if x < 0 { r = -x; } return r; }"

[<Fact>]
let ``sequences: concatenation, equality, quantifiers`` () =
    assertProved "fn f(a: seq<int>, b: seq<int>) -> seq<int> ensures len(result) == len(a) + len(b) { a + b }"
    assertProved "fn f(x: int) -> seq<int> ensures result == [x] + [] { [x] }"
    assertProved
        "fn f(xs: seq<int>) -> bool requires forall i in 0..len(xs): xs[i] > 0 ensures result ==> len(xs) > 0 { len(xs) > 0 && xs[0] > 0 }"

[<Fact>]
let ``tuples`` () =
    assertProved "fn swap(p: (int, bool)) -> (bool, int) ensures result.0 == p.1 && result.1 == p.0 { (p.1, p.0) }"

[<Fact>]
let ``an impossible precondition is rejected`` () =
    let ds = verify "fn f(x: int) -> int requires x > 0 && x < 0 ensures result == 42 { 0 }"
    Assert.True(ds |> List.exists (fun d -> d.Property = Some "precondition is satisfiable"))

[<Fact>]
let ``quantified facts carry over sequence operations (reverse by a loop)`` () =
    // Z3's own sequence theory times out on these: see the sequence axioms in Vcgen
    let reverse (step: string) (inv: string) =
        "fn rev(xs: seq<int>) -> seq<int> ensures len(result) == len(xs) ensures forall i in 0..len(xs): result[i] == xs[len(xs) - 1 - i] {\n"
        + "  let mut r: seq<int> = []; let mut i = 0;\n"
        + "  while i < len(xs) invariant 0 <= i <= len(xs) invariant len(r) == i invariant forall j in 0..i: r[j] == " + inv + " decreases len(xs) - i\n"
        + "  { r = " + step + "; i = i + 1; }\n"
        + "  return r; }"
    assertProved (reverse "r + [xs[len(xs) - 1 - i]]" "xs[len(xs) - 1 - j]")
    assertProved (reverse "[xs[i]] + r" "xs[i - 1 - j]")

[<Fact>]
let ``a run-length step keeps a quantified property of the prefix`` () =
    assertProved
        ("fn step(r: seq<(int, nat)>, x: int) -> seq<(int, nat)> requires forall i in 0..len(r): r[i].1 >= 1 ensures forall i in 0..len(result): result[i].1 >= 1 "
         + "{ if len(r) > 0 && r[len(r) - 1].0 == x { r[..len(r) - 1] + [(x, r[len(r) - 1].1 + 1)] } else { r + [(x, 1)] } }")
[<Fact>]
let ``a bug the solver times out on is refuted by running the function (the review's bug.quod)`` () =
    // ps is built from xs (the requires define it); i == 2 breaks the postcondition
    let rec up (d: DirectoryInfo) =
        if File.Exists(Path.Combine(d.FullName, "bench", "review", "prefix_sums.quod")) then Path.Combine(d.FullName, "bench", "review", "prefix_sums.quod")
        else up d.Parent
    let src =
        File.ReadAllText(up (DirectoryInfo AppContext.BaseDirectory))
            .Replace("  return ps[j] - ps[i];", "  return ps[j] - ps[i] + 0 * j + (if i == 2 { 1 } else { 0 });")
    let d = assertRefuted "postcondition (ensures #1)" src
    Assert.Equal("refuted", d.Status)
    Assert.Equal("2", (Map.ofList d.Counterexample).["i"])

[<Fact>]
let ``false invariants get a counterexample from execution`` () =
    let d =
        assertRefuted "invariant #3 is preserved"
            ("fn max_index(xs: seq<int>) -> int requires len(xs) > 0 ensures 0 <= result < len(xs) ensures forall i in 0..len(xs): xs[i] <= xs[result] {\n"
             + "  let mut best = 0; let mut i = 1;\n"
             + "  while i < len(xs) invariant 1 <= i <= len(xs) invariant 0 <= best < len(xs) invariant forall j in 0..i: xs[j] <= xs[best] decreases len(xs) - i\n"
             + "  { if xs[i] > xs[best] { best = i; } i = i + 2; }\n"
             + "  return best; }")
    Assert.NotEmpty(d.Counterexample)
[<Fact>]
let ``a recursive call that does not decrease gets a counterexample from execution`` () =
    // sum(xs, i, j - 0) recurses forever: the solver may only time out, running it shows it
    let d =
        assertRefuted "recursive call decreases"
            ("fn sum(xs: seq<int>, i: nat, j: nat) -> int requires i <= j <= len(xs) decreases j - i {\n"
             + "  if i == j { 0 } else { sum(xs, i, j - 0) + xs[j - 1] } }")
    Assert.NotEmpty(d.Counterexample)

[<Fact>]
let ``a lemma whose recursive call does not decrease gets a counterexample from execution`` () =
    let d =
        assertRefuted "recursive call decreases"
            ("fn down(n: nat) -> bool ensures result decreases n {\n"
             + "  if n == 0 { return true; } let ih = down(n); return ih; }")
    Assert.NotEmpty(d.Counterexample)

[<Fact>]
let ``a counterexample says where it comes from: a run, or the solver`` () =
    // no small input or constant of the program satisfies the requires (x > 56 with y = 8 at
    // least), and the inputs found by the solver cannot see through the call to big: the
    // counterexample comes from the solver
    let solver =
        assertRefuted "postcondition"
            "fn big(y: int) -> bool { y > 7 }\nfn f(x: int, y: int) -> int requires big(y) && x > 7 * y ensures result > 0 { x - 7 * y - 5 }"
    Assert.Equal(Some "solver", solver.Evidence)
    let run = assertRefuted "postcondition" "fn g(x: int) -> int ensures result > 0 { x }"
    Assert.Equal(Some "run", run.Evidence)

[<Fact>]
let ``an inconclusive proof gives the solver's reason`` () =
    // a^3 + b^3 = c^3 has no solution in positive integers: nonlinear, beyond the solver
    let ds =
        verify "fn fermat(a: int, b: int, c: int) -> int requires a > 0 && b > 0 && c > 0 ensures result != 0 { a * a * a + b * b * b - c * c * c }"
    let d = ds |> List.exactlyOne
    Assert.Equal("inconclusive", d.Status)
    Assert.True(d.Reason.IsSome)

[<Fact>]
let ``the program's constants are among the inputs run: a bug at n == 1000 is found`` () =
    let d =
        assertRefuted "postcondition"
            ("fn isqrt(n: nat) -> nat ensures result * result <= n ensures n < (result + 1) * (result + 1) {\n"
             + "  let mut lo = 0; let mut hi = n + 1;\n"
             + "  while hi - lo > 1 invariant 0 <= lo < hi invariant lo * lo <= n invariant n < hi * hi decreases hi - lo\n"
             + "  { let mid = lo + (hi - lo) / 2; if mid * mid <= n { lo = mid; } else { hi = mid; } }\n"
             + "  if n == 1000 { return lo + 1; }\n"
             + "  return lo; }")
    Assert.Equal<(string * string) list>([ "n", "1000" ], d.Counterexample)
    Assert.Equal(Some "run", d.Evidence)

[<Fact>]
let ``inputs that a quantified requires makes rare come from the solver, and are run`` () =
    // the external counter-review's case: four strictly increasing values from 4 up, which no
    // small random input gives; the bug needs xs[3] > 40
    let d =
        assertRefuted "postcondition"
            ("fn first(xs: seq<int>) -> int requires len(xs) >= 4 requires forall i in 0..len(xs) - 1: xs[i] < xs[i + 1]\n"
             + "  requires xs[0] > 3 ensures result == xs[0] {\n"
             + "  if xs[3] > 40 { return xs[1]; } return xs[0]; }")
    Assert.Equal(Some "run", d.Evidence)
