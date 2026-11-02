module Quod.Tests.LemmaTests

open System.IO
open Xunit
open Quod.Diagnostics
open Quod.Tests.TypeTests
open Quod.Tests.VerifyTests
open Quod.Tests.CodegenTests

let private sumAndSplit =
    "fn sum(xs: seq<int>, i: nat, j: nat) -> int requires i <= j <= len(xs) decreases j - i {\n"
    + "  if i == j { 0 } else { sum(xs, i, j - 1) + xs[j - 1] } }\n"
    + "lemma sum_split(xs: seq<int>, i: nat, j: nat) requires i <= j <= len(xs)\n"
    + "  ensures sum(xs, 0, j) == sum(xs, 0, i) + sum(xs, i, j) decreases j - i {\n"
    + "  if i < j { sum_split(xs, i, j - 1); } }\n"

let private rangeSum =
    "fn range_sum(xs: seq<int>, ps: seq<int>, i: nat, j: nat) -> int\n"
    + "  requires len(ps) == len(xs) + 1 requires forall k in 0..len(xs) + 1: ps[k] == sum(xs, 0, k)\n"
    + "  requires i <= j <= len(xs) ensures result == sum(xs, i, j) {\n"
    + "  sum_split(xs, i, j); return ps[j] - ps[i]; }\n"

[<Fact>]
let ``a lemma has no value: it is not used in an expression`` () =
    assertError "is a lemma: it has no value"
        "lemma l(n: int) ensures n == n { }\nfn f(n: int) -> bool { l(n) }"

[<Fact>]
let ``a lemma returns nothing`` () =
    assertError "a lemma returns nothing" "lemma l(n: int) ensures n == n { return true; }"

[<Fact>]
let ``a lemma has no result, so no result type and no result in its ensures`` () =
    let d = Quod.Tests.ParserTests.syntaxErrorOf "lemma l(n: int) -> bool ensures n == n { }"
    Assert.Contains("a lemma has no result", d.Message)
    Assert.NotEmpty(errorsOf "lemma l(n: int) ensures result { }")

[<Fact>]
let ``only a lemma is called on its own`` () =
    assertError "only a lemma is called on its own" "fn g(n: int) -> int { n }\nfn f(n: int) -> int { g(n); return n; }"

[<Fact>]
let ``a lemma is proved like a function, and its call gives its ensures to the caller`` () =
    assertProved (sumAndSplit + rangeSum)
    // without the call, the range sum does not follow from the prefix sums
    let ds = verify (sumAndSplit + rangeSum.Replace("sum_split(xs, i, j); ", ""))
    Assert.NotEmpty(ds)

[<Fact>]
let ``a false lemma is refuted with a counterexample`` () =
    let d = assertRefuted "postcondition" "lemma pos(n: nat) ensures n > 0 { }"
    Assert.Equal<string list>([ "n = 0" ], d.Counterexample |> List.map (fun (k, v) -> k + " = " + v))

[<Fact>]
let ``a lemma is neither a contract to complete nor a contract style`` () =
    let ds = verifyAll (sumAndSplit + rangeSum)
    Assert.DoesNotContain(ds, fun d -> d.Fn = Some "sum_split" && (d.Kind = "completeness" || d.Kind = "contract"))

[<Fact>]
let ``lemmas and their calls are erased from the generated Python: range_sum is O(1)`` () =
    let _, modul = compile (sumAndSplit + rangeSum)
    Assert.DoesNotContain("def sum_split", modul)
    Assert.DoesNotContain("sum_split(", modul.Substring(modul.IndexOf "def range_sum"))
    // the review's case: a recursive lemma run at n = 5000 raised RecursionError
    let out =
        runPython modul
            "from itertools import accumulate\nxs = list(range(5000))\nps = list(accumulate(xs, initial=0))\nprint(range_sum(xs, ps, 0, 5000))"
    Assert.Equal("12497500\n", out)
