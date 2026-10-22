module Quod.Tests.CompletenessTests

open Xunit
open Quod.Diagnostics
open Quod.Tests.VerifyTests

/// The completeness verdict of the single function `f` in `src` (whose proofs must pass).
let verdict (src: string) : Diagnostic option =
    let ds = verifyAll src
    let proofs = ds |> List.filter (fun d -> d.Kind = "proof")
    Assert.True(proofs.IsEmpty, "proofs should pass: " + String.concat " | " (proofs |> List.map toText))
    ds |> List.tryFind (fun d -> d.Kind = "completeness")

let assertDetermined (src: string) =
    match verdict src with
    | None -> ()
    | Some d -> failwith ("expected a determined contract, got: " + toText d)

/// Underspecified, with a witness that names result_a and result_b; returns the witness.
let assertUnderspecified (src: string) : Map<string, string> =
    match verdict src with
    | Some d when d.Status = "underspecified" ->
        Assert.Equal(Error, d.Severity)
        let w = Map.ofList d.Counterexample
        Assert.True(w.ContainsKey "result_a" && w.ContainsKey "result_b")
        Assert.NotEqual<string>(w.["result_a"], w.["result_b"])
        w
    | other -> failwith ("expected an underspecified contract, got: " + (other |> Option.map toText |> Option.defaultValue "determined"))

[<Fact>]
let ``complete contracts are determined`` () =
    assertDetermined "fn inc(x: int) -> int ensures result == x + 1 { x + 1 }"
    assertDetermined "fn max_of(a: int, b: int) -> int ensures result >= a && result >= b ensures result == a || result == b { if a >= b { a } else { b } }"
    assertDetermined "fn abs(x: int) -> int ensures result >= 0 ensures result == x || result == -x { if x < 0 { -x } else { x } }"
    assertDetermined "fn swap(p: (int, int)) -> (int, int) ensures result == (p.1, p.0) { (p.1, p.0) }"

[<Fact>]
let ``a lower bound alone is underspecified, with a confirmed witness`` () =
    let w = assertUnderspecified "fn f(x: int) -> int ensures result > x { x + 1 }"
    Assert.True(w.ContainsKey "x")

[<Fact>]
let ``clamp without its out-of-range cases is underspecified`` () =
    assertUnderspecified
        "fn clamp(x: int, lo: int, hi: int) -> int requires lo <= hi ensures lo <= result <= hi ensures lo <= x <= hi ==> result == x { if x < lo { lo } else { if x > hi { hi } else { x } } }"
    |> ignore

[<Fact>]
let ``a contract on the length only is underspecified (the lru_cache case)`` () =
    assertUnderspecified "fn f(xs: seq<int>) -> seq<int> ensures len(result) == len(xs) { xs }" |> ignore

[<Fact>]
let ``an upper bound over a sequence is underspecified`` () =
    assertUnderspecified
        "fn ub(xs: seq<int>) -> int requires len(xs) > 0 ensures forall i in 0..len(xs): xs[i] <= result { let mut m = xs[0]; let mut i = 1; while i < len(xs) invariant 1 <= i <= len(xs) invariant forall j in 0..i: xs[j] <= m decreases len(xs) - i { if xs[i] > m { m = xs[i]; } i = i + 1; } return m; }"
    |> ignore

let firstIndex (looseClause: string) =
    "fn find(xs: seq<int>, v: int) -> int\n"
    + "  ensures -1 <= result < len(xs)\n"
    + "  ensures result >= 0 ==> xs[result] == v\n"
    + "  ensures result == -1 ==> forall i in 0..len(xs): xs[i] != v\n"
    + looseClause
    + "{ let mut i = 0; while i < len(xs) invariant 0 <= i <= len(xs) invariant forall j in 0..i: xs[j] != v decreases len(xs) - i { if xs[i] == v { return i; } i = i + 1; } return -1; }"

[<Fact>]
let ``any matching index: underspecified without loose`` () =
    let w = assertUnderspecified (firstIndex "")
    Assert.True(w.ContainsKey "xs" && w.ContainsKey "v")

[<Fact>]
let ``any matching index: determined once the freedom is declared`` () =
    assertDetermined (firstIndex "  loose (r1, r2) => (r1 == -1) == (r2 == -1)\n")

[<Fact>]
let ``a loose relation that is too narrow is reported`` () =
    match verdict (firstIndex "  loose (r1, r2) => r1 == r2 || r1 == -1\n") with
    | Some d ->
        Assert.Equal("underspecified", d.Status)
        Assert.Contains("'loose' relation does not allow", d.Message)
    | None -> failwith "expected a violated loose relation"

[<Fact>]
let ``functions without ensures are not checked`` () =
    Assert.True((verdict "fn f(x: int) -> int { x }").IsNone)

[<Fact>]
let ``an underspecified contract is an error, an inconclusive one only a warning`` () =
    let ds = verifyAll "fn f(x: int) -> int ensures result > x { x + 1 }"
    Assert.True(ds |> List.exists (fun d -> d.Kind = "completeness" && d.Severity = Error))
