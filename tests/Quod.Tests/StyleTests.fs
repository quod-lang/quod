module Quod.Tests.StyleTests

open Xunit
open Quod.ContractStyle

/// The style of each function with ensures, by name.
let styles (src: string) : Map<string, Style> =
    let typed, errs = Quod.Typecheck.check "test.quod" (Quod.Parser.parseProgram "test.quod" src)
    Assert.True(errs.IsEmpty, "type errors: " + String.concat " | " (errs |> List.map (fun d -> d.Message)))
    let names = typed.Fns |> List.map (fun f -> f.Name) |> Set.ofList
    let uses = valueUses typed
    typed.Fns |> List.choose (fun f -> styleOf names uses f |> Option.map (fun s -> f.Name, s)) |> Map.ofList

[<Fact>]
let ``properties of the result`` () =
    let s = styles "fn max_of(a: int, b: int) -> int ensures result >= a && result >= b ensures result == a || result == b { if a >= b { a } else { b } }"
    Assert.Equal(Properties, s.["max_of"])

[<Fact>]
let ``an ensures that restates the body (the agent's rotate)`` () =
    let s =
        styles
            ("fn rotate(xs: seq<int>, k: int) -> seq<int>\n"
             + "  ensures len(xs) == 0 ==> result == xs\n"
             + "  ensures len(xs) > 0 ==> result == xs[len(xs) - k % len(xs)..] + xs[..len(xs) - k % len(xs)]\n"
             + "{ if len(xs) == 0 { xs } else { xs[len(xs) - k % len(xs)..] + xs[..len(xs) - k % len(xs)] } }")
    Assert.Equal(Restated, s.["rotate"])

[<Fact>]
let ``a returned value restated by a statement function`` () =
    let s = styles "fn f(x: int) -> int ensures result == x * 2 + 1 { let y = x; return y * 2 + 1; }"
    // y * 2 + 1 is not x * 2 + 1 as text: only a word-for-word restatement is reported
    Assert.Equal(Properties, s.["f"])
    let s2 = styles "fn f(x: int) -> int ensures result == x * 2 + 1 { if x > 0 { return x * 2 + 1; } return x * 2 + 1; }"
    Assert.Equal(Restated, s2.["f"])

[<Fact>]
let ``a model: the result is a function of the program`` () =
    let src =
        "fn sum(xs: seq<int>) -> int decreases len(xs) { if len(xs) == 0 { 0 } else { sum(xs[..len(xs) - 1]) + xs[len(xs) - 1] } }\n"
        + "fn total(xs: seq<int>) -> int ensures result == sum(xs) {\n"
        + "  let mut s = 0; let mut i = 0;\n"
        + "  while i < len(xs) invariant 0 <= i <= len(xs) invariant s == sum(xs[..i]) decreases len(xs) - i { s = s + xs[i]; i = i + 1; }\n"
        + "  return s; }"
    let s = styles src
    Assert.Equal(Model, s.["total"])
    Assert.False(s.ContainsKey "sum") // no ensures, no style

[<Fact>]
let ``returning the model itself is a restatement`` () =
    let s = styles "fn double(x: int) -> int { 2 * x } fn g(x: int) -> int ensures result == double(x) { double(x) }"
    Assert.Equal(Restated, s.["g"])

[<Fact>]
let ``a variable or a literal is no restatement`` () =
    let s = styles "fn id(xs: seq<int>) -> seq<int> ensures result == xs { xs }"
    Assert.Equal(Properties, s.["id"])

[<Fact>]
let ``a statement function without ensures has no contract (Haiku's rle_encode)`` () =
    let s = styles "fn f(xs: seq<int>) -> int { let mut n = 0; let mut i = 0; while i < len(xs) invariant 0 <= i <= len(xs) decreases len(xs) - i { n = n + 1; i = i + 1; } return n; }"
    Assert.Equal(NoContract, s.["f"])
    // an expression function without ensures is known by its definition: not classified
    Assert.False((styles "fn g(x: int) -> int { x + 1 }").ContainsKey "g")
[<Fact>]
let ``a statement function that always returns true is a lemma written as a function`` () =
    let s =
        styles (
            "fn sum(xs: seq<int>, i: nat, j: nat) -> int requires i <= j <= len(xs) decreases j - i { if i == j { 0 } else { sum(xs, i, j - 1) + xs[j - 1] } }\n"
            + "fn split(xs: seq<int>, i: nat, j: nat) -> bool requires i <= j <= len(xs) ensures result ensures sum(xs, 0, j) == sum(xs, 0, i) + sum(xs, i, j) decreases j - i {\n"
            + "  if i == j { return true; } let ih = split(xs, i, j - 1); return true; }\n"
            + "fn split2(xs: seq<int>, i: nat, j: nat) -> bool requires i <= j <= len(xs) ensures result ensures sum(xs, 0, j) == sum(xs, 0, i) + sum(xs, i, j) decreases j - i {\n"
            + "  if i == j { return true; } let ih = split2(xs, i, j - 1); return ih; }\n"
            + "fn nonneg(x: int) -> bool ensures result == (x >= 0) { if x >= 0 { return true; } return false; }\n")
    Assert.Equal(LemmaAsFunction, s.["split"])
    Assert.Equal(LemmaAsFunction, s.["split2"])
    Assert.Equal(Properties, s.["nonneg"])

let private reviewOf (src: string) =
    let typed, errs = Quod.Typecheck.check "test.quod" (Quod.Parser.parseProgram "test.quod" src)
    Assert.True(errs.IsEmpty)
    review "test.quod" typed

[<Fact>]
let ``every loose is noted, with its relation`` () =
    let ds = reviewOf "fn idx(xs: seq<int>) -> int requires len(xs) > 0 ensures 0 <= result < len(xs) loose (a, b) => xs[a] == xs[b] { 0 }"
    let d = ds |> List.find (fun d -> d.Kind = "loose")
    Assert.Equal(Some "idx", d.Fn)
    Assert.Contains("loose (a, b) => xs[a] == xs[b]", d.Message)

[<Fact>]
let ``the functions the contracts are stated with are listed for review, through expression functions`` () =
    let src =
        "fn sq(x: int) -> int { x * x }\n"
        + "fn sum_sq(xs: seq<int>, j: nat) -> int requires j <= len(xs) decreases j { if j == 0 { 0 } else { sum_sq(xs, j - 1) + sq(xs[j - 1]) } }\n"
        + "fn energy(xs: seq<int>) -> int ensures result == sum_sq(xs, len(xs)) { sum_sq(xs, len(xs)) }\n"
        + "fn unused(x: int) -> int { x }\n"
    let ds = reviewOf src |> List.filter (fun d -> d.Kind = "review")
    Assert.Equal<string list>([ "sq"; "sum_sq" ], ds |> List.choose (fun d -> d.Fn))
    Assert.All(ds, fun d -> Assert.Equal(Some(reviewProperty + "energy"), d.Property))

[<Fact>]
let ``a function whose value is used is not a lemma, even if it always returns true`` () =
    // the counter-review's case: rewritten as a lemma, `if feature_enabled()` would not type-check
    let s =
        styles (
            "fn feature_enabled() -> bool ensures result { return true; }\n"
            + "fn use_flag(x: int) -> int ensures result == x + 1 { if feature_enabled() { return x + 1; } return x + 1; }\n"
            + "fn flag2() -> bool ensures result { return true; }\n"
            + "fn use2(x: int) -> int ensures result == x { let b = flag2(); if b { return x; } return x; }\n"
            + "fn unused_flag() -> bool ensures result { return true; }\n"
            + "fn use3(x: int) -> int ensures result == x { let u = unused_flag(); return x; }\n")
    Assert.NotEqual(LemmaAsFunction, s.["feature_enabled"])
    Assert.NotEqual(LemmaAsFunction, s.["flag2"])
    Assert.Equal(LemmaAsFunction, s.["unused_flag"])
