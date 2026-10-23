module Quod.Tests.StyleTests

open Xunit
open Quod.ContractStyle

/// The style of each function with ensures, by name.
let styles (src: string) : Map<string, Style> =
    let typed, errs = Quod.Typecheck.check "test.quod" (Quod.Parser.parseProgram "test.quod" src)
    Assert.True(errs.IsEmpty, "type errors: " + String.concat " | " (errs |> List.map (fun d -> d.Message)))
    let names = typed.Fns |> List.map (fun f -> f.Name) |> Set.ofList
    typed.Fns |> List.choose (fun f -> styleOf names f |> Option.map (fun s -> f.Name, s)) |> Map.ofList

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
