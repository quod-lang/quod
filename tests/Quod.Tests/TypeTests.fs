module Quod.Tests.TypeTests

open System.IO
open Xunit
open Quod.Syntax
open Quod.Typed
open Quod.Diagnostics

let typecheck (src: string) = Quod.Typecheck.check "test.quod" (Quod.Parser.parseProgram "test.quod" src)

let errorsOf (src: string) = snd (typecheck src) |> List.map (fun d -> d.Message)

let assertOk (src: string) =
    let errs = errorsOf src
    Assert.True(errs.IsEmpty, "unexpected errors: " + String.concat " | " errs)

let assertError (fragment: string) (src: string) =
    let errs = errorsOf src
    Assert.True(errs |> List.exists (fun m -> m.Contains fragment),
                "expected an error containing '" + fragment + "', got: " + String.concat " | " errs)

let fnOf (src: string) (name: string) = (fst (typecheck src)).Fns |> List.find (fun f -> f.Name = name)

[<Fact>]
let ``the examples type-check without errors`` () =
    let rec up (d: DirectoryInfo) =
        if Directory.Exists(Path.Combine(d.FullName, "examples")) then Path.Combine(d.FullName, "examples")
        else up d.Parent
    let dir = up (DirectoryInfo(System.AppContext.BaseDirectory))
    for f in Directory.GetFiles(dir, "*.quod") do
        let _, errs = Quod.Typecheck.check f (Quod.Parser.parseProgram f (File.ReadAllText f))
        Assert.True(errs.IsEmpty, f + ": " + String.concat " | " (errs |> List.map toText))

[<Fact>]
let ``unknown names and wrong arities`` () =
    assertError "unknown variable 'y'" "fn f(x: int) -> int { y }"
    assertError "unknown function 'g'" "fn f(x: int) -> int { g(x) }"
    assertError "takes 1 argument(s), 2 given" "fn g(a: int) -> int { a } fn f(x: int) -> int { g(x, x) }"
    assertError "is a function: call it" "fn g(a: int) -> int { a } fn f(x: int) -> int { g }"

[<Fact>]
let ``operators are checked and disambiguated`` () =
    assertError "must be an int" "fn f(b: bool) -> int { b + 1 }"
    assertError "must be a bool" "fn f(x: int) -> bool { x && true }"
    assertError "cannot be compared" "fn f(x: int, b: bool) -> bool { x == b }"
    let f = fnOf "fn f(a: seq<int>, b: seq<int>) -> seq<int> { a + b }" "f"
    match f.Body with
    | TExprBody { Kind = EConcat _ } -> ()
    | _ -> failwith "sequence + should be a concatenation"

[<Fact>]
let ``int used as nat becomes an explicit obligation`` () =
    let f = fnOf "fn f(x: int) -> nat { x }" "f"
    match f.Body with
    | TExprBody { Kind = EToNat _; Ty = TyNat } -> ()
    | _ -> failwith "expected EToNat"
    // nat is accepted as int without any obligation
    let g = fnOf "fn g(n: nat) -> int { n }" "g"
    match g.Body with
    | TExprBody { Kind = EVar "n" } -> ()
    | _ -> failwith "expected a plain variable"

[<Fact>]
let ``a variable is a nat only when declared so`` () =
    let f = fnOf "fn f(xs: seq<int>) -> int { let n = len(xs); return n; }" "f"
    match f.Body with
    | TStmtBody [ { Kind = SLet(_, "n", TyInt, _) }; _ ] -> ()
    | _ -> failwith "len() bound without annotation should be an int variable"

[<Fact>]
let ``sequences: element types, empty literal, indexing`` () =
    assertOk "fn f() -> seq<int> { [] }"
    assertError "cannot be inferred" "fn f() -> int { let e = []; return 0; }"
    assertError "do not all have the same type" "fn f() -> seq<int> { let s = [1, true]; return s; }"
    assertError "only sequences can be indexed" "fn f(x: int) -> int { x[0] }"
    assertOk "fn f(xs: seq<int>) -> seq<int> { xs[1..] + xs[..1] + [xs[0]] }"

[<Fact>]
let ``tuples and projections`` () =
    assertOk "fn f(t: (int, bool)) -> bool { t.1 }"
    assertError "components, numbered from 0" "fn f(t: (int, bool)) -> int { t.2 }"
    assertOk "fn f(x: int) -> (int, int) ensures result.0 <= result.1 { (x, x + 1) }"

[<Fact>]
let ``result only in ensures, quantifiers only in contracts`` () =
    assertError "'result' can only be used" "fn f(x: int) -> int requires result > 0 { x }"
    assertError "quantifiers can only be used" "fn f(xs: seq<int>) -> bool { forall i in 0..len(xs): xs[i] > 0 }"
    assertOk "fn f(xs: seq<int>) -> int requires forall i in 0..len(xs): xs[i] > 0 { 0 }"

[<Fact>]
let ``statement functions cannot be used in contracts`` () =
    assertError "cannot be used in a contract"
        "fn g(x: int) -> int { let y = x; return y; } fn f(x: int) -> int ensures result == g(x) { x }"
    assertOk "fn g(x: int) -> int { x + 1 } fn f(x: int) -> int ensures result == g(x) - 1 { x }"

[<Fact>]
let ``assignment needs a mutable local`` () =
    assertError "is a parameter and cannot be assigned" "fn f(x: int) -> int { x = 1; return x; }"
    assertError "declare it with 'let mut'" "fn f(x: int) -> int { let y = 0; y = 1; return y; }"
    assertOk "fn f(x: int) -> int { let mut y = 0; y = x; return y; }"

[<Fact>]
let ``no shadowing`` () =
    assertError "already declared (as a parameter)" "fn f(x: int) -> int { let x = 1; return x; }"
    assertError "already declared" "fn f(xs: seq<int>) -> bool requires forall xs in 0..1: true { true }"

[<Fact>]
let ``loops need decreases, recursion needs decreases`` () =
    assertError "needs a 'decreases' clause"
        "fn f(n: nat) -> int { let mut i = 0; while i < n { i = i + 1; } return i; }"
    assertError "is recursive" "fn f(n: nat) -> int { if n == 0 { 0 } else { f(n - 1) } }"
    assertError "is recursive"
        "fn even(n: nat) -> bool { if n == 0 { true } else { odd(n - 1) } } fn odd(n: nat) -> bool decreases n { if n == 0 { false } else { even(n - 1) } }"
    assertOk "fn f(n: nat) -> int decreases n { if n == 0 { 0 } else { f(n - 1) } }"

[<Fact>]
let ``every path returns`` () =
    assertError "not every path returns" "fn f(x: int) -> int { if x > 0 { return 1; } }"
    assertError "not every path returns"
        "fn f(n: nat) -> int { let mut i = 0; while i < n decreases n - i { return i; } }"
    assertOk "fn f(x: int) -> int { if x > 0 { return 1; } else { return 2; } }"
    assertOk "fn f(x: int) -> int { if x > 0 { return 1; } return 2; }"

[<Fact>]
let ``a value in the middle of a function is rejected`` () =
    assertError "can only end the function body"
        "fn f(n: nat) -> int { let mut i = 0; while i < n decreases n - i { i } return 0; }"

[<Fact>]
let ``loose names are bound to the result type`` () =
    assertOk "fn f(x: int) -> int ensures result >= x loose (a, b) => a >= b || b >= a { x }"
    assertError "there is no 'ensures' clause" "fn f(x: int) -> int loose (a, b) => true { x }"

[<Fact>]
let ``duplicate functions and len`` () =
    assertError "already defined" "fn f(x: int) -> int { x } fn f(y: int) -> int { y }"
    assertError "built-in" "fn len(x: int) -> int { x }"

[<Fact>]
let ``several errors are reported at once, without cascades`` () =
    let errs = errorsOf "fn f(x: int) -> int { let a = y + 1; let b = z + a; return a + b; }"
    Assert.Equal(2, errs.Length) // y and z: nothing about a, b or the return

[<Fact>]
let ``int parts of literals are accepted as nat, with a proof obligation`` () =
    assertOk "fn f(c: nat) -> (int, nat) { (1, c + 1) }"
    assertOk "fn f(c: nat) -> seq<nat> { [c, c + 1] }"
    assertOk "fn f(b: bool, c: nat) -> (int, nat) { if b { (0, c + 1) } else { (1, 1) } }"
    assertError "but (int, nat) is expected" "fn f(p: (int, int)) -> (int, nat) { p }"