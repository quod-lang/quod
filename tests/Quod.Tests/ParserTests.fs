module Quod.Tests.ParserTests

open System.IO
open Xunit
open Quod.Syntax
open Quod.Diagnostics
open Quod.Parser
open Quod.Printer

/// Structure of an expression, without spans, in a compact prefix form for assertions.
let rec shape (e: Expr) : string =
    match e.Kind with
    | IntLit v -> v.ToString()
    | BoolLit b -> if b then "true" else "false"
    | Var n -> n
    | Result -> "result"
    | SeqLit xs -> "[" + (xs |> List.map shape |> String.concat " ") + "]"
    | TupleLit xs -> "(tuple " + (xs |> List.map shape |> String.concat " ") + ")"
    | Index(s, i) -> "(at " + shape s + " " + shape i + ")"
    | Slice(s, lo, hi) ->
        let o = function Some x -> shape x | None -> "_"
        "(slice " + shape s + " " + o lo + " " + o hi + ")"
    | Proj(t, k) -> "(proj " + shape t + " " + string k + ")"
    | Call(f, args) -> "(" + f + (args |> List.map (fun a -> " " + shape a) |> String.concat "") + ")"
    | Unary(Neg, x) -> "(neg " + shape x + ")"
    | Unary(Not, x) -> "(not " + shape x + ")"
    | Binary(op, l, r) ->
        let o =
            match op with
            | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "%"
            | Eq -> "==" | Ne -> "!=" | Lt -> "<" | Le -> "<=" | Gt -> ">" | Ge -> ">="
            | And -> "&&" | Or -> "||" | Implies -> "==>" | Iff -> "<==>"
        "(" + o + " " + shape l + " " + shape r + ")"
    | IfExpr(c, a, b) -> "(if " + shape c + " " + shape a + " " + shape b + ")"
    | Quant(q, v, lo, hi, body) ->
        let k = match q with Forall -> "forall" | Exists -> "exists"
        "(" + k + " " + v + " " + shape lo + " " + shape hi + " " + shape body + ")"

let expr (src: string) = shape (parseExpression "test.quod" src)

/// The diagnostic raised when parsing `src` as a program.
let syntaxErrorOf (src: string) : Diagnostic =
    try
        parseProgram "test.quod" src |> ignore
        failwith "expected a syntax error"
    with QuodError d -> d

[<Fact>]
let ``arithmetic precedence and left associativity`` () =
    Assert.Equal("(+ 1 (* 2 3))", expr "1 + 2 * 3")
    Assert.Equal("(- (- a b) c)", expr "a - b - c")
    Assert.Equal("(% (* a b) c)", expr "a * b % c")

[<Fact>]
let ``logical precedence: && binds tighter than ||, ==> is right associative`` () =
    Assert.Equal("(|| a (&& b c))", expr "a || b && c")
    Assert.Equal("(==> a (==> b c))", expr "a ==> b ==> c")
    Assert.Equal("(<==> (==> a b) c)", expr "a ==> b <==> c")
    Assert.Equal("(==> (< x 0) (> y 0))", expr "x < 0 ==> y > 0")

[<Fact>]
let ``comparison chains become conjunctions`` () =
    Assert.Equal("(&& (<= 0 i) (< i n))", expr "0 <= i < n")
    Assert.Equal("(&& (&& (<= 0 a) (<= a b)) (< b n))", expr "0 <= a <= b < n")
    Assert.Equal("(&& (> a b) (>= b c))", expr "a > b >= c")

[<Fact>]
let ``a comparison chain in two directions is rejected`` () =
    let ex = Assert.Throws<QuodError>(fun () -> parseExpression "t" "a < b > c" |> ignore)
    match ex :> exn with
    | QuodError d -> Assert.Contains("one direction", d.Message)
    | _ -> ()

[<Fact>]
let ``negative literals, unary operators`` () =
    Assert.Equal("-1", expr "-1")
    Assert.Equal("(neg x)", expr "-x")
    Assert.Equal("(not (&& a b))", expr "!(a && b)")
    Assert.Equal("(- x -1)", expr "x - -1")

[<Fact>]
let ``sequences: indexing, slices, len, literals, concatenation`` () =
    Assert.Equal("(at xs (+ i 1))", expr "xs[i + 1]")
    Assert.Equal("(slice xs 1 _)", expr "xs[1..]")
    Assert.Equal("(slice xs _ n)", expr "xs[..n]")
    Assert.Equal("(slice xs a b)", expr "xs[a..b]")
    Assert.Equal("(+ [1 2] [])", expr "[1, 2] + []")
    Assert.Equal("(len xs)", expr "len(xs)")

[<Fact>]
let ``tuples and projections`` () =
    Assert.Equal("(tuple a (+ b 1))", expr "(a, b + 1)")
    Assert.Equal("(proj (proj t 1) 0)", expr "t.1.0")
    Assert.Equal("(proj result 0)", expr "result.0")

[<Fact>]
let ``quantifiers extend to the end, ranges are additive`` () =
    Assert.Equal("(forall i 0 (- (len xs) 1) (&& (<= (at xs i) (at xs (+ i 1))) true))",
                 expr "forall i in 0..len(xs) - 1: xs[i] <= xs[i + 1] && true")
    Assert.Equal("(==> (== result -1) (forall i 0 (len xs) (!= (at xs i) t)))",
                 expr "result == -1 ==> forall i in 0..len(xs): xs[i] != t")

[<Fact>]
let ``if expressions, including else if`` () =
    Assert.Equal("(if (> a b) a b)", expr "if a > b { a } else { b }")
    Assert.Equal("(if a 1 (if b 2 3))", expr "if a { 1 } else if b { 2 } else { 3 }")

[<Fact>]
let ``bodies: expression functions and statement functions`` () =
    let p =
        parseProgram "t" """
fn a(x: int) -> int { x + 1 }
fn b(x: int) -> int { if x > 0 { x } else { -x } }
fn c(x: int) -> int { let y = x + 1; return y; }
fn d(x: int) -> int { if x > 0 { return 1; } return 0; }
"""
    let kinds = p.Fns |> List.map (fun f -> match f.Body with ExprBody _ -> "expr" | StmtBody _ -> "stmt")
    Assert.Equal<string list>([ "expr"; "expr"; "stmt"; "stmt" ], kinds)

[<Fact>]
let ``contract clauses are collected in order`` () =
    let p =
        parseProgram "t" """
fn f(xs: seq<int>, k: nat) -> (int, bool)
  requires len(xs) > 0
  requires k < len(xs)
  ensures result.0 == xs[k]
  loose (r1, r2) => r1.0 == r2.0
  decreases k
{ (xs[k], true) }
"""
    let f = p.Fns.Head
    Assert.Equal(2, f.Requires.Length)
    Assert.Equal(1, f.Ensures.Length)
    Assert.Equal(TTuple [ TInt; TBool ], f.Ret)
    Assert.Equal(TSeq TInt, f.Params.Head.Type)
    Assert.Equal(TNat, f.Params.[1].Type)
    Assert.True(f.Loose.IsSome && f.Loose.Value.Left = "r1")
    Assert.True(f.Decreases.IsSome)

// --- error messages: position and advice --------------------------------------------

[<Fact>]
let ``missing return type is reported at the right place`` () =
    let d = syntaxErrorOf "fn f(x: int) { x }"
    Assert.Equal(1, d.Span.Start.Line)
    Assert.Equal(14, d.Span.Start.Col)
    Assert.Contains("'->'", d.Message)

[<Fact>]
let ``Dafny and Rust habits get a hint`` () =
    Assert.Contains("not ':='", (syntaxErrorOf "fn f(x: int) -> int { let y := x; return y; }").Message)
    Assert.Contains("len(s)", (syntaxErrorOf "fn f(xs: seq<int>) -> int { |xs| }").Message)
    Assert.Contains("'forall i in lo..hi: P'",
                    (syntaxErrorOf "fn f(xs: seq<int>) -> bool { forall i :: true }").Message)
    Assert.Contains("'fn'", (syntaxErrorOf "method f(x: int) returns (y: int) { }").Message)
    Assert.Contains("'&&'", (syntaxErrorOf "fn f(a: bool, b: bool) -> bool { a and b }").Message)

[<Fact>]
let ``an expression with a semicolon has no effect`` () =
    let d = syntaxErrorOf "fn f(x: int) -> int { x + 1; return x; }"
    Assert.Contains("no effect", d.Message)

[<Fact>]
let ``an expression in the middle of a block is rejected`` () =
    let d = syntaxErrorOf "fn f(x: int) -> int { x + 1 return x; }"
    Assert.Equal("syntax", d.Kind)

[<Fact>]
let ``at most one decreases and one loose`` () =
    Assert.Contains("at most one 'decreases'", (syntaxErrorOf "fn f(x: nat) -> int decreases x decreases x { 0 }").Message)
    Assert.Contains("at most one 'loose'",
                    (syntaxErrorOf "fn f(x: int) -> int loose (a, b) => true loose (a, b) => true { 0 }").Message)

[<Fact>]
let ``diagnostics as text and JSON`` () =
    let d = syntaxErrorOf "fn f(x: int) { x }"
    Assert.StartsWith("test.quod(1,14): error: ", toText d)
    let json = toJson [ d ]
    Assert.Contains("\"kind\": \"syntax\"", json)
    Assert.Contains("\"line\": 1", json)

// --- round trip: printing then parsing gives the same program -----------------------

let examplesDir =
    let rec up (d: DirectoryInfo) =
        if isNull d then failwith "examples folder not found"
        elif Directory.Exists(Path.Combine(d.FullName, "examples")) then Path.Combine(d.FullName, "examples")
        else up d.Parent
    up (DirectoryInfo(System.AppContext.BaseDirectory))

[<Fact>]
let ``every example prints back to a program with the same structure`` () =
    let files = Directory.GetFiles(examplesDir, "*.quod")
    Assert.NotEmpty(files)
    for f in files do
        let once = programText (parseProgram f (File.ReadAllText f))
        let twice = programText (parseProgram f once)
        Assert.Equal(once, twice)
