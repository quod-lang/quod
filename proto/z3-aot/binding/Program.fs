// Prototype A: Z3 through the official .NET binding (Microsoft.Z3), compiled with Native AOT.
// Three checks: a valid property, a false one (counterexample), and a Quod-style completeness
// check (does a contract admit two different results?). No printf/%A: they rely on reflection.
open System
open System.Diagnostics
open Microsoft.Z3

/// Prove `goal` by asking Z3 whether its negation is satisfiable.
let prove (ctx: Context) (name: string) (goal: BoolExpr) (shown: (string * Expr) list) =
    let s = ctx.MkSolver()
    s.Assert(ctx.MkNot(goal))
    match s.Check() with
    | Status.UNSATISFIABLE -> Console.WriteLine(name + ": proved")
    | Status.SATISFIABLE ->
        let m = s.Model
        let values = shown |> List.map (fun (n, e) -> n + " = " + m.Eval(e, true).ToString())
        Console.WriteLine(name + ": refuted, counterexample " + String.Join(", ", values))
    | _ -> Console.WriteLine(name + ": unknown (" + s.ReasonUnknown + ")")

[<EntryPoint>]
let main _ =
    let clock = Stopwatch.StartNew()
    use ctx = new Context()
    let x = ctx.MkIntConst("x")
    let r1 = ctx.MkIntConst("r1")
    let r2 = ctx.MkIntConst("r2")
    let n (k: int) = ctx.MkInt(k) :> ArithExpr

    // 1. valid: x > 0 ==> x + x > x
    prove ctx "x > 0 ==> x + x > x"
        (ctx.MkImplies(ctx.MkGt(x, n 0), ctx.MkGt(ctx.MkAdd(x, x), x))) [ "x", x :> Expr ]

    // 2. false: x + 1 > 2 * x  (fails for x >= 1)
    prove ctx "x + 1 > 2 * x" (ctx.MkGt(ctx.MkAdd(x, n 1), ctx.MkMul(n 2, x))) [ "x", x :> Expr ]

    // 3. completeness of the contract  ensures r >= x && r <= x + 1:
    //    E(x, r1) && E(x, r2) ==> r1 == r2 ; a counterexample is a witness.
    let ensures (r: ArithExpr) = ctx.MkAnd(ctx.MkGe(r, x), ctx.MkLe(r, ctx.MkAdd(x, n 1)))
    prove ctx "uniqueness of (r >= x && r <= x + 1)"
        (ctx.MkImplies(ctx.MkAnd(ensures r1, ensures r2), ctx.MkEq(r1, r2)))
        [ "x", x :> Expr; "r1", r1 :> Expr; "r2", r2 :> Expr ]

    Console.WriteLine("Z3 " + Microsoft.Z3.Version.FullVersion + ", total " + string clock.ElapsedMilliseconds + " ms")
    0
