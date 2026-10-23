/// Python backend: one module per Quod file, one `def` per function, from the typed
/// representation of a *verified* program. Proved contracts produce no code. The semantics are
/// Quod's, not Python's where they differ: Euclidean division, sequences copied on entry.
module Quod.CodegenPython

open System
open System.Text
open Quod.Typed

/// Python keywords and soft keywords: a Quod name equal to one of them gets a trailing '_'.
let private reserved =
    set [ "False"; "None"; "True"; "and"; "as"; "assert"; "async"; "await"; "break"; "class"
          "continue"; "def"; "del"; "elif"; "else"; "except"; "finally"; "for"; "from"; "global"
          "if"; "import"; "in"; "is"; "lambda"; "nonlocal"; "not"; "or"; "pass"; "raise"
          "return"; "try"; "while"; "with"; "yield"; "match"; "case"; "type"; "_" ]

let pyName (n: string) = if reserved.Contains n || n.StartsWith "_quod_" then n + "_" else n

let rec private pyType (t: Ty) =
    match t with
    | TyInt | TyNat | TyError -> "int"
    | TyBool -> "bool"
    | TySeq e -> "list[" + pyType e + "]"
    | TyTuple ts -> "tuple[" + (ts |> List.map pyType |> String.concat ", ") + "]"

/// Helpers shared by every generated module. Builtins are aliased so that a Quod function or
/// variable named `len`, `all`, `range`... can never shadow what the generated code relies on.
let private prelude =
    """_quod_len = len
_quod_all = all
_quod_any = any
_quod_range = range
_quod_list = list
_quod_tuple = tuple


def _quod_divmod(a: int, b: int) -> tuple[int, int]:
    # Euclidean division (as in Quod and SMT-LIB): the remainder is always >= 0.
    # Python's divmod floors, which differs when the divisor is negative.
    q, r = divmod(a, b)
    if r < 0:
        q, r = q + 1, r - b
    return q, r


def _quod_div(a: int, b: int) -> int:
    return _quod_divmod(a, b)[0]


def _quod_mod(a: int, b: int) -> int:
    return _quod_divmod(a, b)[1]


# Used only in functions built with --runtime-checks: Python would wrap a negative index and
# clamp a slice, where Quod (whose proofs did not all pass) requires the bounds.
def _quod_at(xs, i: int):
    if not 0 <= i < _quod_len(xs):
        raise IndexError("index " + str(i) + " out of bounds (not proved: checked at run time)")
    return xs[i]


def _quod_slice(xs, lo: int, hi: int):
    if not 0 <= lo <= hi <= _quod_len(xs):
        raise IndexError("slice " + str(lo) + ".." + str(hi) + " out of bounds (not proved: checked at run time)")
    return xs[lo:hi]
"""

type private Gen(checks: Set<string>) =
    let mutable counter = 0
    /// Is the function being generated checked at run time (--runtime-checks)?
    let mutable checking = false

    member _.Fresh(prefix: string) =
        counter <- counter + 1
        "_quod_" + prefix + string counter

    member g.Expr(e: TExpr) : string =
        let go = g.Expr
        match e.Kind with
        | EInt n -> if n.Sign < 0 then "(" + n.ToString() + ")" else n.ToString()
        | EBool b -> if b then "True" else "False"
        | EVar n -> pyName n
        | EResult -> "_quod_result"
        | ESeq xs -> "[" + (xs |> List.map go |> String.concat ", ") + "]"
        | ETuple xs -> "(" + (xs |> List.map go |> String.concat ", ") + ")"
        | EIndex(s, i) -> if checking then "_quod_at(" + go s + ", " + go i + ")" else go s + "[" + go i + "]"
        | ESlice(s, lo, hi) when checking ->
            let sv = go s
            "_quod_slice(" + sv + ", " + (lo |> Option.map go |> Option.defaultValue "0") + ", "
            + (hi |> Option.map go |> Option.defaultValue ("_quod_len(" + sv + ")")) + ")"
        | ESlice(s, lo, hi) ->
            go s + "[" + (lo |> Option.map go |> Option.defaultValue "") + ":" + (hi |> Option.map go |> Option.defaultValue "") + "]"
        | EProj(t, k) -> go t + "[" + string k + "]"
        | ELen s -> "_quod_len(" + go s + ")"
        | ECall(f, args) -> pyName f + "(" + (args |> List.map go |> String.concat ", ") + ")"
        | ENeg x -> "(-" + go x + ")"
        | ENot x -> "(not " + go x + ")"
        | EArith(op, a, b) ->
            match op with
            | OAdd -> "(" + go a + " + " + go b + ")"
            | OSub -> "(" + go a + " - " + go b + ")"
            | OMul -> "(" + go a + " * " + go b + ")"
            | ODiv -> "_quod_div(" + go a + ", " + go b + ")"
            | OMod -> "_quod_mod(" + go a + ", " + go b + ")"
        | EConcat(a, b) -> "(" + go a + " + " + go b + ")"
        | ECmp(op, a, b) ->
            let o = match op with OLt -> "<" | OLe -> "<=" | OGt -> ">" | OGe -> ">="
            "(" + go a + " " + o + " " + go b + ")"
        | EEq(a, b) -> "(" + go a + " == " + go b + ")"
        | ELogic(op, a, b) ->
            match op with
            | OAnd -> "(" + go a + " and " + go b + ")"
            | OOr -> "(" + go a + " or " + go b + ")"
            | OImplies -> "((not " + go a + ") or " + go b + ")"
            | OIff -> "(" + go a + " == " + go b + ")"
        | EIf(c, a, b) -> "(" + go a + " if " + go c + " else " + go b + ")"
        | EQuant(q, v, lo, hi, body) ->
            let f = match q with Syntax.Forall -> "_quod_all" | Syntax.Exists -> "_quod_any"
            f + "(" + go body + " for " + pyName v + " in _quod_range(" + go lo + ", " + go hi + "))"
        | EToNat x -> go x

    /// Copy a sequence argument into fresh lists (recursively), so that a caller passing a
    /// tuple, or mutating its list afterwards, cannot affect the function.
    member g.Copy(t: Ty, term: string) : string =
        match t with
        | TySeq e ->
            match g.Copy(e, "_quod_x") with
            | "_quod_x" -> "_quod_list(" + term + ")"
            | inner -> "[" + inner + " for _quod_x in " + term + "]"
        | TyTuple ts ->
            "(" + (ts |> List.mapi (fun k ct -> g.Copy(ct, term + "[" + string k + "]")) |> String.concat ", ") + ")"
        | _ -> term

    member g.Stmts(sb: StringBuilder, indent: string, items: TStmt list, f: TFn) =
        if items.IsEmpty then sb.Append(indent).Append("pass\n") |> ignore
        for s in items do
            g.Stmt(sb, indent, s, f)

    /// A run-time check. Not a Python `assert`, which `python -O` removes.
    member g.Check(sb: StringBuilder, indent: string, e: TExpr, what: string) =
        sb.Append(indent).Append("if not ").Append(g.Expr e).Append(":\n")
          .Append(indent).Append("    raise AssertionError(\"").Append(what).Append(" not proved: checked at run time\")\n") |> ignore

    member g.Stmt(sb: StringBuilder, indent: string, s: TStmt, f: TFn) =
        let line (text: string) = sb.Append(indent).Append(text).Append('\n') |> ignore
        let checked' = checks.Contains f.Name
        match s.Kind with
        | SLet(_, n, _, v) | SAssign(n, v) -> line (pyName n + " = " + g.Expr v)
        | SIf(c, a, b) ->
            line ("if " + g.Expr c + ":")
            g.Stmts(sb, indent + "    ", a, f)
            if not b.IsEmpty then
                line "else:"
                g.Stmts(sb, indent + "    ", b, f)
        | SWhile(c, invs, _, body) ->
            line ("while " + g.Expr c + ":")
            // invariants hold before every iteration and after the last one
            if checked' then for inv in invs do g.Check(sb, indent + "    ", inv, "invariant")
            g.Stmts(sb, indent + "    ", body, f)
            if checked' then for inv in invs do g.Check(sb, indent, inv, "invariant")
        | SAssert e -> if checked' then g.Check(sb, indent, e, "assertion")
        | SReturn e ->
            if checked' && not f.Ensures.IsEmpty then
                line ("_quod_result = " + g.Expr e)
                for ens in f.Ensures do g.Check(sb, indent, ens, "postcondition")
                line "return _quod_result"
            else
                line ("return " + g.Expr e)

    member g.Function(sb: StringBuilder, f: TFn) =
        checking <- checks.Contains f.Name
        let ps = f.Params |> List.map (fun p -> pyName p.Name + ": " + pyType p.Ty) |> String.concat ", "
        sb.Append("def ").Append(pyName f.Name).Append("(").Append(ps).Append(") -> ").Append(pyType f.Ret).Append(":\n") |> ignore
        let doc = ResizeArray<string>()
        for r in f.Requires do doc.Add("requires " + Printer.exprText (toSyntax r))
        for e in f.Ensures do doc.Add("ensures " + Printer.exprText (toSyntax e))
        if not (checks.Contains f.Name) && doc.Count > 0 then doc.Add("(proved by quod)")
        elif checks.Contains f.Name then doc.Add("(NOT fully proved: contracts are checked at run time)")
        if doc.Count > 0 then
            sb.Append("    \"\"\"").Append(String.Join("\n    ", doc)).Append("\"\"\"\n") |> ignore
        for p in f.Params do
            match p.Ty with
            | TySeq _ | TyTuple _ -> sb.Append("    ").Append(pyName p.Name).Append(" = ").Append(g.Copy(p.Ty, pyName p.Name)).Append('\n') |> ignore
            | _ -> ()
        if checks.Contains f.Name then
            for r in f.Requires do g.Check(sb, "    ", r, "precondition")
        match f.Body with
        | TExprBody e ->
            g.Stmt(sb, "    ", { Kind = SReturn e; Span = e.Span }, f)
        | TStmtBody items -> g.Stmts(sb, "    ", items, f)

/// Generate the Python module. `checked` lists the functions whose proofs did not all pass
/// (built only with --runtime-checks): their contracts become run-time assertions.
let generate (sourceFile: string) (prog: TProgram) (checks: Set<string>) : string =
    let sb = StringBuilder()
    sb.Append("# Generated by quod 0.1.0-dev from ").Append(IO.Path.GetFileName sourceFile).Append(". Do not edit.\n") |> ignore
    if checks.IsEmpty then
        sb.Append("# Every contract below was proved; none is checked at run time.\n") |> ignore
    else
        sb.Append("# WARNING: not fully proved (--runtime-checks): ").Append(String.Join(", ", checks)).Append("\n") |> ignore
    sb.Append("from __future__ import annotations\n\n").Append(prelude) |> ignore
    sb.Append("\n\n__all__ = [").Append(prog.Fns |> List.map (fun f -> "\"" + pyName f.Name + "\"") |> String.concat ", ").Append("]\n") |> ignore
    let g = Gen(checks)
    for f in prog.Fns do
        sb.Append("\n\n") |> ignore
        g.Function(sb, f)
    sb.ToString()
