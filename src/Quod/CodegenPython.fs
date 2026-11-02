/// Python backend: one module per Quod file, one `def` per function, from the typed
/// representation of a *verified* program. Proved contracts produce no code. The semantics are
/// Quod's, not Python's where they differ: Euclidean division, sequences that never change.
module Quod.CodegenPython

open System
open System.Collections.Generic
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


def _quod_seq(xs):
    # A sequence argument as a list: as it is when it already is one (generated code never
    # mutates an argument, so no copy is needed), converted when it is a tuple or a range.
    return xs if type(xs) is list else _quod_list(xs)


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

/// The implementation of a Quod function: what Quod code calls. The public `def` only
/// normalizes its arguments, once, then calls it.
let private implName (f: string) = "_quod_f_" + f

/// Does this expression build a new list (so that nothing else refers to it)?
let rec private fresh (e: TExpr) =
    match e.Kind with
    | ESeq _ | EConcat _ | ESlice _ -> true
    | EIf(_, a, b) -> fresh a && fresh b
    | _ -> false

/// The mutable sequence locals that may be extended in place: `r = r + [e]` as `r.append(e)`
/// instead of a copy (quadratic in a loop). A local qualifies when it always holds a list of its
/// own: every value assigned to it is fresh, and it is never shared, that is never used as a
/// whole except in a concatenation, len, an index, a slice, a comparison, or a return. Then no
/// other variable, argument, tuple or sequence can see the list change.
let private appendable (body: TStmt list) (checkedAtRunTime: bool) : Set<string> =
    let candidates = HashSet<string>()
    let shared = HashSet<string>()
    let rec uses (whole: bool) (e: TExpr) =
        let reads = uses true
        let inner = uses false
        match e.Kind with
        | EVar n -> if not whole then shared.Add n |> ignore
        | EConcat(a, b) | EEq(a, b) -> reads a; reads b
        | ELen s -> reads s
        | EIndex(s, i) -> reads s; inner i
        | ESlice(s, lo, hi) -> reads s; Option.iter inner lo; Option.iter inner hi
        | ESeq xs | ETuple xs | ECall(_, xs) -> List.iter inner xs
        | EProj(x, _) | ENeg x | ENot x | EToNat x -> inner x
        | EArith(_, a, b) | ECmp(_, a, b) | ELogic(_, a, b) -> inner a; inner b
        | EIf(c, a, b) -> inner c; inner a; inner b
        | EQuant(_, _, lo, hi, b) -> inner lo; inner hi; inner b
        | EInt _ | EBool _ | EResult -> ()
    let rec walk (ss: TStmt list) =
        for s in ss do
            match s.Kind with
            | SLet(_, n, _, _) when isLemmaBinding n -> () // erased
            | SLet(isMut, n, ty, v) ->
                (match ty with
                 | TySeq _ when isMut && fresh v -> candidates.Add n |> ignore
                 | _ -> shared.Add n |> ignore) // another variable of that name: leave both alone
                uses false v
            | SAssign(n, v) ->
                if not (fresh v) then shared.Add n |> ignore
                uses false v
            | SIf(c, a, b) -> uses false c; walk a; walk b
            | SWhile(c, invs, _, b) ->
                uses false c
                if checkedAtRunTime then List.iter (uses false) invs
                walk b
            | SAssert e -> if checkedAtRunTime then uses false e
            | SReturn e -> uses true e
    walk body
    candidates |> Seq.filter (fun n -> not (shared.Contains n)) |> Set.ofSeq

type private Gen(checks: Set<string>) =
    let mutable counter = 0
    /// Is the function being generated checked at run time (--runtime-checks)?
    let mutable checking = false
    /// Locals of the function being generated that are extended in place (see appendable).
    let mutable inPlace: Set<string> = Set.empty

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
        | ECall(f, args) -> implName f + "(" + (args |> List.map go |> String.concat ", ") + ")"
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

    /// An argument from Python as the generated code expects it: sequences as lists, tuples as
    /// tuples. A list of numbers or booleans is taken as it is (O(1)); a sequence of tuples or of
    /// sequences is rebuilt, since its elements may come as lists or tuples (O(n), at the public
    /// boundary only: calls between Quod functions pass values already in shape).
    member g.Normalize(t: Ty, term: string) : string =
        match t with
        | TySeq e ->
            match g.Normalize(e, "_quod_x") with
            | "_quod_x" -> "_quod_seq(" + term + ")"
            | inner -> "[" + inner + " for _quod_x in " + term + "]"
        | TyTuple ts ->
            "(" + (ts |> List.mapi (fun k ct -> g.Normalize(ct, term + "[" + string k + "]")) |> String.concat ", ") + ")"
        | _ -> term

    member g.Stmts(sb: StringBuilder, indent: string, items: TStmt list, f: TFn) =
        // lemma calls are proof steps: erased (a lemma may be recursive and slow, and its value is true)
        let items = items |> List.filter (fun s -> match s.Kind with SLet(_, n, _, _) -> not (isLemmaBinding n) | _ -> true)
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
        | SAssign(n, { Kind = EConcat({ Kind = EVar n2 }, tail) }) when n2 = n && inPlace.Contains n ->
            match tail.Kind with
            | ESeq [ x ] -> line (pyName n + ".append(" + g.Expr x + ")")
            | _ -> line (pyName n + ".extend(" + g.Expr tail + ")")
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

    /// Two definitions: the public `def name`, which normalizes its arguments once and calls the
    /// implementation `_quod_f_name`, the one Quod code calls (recursion included).
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
        let args = f.Params |> List.map (fun p -> g.Normalize(p.Ty, pyName p.Name)) |> String.concat ", "
        sb.Append("    return ").Append(implName f.Name).Append("(").Append(args).Append(")\n\n\n") |> ignore
        sb.Append("def ").Append(implName f.Name).Append("(").Append(ps).Append(") -> ").Append(pyType f.Ret).Append(":\n") |> ignore
        inPlace <-
            match f.Body with
            | TStmtBody items -> appendable items checking
            | TExprBody _ -> Set.empty
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
    let lemmas = prog.Fns |> List.filter (fun f -> f.IsLemma) |> List.map (fun f -> f.Name)
    if not lemmas.IsEmpty then
        sb.Append("# Lemmas are proofs, not code, and are not generated: ").Append(String.Join(", ", lemmas)).Append("\n") |> ignore
    sb.Append("from __future__ import annotations\n\n").Append(prelude) |> ignore
    let fns = prog.Fns |> List.filter (fun f -> not f.IsLemma)
    sb.Append("\n\n__all__ = [").Append(fns |> List.map (fun f -> "\"" + pyName f.Name + "\"") |> String.concat ", ").Append("]\n") |> ignore
    let g = Gen(checks)
    for f in fns do
        sb.Append("\n\n") |> ignore
        g.Function(sb, f)
    sb.ToString()
