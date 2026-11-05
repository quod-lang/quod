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
/// A call in Quod code: the implementation in this module, the public function of another one,
/// through a name no parameter or local can shadow.
let private implName (f: string) =
    match Quod.Modules.split f with
    | Some m, g -> "_quod_m_" + m + "." + pyName g
    | None, _ -> "_quod_f_" + f

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

    /// The test that a value's `nat`s are `>= 0`, None if it has none to test. Under a sequence,
    /// only with `deep`: it costs a pass over it, like a quantified requires.
    member g.NatTest(t: Ty, term: string, deep: bool, depth: int) : string option =
        match t with
        | TyNat -> Some("(" + term + " >= 0)")
        | TySeq e when deep ->
            let x = "_quod_n" + string depth
            g.NatTest(e, x, deep, depth + 1) |> Option.map (fun inner -> "_quod_all(" + inner + " for " + x + " in " + term + ")")
        | TyTuple ts ->
            match ts |> List.mapi (fun k c -> g.NatTest(c, term + "[" + string k + "]", deep, depth)) |> List.choose id with
            | [] -> None
            | tests -> Some("(" + String.Join(" and ", tests) + ")")
        | _ -> None

    member g.Stmts(sb: StringBuilder, indent: string, items: TStmt list, f: TFn) =
        // lemma calls are proof steps: erased (a lemma may be recursive and slow, and its value is true)
        let items = items |> List.filter (fun s -> match s.Kind with SLet(_, n, _, _) -> not (isLemmaBinding n) | _ -> true)
        if items.IsEmpty then sb.Append(indent).Append("pass\n") |> ignore
        for s in items do
            g.Stmt(sb, indent, s, f)

    /// A run-time check. Not a Python `assert`, which `python -O` removes. The message names the
    /// function, the property and the values (the arguments, and the result for a
    /// postcondition): the first thing a Python developer sees of an unproved contract.
    member g.Check(sb: StringBuilder, indent: string, e: TExpr, what: string, f: TFn) =
        let literal (text: string) = "\"" + text.Replace("\\", "\\\\").Replace("\"", "\\\"") + "\""
        let values =
            (f.Params |> List.map (fun p -> p.Name, pyName p.Name))
            @ (if what = "postcondition" then [ "result", "_quod_result" ] else [])
            |> List.mapi (fun k (n, py) -> literal ((if k = 0 then "; " else ", ") + n + " = ") + " + repr(" + py + ")")
        let message =
            literal (f.Name + ": " + what + " `" + Printer.exprText (toSyntax e) + "` does not hold (not proved by quod: checked at run time)")
            :: values
        sb.Append(indent).Append("if not ").Append(g.Expr e).Append(":\n")
          .Append(indent).Append("    raise AssertionError(").Append(String.Join(" + ", message)).Append(")\n") |> ignore

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
            if checked' then for inv in invs do g.Check(sb, indent + "    ", inv, "invariant", f)
            g.Stmts(sb, indent + "    ", body, f)
            if checked' then for inv in invs do g.Check(sb, indent, inv, "invariant", f)
        | SAssert e -> if checked' then g.Check(sb, indent, e, "assertion", f)
        | SReturn e ->
            if checked' && not f.Ensures.IsEmpty then
                line ("_quod_result = " + g.Expr e)
                for ens in f.Ensures do g.Check(sb, indent, ens, "postcondition", f)
                line "return _quod_result"
            else
                line ("return " + g.Expr e)

    /// Two definitions: the public `def name`, which normalizes its arguments once and calls the
    /// implementation `_quod_f_name`, the one Quod code calls (recursion included).
    member g.Function(sb: StringBuilder, f: TFn, allRequires: bool) =
        checking <- checks.Contains f.Name
        let ps = f.Params |> List.map (fun p -> pyName p.Name + ": " + pyType p.Ty) |> String.concat ", "
        // a private function has only its implementation: code of its own module calls that
        let head = StringBuilder()
        let sb' = sb
        let sb = if f.IsPrivate then head else sb'
        sb.Append("def ").Append(pyName f.Name).Append("(").Append(ps).Append(") -> ").Append(pyType f.Ret).Append(":\n") |> ignore
        let doc = ResizeArray<string>()
        let boundary = f.Requires |> List.filter (fun r -> match r.Kind with EBool true -> false | _ -> true)
        let enforced, left = boundary |> List.partition (fun r -> allRequires || Codegen.cheap r)
        for r in enforced do doc.Add("requires " + Printer.exprText (toSyntax r) + " (checked)")
        for r in left do doc.Add("NOT CHECKED, the caller's duty: requires " + Printer.exprText (toSyntax r))
        if not allRequires then
            for p in f.Params |> List.filter (fun p -> Codegen.natInList p.Ty) do
                doc.Add("NOT CHECKED, the caller's duty: every integer of " + p.Name + " is >= 0")
        for e in f.Ensures do doc.Add("ensures " + Printer.exprText (toSyntax e))
        if not (checks.Contains f.Name) && doc.Count > 0 then doc.Add("(proved by quod)")
        elif checks.Contains f.Name then doc.Add("(NOT fully proved: contracts are checked at run time)")
        if doc.Count > 0 then
            sb.Append("    \"\"\"").Append(String.Join("\n    ", doc)).Append("\"\"\"\n") |> ignore
        // a Python caller proves nothing: what is cheap to check is checked here, not in the
        // implementation, which Quod code calls with proved arguments
        // a `nat` is a requires the proofs rely on: `n >= 0` (review of 0.1.5)
        for p in f.Params do
            match g.NatTest(p.Ty, pyName p.Name, allRequires, 0) with
            | Some test ->
                sb.Append("    if not ").Append(test).Append(":\n        raise ValueError(\"")
                  .Append(f.Name + ": argument " + p.Name + " must be >= 0").Append("\")\n") |> ignore
            | None -> ()
        for r in enforced do
            let negated = match r.Kind with ENot x -> g.Expr x | _ -> "not " + g.Expr r
            sb.Append("    if ").Append(negated).Append(":\n        raise ValueError(")
              .Append("\"" + (f.Name + ": requires " + Printer.exprText (toSyntax r)).Replace("\\", "\\\\").Replace("\"", "\\\"") + "\"").Append(")\n") |> ignore
        let args = f.Params |> List.map (fun p -> g.Normalize(p.Ty, pyName p.Name)) |> String.concat ", "
        sb.Append("    return ").Append(implName f.Name).Append("(").Append(args).Append(")\n\n\n") |> ignore
        let sb = sb'
        sb.Append("def ").Append(implName f.Name).Append("(").Append(ps).Append(") -> ").Append(pyType f.Ret).Append(":\n") |> ignore
        inPlace <-
            match f.Body with
            | TStmtBody items -> Codegen.appendable items checking
            | TExprBody _ -> Set.empty
        if checks.Contains f.Name then
            for r in f.Requires do g.Check(sb, "    ", r, "precondition", f)
        match f.Body with
        | TExprBody e ->
            g.Stmt(sb, "    ", { Kind = SReturn e; Span = e.Span }, f)
        | TStmtBody items -> g.Stmts(sb, "    ", items, f)

/// Generate the Python module. `checked` lists the functions whose proofs did not all pass
/// (built only with --runtime-checks): their contracts become run-time assertions.
let rec generate (sourceFile: string) (prog: TProgram) (checks: Set<string>) : string =
    generateWith sourceFile prog checks false

/// The same; `allRequires` also checks the quantified requires at the public boundary.
and generateWith (sourceFile: string) (prog: TProgram) (checks: Set<string>) (allRequires: bool) : string =
    let sb = StringBuilder()
    sb.Append("# Generated by quod ").Append(Quod.Diagnostics.quodVersion).Append(" from ").Append(IO.Path.GetFileName sourceFile).Append(". Do not edit.\n") |> ignore
    if checks.IsEmpty then
        sb.Append("# Every contract below was proved; none is checked at run time.\n") |> ignore
    else
        sb.Append("# WARNING: not fully proved (--runtime-checks): ").Append(String.Join(", ", checks)).Append("\n") |> ignore
    let lemmas = prog.Fns |> List.filter (fun f -> f.IsLemma) |> List.map (fun f -> f.Name)
    if not lemmas.IsEmpty then
        sb.Append("# Lemmas are proofs, not code, and are not generated: ").Append(String.Join(", ", lemmas)).Append("\n") |> ignore
    sb.Append("from __future__ import annotations\n\n") |> ignore
    for m in Codegen.calledModules prog do
        sb.Append("import ").Append(m).Append(" as _quod_m_").Append(m).Append("\n") |> ignore
    if not (Codegen.calledModules prog).IsEmpty then sb.Append("\n") |> ignore
    sb.Append(prelude) |> ignore
    let fns = prog.Fns |> List.filter (fun f -> not f.IsLemma)
    sb.Append("\n\n__all__ = [").Append(fns |> List.filter (fun f -> not f.IsPrivate) |> List.map (fun f -> "\"" + pyName f.Name + "\"") |> String.concat ", ").Append("]\n") |> ignore
    let g = Gen(checks)
    for f in fns do
        sb.Append("\n\n") |> ignore
        g.Function(sb, f, allRequires)
    sb.ToString()
