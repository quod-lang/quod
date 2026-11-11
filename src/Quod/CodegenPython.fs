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

/// `__` is not in a Quod name, so this cannot be the name of something else: `class_` can be (review of 0.3).
let pyName (n: string) = if reserved.Contains n || n.StartsWith "_quod_" then n + "__q" else n

let rec private pyType (t: Ty) =
    match t with
    | TyInt | TyNat | TyI32 | TyI64 | TyError -> "int"
    | TyBool -> "bool"
    | TyChar | TySeq TyChar -> "str"
    | TyData d -> pyName (shortName d.DataName)
    | TySeq e -> "list[" + pyType e + "]"
    | TyMap(k, v) -> "dict[" + pyType k + ", " + pyType v + "]"
    | TySet e -> "frozenset[" + pyType e + "]"
    | TyTuple ts -> "tuple[" + (ts |> List.map pyType |> String.concat ", ") + "]"

/// Helpers shared by every generated module. Builtins are aliased so that a Quod function or
/// variable named `len`, `all`, `range`... can never shadow what the generated code relies on.
let private prelude =
    """_quod_len = len
_quod_type = type
_quod_string = str
_quod_repr = repr
_quod_object = object
_quod_chr = chr
_quod_ord = ord
_quod_builtin_divmod = divmod
_quod_ValueError = ValueError
_quod_IndexError = IndexError
_quod_KeyError = KeyError
_quod_set = set
_quod_dict = dict
_quod_frozenset = frozenset
_quod_TypeError = TypeError
_quod_AssertionError = AssertionError
_quod_all = all
_quod_any = any
_quod_range = range
_quod_list = list
_quod_tuple = tuple


def _quod_seq(xs):
    # A sequence argument as a list: as it is when it already is one (generated code never
    # mutates an argument, so no copy is needed), converted when it is a tuple or a range.
    return xs if _quod_type(xs) is _quod_list else _quod_list(xs)


def _quod_divmod(a: int, b: int) -> tuple[int, int]:
    # Euclidean division (as in Quod and SMT-LIB): the remainder is always >= 0.
    # Python's divmod floors, which differs when the divisor is negative.
    q, r = _quod_builtin_divmod(a, b)
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
        raise _quod_IndexError("index " + _quod_string(i) + " out of bounds (not proved: checked at run time)")
    return xs[i]


def _quod_get(m, k):
    # a key that is not there: Quod requires `k in m` (not proved: checked at run time)
    if k not in m:
        raise _quod_KeyError("key " + _quod_repr(k) + " is not in the map (not proved: checked at run time)")
    return m[k]


def _quod_slice(xs, lo: int, hi: int):
    if not 0 <= lo <= hi <= _quod_len(xs):
        raise _quod_IndexError("slice " + _quod_string(lo) + ".." + _quod_string(hi) + " out of bounds (not proved: checked at run time)")
    return xs[lo:hi]
"""

/// What a type promises, in a function checked at run time: without a proof, nothing else says it.
let private fitPrelude =
    """

def _quod_fit(v: int, lo: int, hi: int, what: str) -> int:
    if not lo <= v <= hi:
        raise _quod_AssertionError("the value " + _quod_string(v) + " does not fit in " + what + " (not proved by quod: checked at run time)")
    return v


def _quod_fit_nat(v: int) -> int:
    if v < 0:
        raise _quod_AssertionError("the value " + _quod_string(v) + " is not a nat (not proved by quod: checked at run time)")
    return v


def _quod_fit_char(v: int) -> str:
    if not 0 <= v <= 0x10FFFF or 0xD800 <= v <= 0xDFFF:
        raise _quod_AssertionError("the value " + _quod_string(v) + " is not a Unicode scalar value (not proved by quod: checked at run time)")
    return _quod_chr(v)
"""

/// What a value holds is its own: the proofs rely on it, and the list a reader gets back is that very one
/// (review of 0.3). A list everywhere else, except that it refuses to change.
let private dataPrelude =
    """

from dataclasses import dataclass as _quod_dataclass


class _quod_frozen_list(list):
    __slots__ = ()

    def _quod_refuse(self, *args, **kwargs):
        raise _quod_TypeError("a list held by a Quod value cannot change")

    __setitem__ = __delitem__ = __iadd__ = __imul__ = _quod_refuse
    append = extend = insert = pop = remove = clear = sort = reverse = _quod_refuse


def _quod_frozen(x):
    if _quod_type(x) is _quod_list:
        return _quod_frozen_list(_quod_frozen(y) for y in x)
    if _quod_type(x) is _quod_tuple:
        return _quod_tuple(_quod_frozen(y) for y in x)
    return x
"""

/// A string or a char at the public boundary: a surrogate is not a Unicode scalar value, and would
/// contradict what was proved. Only in a module whose signatures have one.
let private textPrelude =
    """

def _quod_str(s):
    if _quod_type(s) is not _quod_string:
        raise _quod_TypeError("a string is expected, not " + _quod_type(s).__name__)
    for c in s:
        if "\ud800" <= c <= "\udfff":
            raise _quod_ValueError("a lone surrogate is not a character")
    return s


def _quod_char(c):
    if _quod_type(c) is not _quod_string or _quod_len(c) != 1:
        raise _quod_TypeError("one character is expected")
    return _quod_str(c)
"""

/// A Python literal for these scalar values, the same whatever the encoding of the file.
let private pyString (scalars: int list) =
    let one (v: int) =
        match v with
        | 92 -> "\\\\"
        | 34 -> "\\\""
        | 10 -> "\\n"
        | 13 -> "\\r"
        | 9 -> "\\t"
        | _ when v < 32 || v = 127 -> "\\x" + v.ToString "x2"
        | _ when v < 127 -> string (char v)
        | _ when v <= 0xFFFF -> "\\u" + v.ToString "x4"
        | _ -> "\\U" + v.ToString "x8"
    "\"" + (scalars |> List.map one |> String.concat "") + "\""

/// The implementation of a Quod function: what Quod code calls. The public `def` only
/// normalizes its arguments, once, then calls it.
/// A call in Quod code: the implementation in this module, the public function of another one,
/// through a name no parameter or local can shadow.
let private implName (f: string) =
    match Quod.Modules.split f with
    | Some m, g -> "_quod_m_" + m + "." + pyName g
    | None, _ -> "_quod_f_" + f

/// The Python class of a case: a copy of a generic has a name of its own for each case.
let private caseClass (d: DataDecl) (k: int) =
    let case = shortName d.DataCases.[k].CaseName
    pyName (if d.Origin <> d.DataName then shortName d.DataName + "_" + case else case)

type private Gen(checks: Set<string>, local: Set<string>) =
    let mutable counter = 0
    /// Is the function being generated checked at run time (--runtime-checks)?
    let mutable checking = false
    /// Through its module if the type is not of this one, or else through an alias that no
    /// parameter or local named `Leaf` can shadow (review of 0.3).
    let qualified (d: DataDecl) (cls: string) =
        match Quod.Modules.split d.DataName with
        | Some m, _ when not (local.Contains d.DataName) -> "_quod_m_" + m + "." + cls
        | _ -> "_quod_c_" + cls
    /// What a bounded type promises, where a function checked at run time computes it.
    let fit (t: Ty) (term: string) =
        if checking && isBounded t then
            let lo, hi = (boundsOf t).Value
            "_quod_fit(" + term + ", " + lo.ToString() + ", " + hi.ToString() + ", \"" + tyText t + "\")"
        else term
    /// Locals of the function being generated that are extended in place (see appendable).
    let mutable inPlace: Set<string> = Set.empty

    member _.Fresh(prefix: string) =
        counter <- counter + 1
        "_quod_" + prefix + string counter

    member g.Expr(e: TExpr) : string =
        let go = g.Expr
        match e.Kind with
        | EInt n when e.Ty = TyChar -> pyString [ int n ]
        | EInt n -> if n.Sign < 0 then "(" + n.ToString() + ")" else n.ToString()
        | EBool b -> if b then "True" else "False"
        | EVar n -> pyName n
        | EResult -> "_quod_result"
        | ESeq xs when e.Ty = TySeq TyChar ->
            if xs |> List.forall (fun x -> match x.Kind with EInt _ -> true | _ -> false) then
                pyString (xs |> List.map (fun x -> match x.Kind with EInt n -> int n | _ -> 0))
            else "\"\".join([" + (xs |> List.map go |> String.concat ", ") + "])"
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
        | ECol(op, args) -> g.Collection(e, op, args)
        | EQuantIn(q, v, col, body) ->
            let f = match q with Syntax.Forall -> "_quod_all" | Syntax.Exists -> "_quod_any"
            f + "(" + go body + " for " + pyName v + " in " + go col + ")"
        | ECons(k, xs) ->
            match e.Ty with
            | TyData d -> qualified d (caseClass d k) + "(" + (xs |> List.map go |> String.concat ", ") + ")"
            | _ -> failwith "a value of no data type"
        | EField(a, k, i) ->
            match a.Ty with
            | TyData d -> go a + "." + pyName (fst d.DataCases.[k].Fields.[i])
            | _ -> failwith "a field of no data type"
        | EMatch(s, arms) ->
            match s.Ty with
            | TyData d ->
                let m = g.Fresh "m"
                // a Python expression has no `let`: a lambda holds the value, and each name of a case
                let arm (k: int, names: string list, body: TExpr) =
                    List.foldBack2 (fun (n: string) (field: string, _) inner ->
                        if n = "_" then inner else "(lambda " + pyName n + ": " + inner + ")(" + m + "." + pyName field + ")") names d.DataCases.[k].Fields (go body)
                let rec chain (xs: (int * string list * TExpr) list) =
                    match xs with
                    | [ x ] -> arm x
                    | ((k, _, _) as x) :: rest -> "(" + arm x + " if _quod_type(" + m + ") is " + qualified d (caseClass d k) + " else " + chain rest + ")"
                    | [] -> failwith "a match without a case"
                "(lambda " + m + ": " + chain arms + ")(" + go s + ")"
            | _ -> failwith "a match on no data type"
        | ELen s -> "_quod_len(" + go s + ")"
        | ECall(f, args) -> implName f + "(" + (args |> List.map go |> String.concat ", ") + ")"
        | ENeg x -> fit e.Ty ("(-" + go x + ")")
        | ENot x -> "(not " + go x + ")"
        | EArith(op, a, b) ->
            match op with
            | OAdd -> "(" + go a + " + " + go b + ")"
            | OSub -> "(" + go a + " - " + go b + ")"
            | OMul -> "(" + go a + " * " + go b + ")"
            | ODiv -> "_quod_div(" + go a + ", " + go b + ")"
            | OMod -> "_quod_mod(" + go a + ", " + go b + ")"
            |> fit e.Ty
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
        | EToNat x -> if checking then "_quod_fit_nat(" + go x + ")" else go x
        | EConvert x when isBounded e.Ty -> fit e.Ty (go x)
        | EConvert x when checking && e.Ty = TyChar -> "_quod_fit_char(" + go x + ")"
        | EConvert x -> (if e.Ty = TyChar then "_quod_chr(" else "_quod_ord(") + go x + ")"

    /// An operation on a map (a dict) or a set (a frozenset). Values are never changed: each operation
    /// gives a new one.
    member g.Collection(e: TExpr, op: ColOp, args: TExpr list) : string =
        let go = g.Expr
        match op, args with
        | MapOf, [ { Kind = ESeq items } ] ->
            let entries =
                items |> List.map (fun item ->
                    match item.Kind with
                    | ETuple [ k; x ] -> go k + ": " + go x
                    | _ -> "**_quod_dict([" + go item + "])")
            "{" + String.Join(", ", entries) + "}"
        | SetOf, [ { Kind = ESeq items } ] -> if items.IsEmpty then "_quod_frozenset()" else "_quod_frozenset([" + String.Join(", ", items |> List.map go) + "])"
        | Put, [ m; k; x ] -> "{**" + go m + ", " + go k + ": " + go x + "}"
        | MapRemove, [ m; k ] ->
            let key = g.Fresh "k"
            "{" + key + "_k: " + key + "_v for " + key + "_k, " + key + "_v in " + go m + ".items() if " + key + "_k != " + go k + "}"
        | SetAdd, [ s; x ] -> "(" + go s + " | _quod_frozenset([" + go x + "]))"
        | SetRemove, [ s; x ] -> "(" + go s + " - _quod_frozenset([" + go x + "]))"
        | Keys, [ m ] -> "_quod_frozenset(" + go m + ")"
        | Has, [ c; k ] -> "(" + go k + " in " + go c + ")"
        | Get, [ m; k ] -> if checking then "_quod_get(" + go m + ", " + go k + ")" else go m + "[" + go k + "]"
        | Union, [ a; b ] -> "(" + go a + " | " + go b + ")"
        | Inter, [ a; b ] -> "(" + go a + " & " + go b + ")"
        | Diff, [ a; b ] -> "(" + go a + " - " + go b + ")"
        | Subset, [ a; b ] -> "(" + go a + " <= " + go b + ")"
        | _ -> failwith "internal: an operation on a map or a set that does not fit"

    /// An argument from Python as the generated code expects it: sequences as lists, tuples as
    /// tuples. A list of numbers or booleans is taken as it is (O(1)); a sequence of tuples or of
    /// sequences is rebuilt, since its elements may come as lists or tuples (O(n), at the public
    /// boundary only: calls between Quod functions pass values already in shape).
    member g.Normalize(t: Ty, term: string) : string =
        match t with
        | TyChar -> "_quod_char(" + term + ")"
        | TySeq TyChar -> "_quod_str(" + term + ")"
        | TySeq e ->
            match g.Normalize(e, "_quod_x") with
            | "_quod_x" -> "_quod_seq(" + term + ")"
            | inner -> "[" + inner + " for _quod_x in " + term + "]"
        | TyTuple ts ->
            "(" + (ts |> List.mapi (fun k ct -> g.Normalize(ct, term + "[" + string k + "]")) |> String.concat ", ") + ")"
        | TySet e -> "_quod_frozenset(" + (match g.Normalize(e, "_quod_x") with "_quod_x" -> term | inner -> "(" + inner + " for _quod_x in " + term + ")") + ")"
        | TyMap(k, v) ->
            match g.Normalize(k, "_quod_k"), g.Normalize(v, "_quod_v") with
            | "_quod_k", "_quod_v" -> "_quod_dict(" + term + ")"
            | nk, nv -> "{" + nk + ": " + nv + " for _quod_k, _quod_v in " + term + ".items()}"
        | _ -> term

    /// The test that a value's `nat`s are `>= 0`, None if it has none to test. Under a sequence,
    /// only with `deep`: it costs a pass over it, like a quantified requires.
    member g.NatTest(t: Ty, term: string, deep: bool, depth: int) : string option =
        match t with
        | TyNat -> Some("(" + term + " >= 0)")
        // a Python int has no bounds, and the proofs rely on them
        | TyI32 | TyI64 ->
            let lo, hi = (boundsOf t).Value
            Some("(" + lo.ToString() + " <= " + term + " <= " + hi.ToString() + ")")
        | TySeq e | TySet e when deep ->
            let x = "_quod_n" + string depth
            g.NatTest(e, x, deep, depth + 1) |> Option.map (fun inner -> "_quod_all(" + inner + " for " + x + " in " + term + ")")
        | TyMap(k, v) when deep ->
            let x = "_quod_n" + string depth
            let y = "_quod_p" + string depth
            match g.NatTest(k, x, deep, depth + 1), g.NatTest(v, y, deep, depth + 1) with
            | None, None -> None
            | tk, tv ->
                let parts = [ tk; tv ] |> List.choose id
                Some("_quod_all(" + String.Join(" and ", parts) + " for " + x + ", " + y + " in " + term + ".items())")
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
            |> List.mapi (fun k (n, py) -> literal ((if k = 0 then "; " else ", ") + n + " = ") + " + _quod_repr(" + py + ")")
        let message =
            literal (f.Name + ": " + what + " `" + Printer.exprText (toSyntax e) + "` does not hold (not proved by quod: checked at run time)")
            :: values
        sb.Append(indent).Append("if not ").Append(g.Expr e).Append(":\n")
          .Append(indent).Append("    raise _quod_AssertionError(").Append(String.Join(" + ", message)).Append(")\n") |> ignore

    member g.Stmt(sb: StringBuilder, indent: string, s: TStmt, f: TFn) =
        let line (text: string) = sb.Append(indent).Append(text).Append('\n') |> ignore
        let checked' = checks.Contains f.Name
        match s.Kind with
        | SAssign(n, { Kind = EConcat({ Kind = EVar n2 }, tail); Ty = ty }) when n2 = n && inPlace.Contains n && ty <> TySeq TyChar ->
            match tail.Kind with
            | ESeq [ x ] -> line (pyName n + ".append(" + g.Expr x + ")")
            | _ -> line (pyName n + ".extend(" + g.Expr tail + ")")
        // a map or a set of its own, changed in place: a new dict or set in a loop would be quadratic
        | SAssign(n, { Kind = ECol(Put, [ { Kind = EVar n2 }; k; x ]) }) when n2 = n && inPlace.Contains n ->
            line (pyName n + "[" + g.Expr k + "] = " + g.Expr x)
        | SAssign(n, { Kind = ECol(MapRemove, [ { Kind = EVar n2 }; k ]) }) when n2 = n && inPlace.Contains n ->
            line (pyName n + ".pop(" + g.Expr k + ", None)")
        | SAssign(n, { Kind = ECol(SetAdd, [ { Kind = EVar n2 }; x ]) }) when n2 = n && inPlace.Contains n ->
            line (pyName n + ".add(" + g.Expr x + ")")
        | SAssign(n, { Kind = ECol(SetRemove, [ { Kind = EVar n2 }; x ]) }) when n2 = n && inPlace.Contains n ->
            line (pyName n + ".discard(" + g.Expr x + ")")
        | SLet(_, n, TySet _, v) | SAssign(n, v) when inPlace.Contains n && (match v.Ty with TySet _ -> true | _ -> false) ->
            line (pyName n + " = _quod_set(" + g.Expr v + ")")
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
        // a function checked at run time runs as written; and a run_by whose loop is checked would call itself
        let f = if checks.Contains f.Name || (match f.RunBy with Some g -> checks.Contains g | None -> false) then f else Codegen.tailToLoop f
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
            for p in f.Params |> List.filter (fun p -> Codegen.boundInList p.Ty) do
                doc.Add("NOT CHECKED, the caller's duty: every integer of " + p.Name + " fits its type")
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
                sb.Append("    if not ").Append(test).Append(":\n        raise _quod_ValueError(\"")
                  .Append(f.Name + ": argument " + p.Name + (if isBounded p.Ty then " must fit in " + tyText p.Ty elif Codegen.boundInList p.Ty then " is out of the bounds of its type" else " must be >= 0")).Append("\")\n") |> ignore
            | None -> ()
        for r in enforced do
            let negated = match r.Kind with ENot x -> g.Expr x | _ -> "not " + g.Expr r
            sb.Append("    if ").Append(negated).Append(":\n        raise _quod_ValueError(")
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
    let local = prog.Types |> List.map (fun d -> d.DataName) |> Set.ofList
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
    if not checks.IsEmpty then sb.Append(fitPrelude) |> ignore
    let rec hasChar (t: Ty) =
        match t with
        | TyChar -> true
        | TySeq x -> hasChar x
        | TyTuple ts -> List.exists hasChar ts
        | TyData d -> d.DataCases |> List.exists (fun c -> c.Fields |> List.exists (fun (_, ft) -> hasChar ft))
        | _ -> false
    if prog.Fns |> List.exists (fun f -> not f.IsLemma && f.Params |> List.exists (fun p -> hasChar p.Ty))
       || prog.Types |> List.exists (fun d -> hasChar (TyData d)) then
        sb.Append(textPrelude) |> ignore
    if not prog.Types.IsEmpty then
        sb.Append(dataPrelude) |> ignore
        let dataGen = Gen(checks, local)
        for d in prog.Types do
            if not d.IsStruct then
                sb.Append("\n\nclass ").Append(pyName (shortName d.DataName)).Append(":\n    pass\n") |> ignore
            for k, c in List.indexed d.DataCases do
                sb.Append("\n\n@_quod_dataclass(frozen=True)\nclass ").Append(caseClass d k)
                  .Append(if d.IsStruct then "" else "(" + pyName (shortName d.DataName) + ")").Append(":\n") |> ignore
                if c.Fields.IsEmpty then sb.Append("    pass\n") |> ignore
                for name, t in c.Fields do
                    sb.Append("    ").Append(pyName name).Append(": ").Append(pyType t).Append("\n") |> ignore
                // a Python caller proves nothing: what a field's type promises is checked when it is built
                let checks' =
                    [ for name, t in c.Fields do
                          let term = "self." + pyName name
                          // what a value holds outlives the call, and it is read through anyway: checked in depth
                          match dataGen.NatTest(t, term, true, 0) with
                          | Some test -> yield "        if not " + test + ":\n            raise _quod_ValueError(\"" + c.CaseName + ": field " + name + " is out of the bounds of its type\")\n"
                          | None -> ()
                          match t with
                          | TyChar | TySeq _ | TyTuple _ ->
                              // a copy: the caller's list must not change this value afterwards
                              let held = match t with TySeq TyChar | TyChar -> dataGen.Normalize(t, term) | _ -> "_quod_frozen(" + dataGen.Normalize(t, term) + ")"
                              yield "        _quod_object.__setattr__(self, \"" + pyName name + "\", " + held + ")\n"
                          | _ -> () ]
                if not checks'.IsEmpty then
                    sb.Append("\n    def __post_init__(self):\n") |> ignore
                    for line in checks' do sb.Append(line) |> ignore
                sb.Append("\n\n_quod_c_").Append(caseClass d k).Append(" = ").Append(caseClass d k).Append("\n") |> ignore
    let fns = prog.Fns |> List.filter (fun f -> not f.IsLemma)
    let dataNames = prog.Types |> List.collect (fun d -> (if d.IsStruct then [] else [ pyName (shortName d.DataName) ]) @ (d.DataCases |> List.mapi (fun k _ -> caseClass d k)))
    sb.Append("\n\n__all__ = [").Append((fns |> List.filter (fun f -> not f.IsPrivate) |> List.map (fun f -> "\"" + pyName f.Name + "\"")) @ (dataNames |> List.map (fun n -> "\"" + n + "\"")) |> String.concat ", ").Append("]\n") |> ignore
    let g = Gen(checks, local)
    for f in fns do
        sb.Append("\n\n") |> ignore
        g.Function(sb, f, allRequires)
    sb.ToString()
