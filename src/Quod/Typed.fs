/// The typed intermediate representation produced by the type checker. Names are resolved,
/// operators are disambiguated (integer `+` vs sequence concatenation), and every place where
/// an `int` is used as a `nat` is an explicit `EToNat` node: an obligation for the verifier.
/// Verification and code generation work on this representation, never on the raw syntax.
module Quod.Typed

open Quod.Syntax

[<CustomEquality; NoComparison>]
type Ty =
    | TyInt
    | TyNat
    | TyBool
    | TySeq of Ty
    /// `map<K, V>` and `set<T>`: finite and immutable. Keys are of an ordered type (see `isKeyType`).
    | TyMap of Ty * Ty
    | TySet of Ty
    /// A Unicode scalar value: not an integer, though the verifier models it by one. `string` is `seq<char>`.
    | TyChar
    /// Integers that fit in 32 and 64 bits. In code, an operation that leaves the bounds is a proof
    /// obligation not met; in contracts, arithmetic is mathematical.
    | TyI32
    | TyI64
    | TyTuple of Ty list
    /// A struct or an enum, with its declaration: never recursive, so a value can be copied, and is finite.
    | TyData of DataDecl
    /// The type of an expression that already produced an error: absorbs further checks,
    /// so that one mistake does not cascade into many messages.
    | TyError

    /// Two data types are the same if their names are.
    override t.Equals(o: obj) =
        match o with
        | :? Ty as u ->
            match t, u with
            | TyInt, TyInt | TyNat, TyNat | TyBool, TyBool | TyChar, TyChar | TyI32, TyI32 | TyI64, TyI64 | TyError, TyError -> true
            | TySeq a, TySeq b -> a.Equals b
            | TyMap(k, v), TyMap(k', v') -> k.Equals k' && v.Equals v'
            | TySet a, TySet b -> a.Equals b
            | TyTuple a, TyTuple b -> a.Length = b.Length && List.forall2 (fun (x: Ty) y -> x.Equals y) a b
            | TyData a, TyData b -> a.DataName = b.DataName
            | _ -> false
        | _ -> false

    override t.GetHashCode() =
        match t with
        | TyInt -> 1 | TyNat -> 2 | TyBool -> 3 | TyChar -> 4 | TyI32 -> 5 | TyI64 -> 6 | TyError -> 7
        | TySeq a -> 31 * a.GetHashCode() + 8
        | TyMap(k, v) -> 31 * (31 * k.GetHashCode() + v.GetHashCode()) + 10
        | TySet a -> 31 * a.GetHashCode() + 11
        | TyTuple a -> a |> List.fold (fun h (x: Ty) -> 31 * h + x.GetHashCode()) 9
        | TyData d -> d.DataName.GetHashCode()

and DataDecl =
    { DataName: string
      /// The generic type this is a copy of, and for which types: `Option_int` of `Option`, [int].
      Origin: string
      TypeArgs: Ty list
      IsStruct: bool
      /// Each case with its fields; a struct has one case, named like it.
      DataCases: DataCase list }

and DataCase = { CaseName: string; Fields: (string * Ty) list }

type ArithOp =
    | OAdd | OSub | OMul | ODiv | OMod

type CmpOp =
    | OLt | OLe | OGt | OGe

type LogicOp =
    | OAnd | OOr | OImplies | OIff

/// The operations on maps and sets, each one a node of the typed tree (`ECol`).
/// MapOf: a seq of pairs; SetOf: a seq; Put: map, key, value; MapRemove: map, key; SetAdd and SetRemove:
/// set, element; Keys: map; Has: collection, key or element (`k in m`); Get: map, key (`m[k]`);
/// Union, Inter, Diff, Subset: two sets.
type ColOp =
    | MapOf | SetOf | Put | MapRemove | SetAdd | SetRemove | Keys | Has | Get | Union | Inter | Diff | Subset

type TExpr = { Kind: TExprKind; Ty: Ty; Span: Span }

and TExprKind =
    | EInt of bigint
    | EBool of bool
    /// A parameter, a local variable or a quantifier variable.
    | EVar of string
    | EResult
    | ESeq of TExpr list
    | ETuple of TExpr list
    | EIndex of TExpr * TExpr
    | ESlice of TExpr * TExpr option * TExpr option
    | EProj of TExpr * int
    /// A value of a struct or of a case of an enum (e.Ty says which), with its fields.
    | ECons of int * TExpr list
    /// A field of a struct: the value, the case and the field.
    | EField of TExpr * int * int
    /// Every case of the enum, each once: its index, a name per field ("_" for none) and the value.
    | EMatch of TExpr * (int * string list * TExpr) list
    | ELen of TExpr
    /// An operation on a map or a set.
    | ECol of ColOp * TExpr list
    /// `forall x in s: body` over the elements of a set (or of `keys(m)`).
    | EQuantIn of Quantifier * string * TExpr * TExpr
    /// A call to a user function.
    | ECall of string * TExpr list
    | ENeg of TExpr
    | ENot of TExpr
    | EArith of ArithOp * TExpr * TExpr
    | EConcat of TExpr * TExpr
    | ECmp of CmpOp * TExpr * TExpr
    /// `==` (and `!=` as ENot of EEq) on two values of the same type.
    | EEq of TExpr * TExpr
    | ELogic of LogicOp * TExpr * TExpr
    | EIf of TExpr * TExpr * TExpr
    | EQuant of Quantifier * string * TExpr * TExpr * TExpr
    /// An `int` used where a `nat` is expected: the verifier must prove it is `>= 0`.
    | EToNat of TExpr
    /// `code(c)` (Ty nat) or `char_of(n)` (Ty char, with an obligation): the same number for the solver.
    | EConvert of TExpr

type TStmt = { Kind: TStmtKind; Span: Span }

and TStmtKind =
    | SLet of isMutable: bool * name: string * ty: Ty * value: TExpr
    | SAssign of name: string * value: TExpr
    | SIf of TExpr * TStmt list * TStmt list
    | SWhile of cond: TExpr * invariants: TExpr list * decreases: TExpr * body: TStmt list
    | SAssert of TExpr
    | SReturn of TExpr

type TBody =
    | TExprBody of TExpr
    | TStmtBody of TStmt list

type TParam = { Name: string; Ty: Ty; Span: Span }

type TLoose = { Left: string; Right: string; Relation: TExpr }

type TFn =
    { Name: string
      Params: TParam list
      Ret: Ty
      Requires: TExpr list
      Ensures: TExpr list
      Loose: TLoose option
      Decreases: TExpr option
      Body: TBody
      /// Expression functions can be used in contracts; the verifier knows their definition.
      IsExprFn: bool
      /// Part of a recursive cycle (direct or mutual): needs `decreases`.
      IsRecursive: bool
      /// Identifier of that cycle (-1 when not recursive): a call to a function of the same
      /// cycle must make the `decreases` measure smaller.
      Cycle: int
      /// A lemma: a statement function returning true, checked like the others, erased from the
      /// generated code. Its calls are `SLet` of a `lemmaBinding` name.
      IsLemma: bool
      /// A statement function proved equal, which code runs instead of this definition.
      RunBy: string option
      /// Called from its own module only: no public method or function is generated for it.
      IsPrivate: bool
      Span: Span }

/// A name without its module: `m.first` is `first`.
let shortName (n: string) =
    match n.IndexOf '.' with
    | -1 -> n
    | k -> n.Substring(k + 1)

/// The bounds of a bounded integer type.
/// The keys of a map and the elements of a set are of an ordered type: the integers, `char`, `bool`
/// and `string`. An order gives a canonical value, a traversal that does not depend on the backend, and a
/// translation to C without a collector (design note maps-ensembles).
let isKeyType (t: Ty) =
    match t with
    | TyInt | TyNat | TyI32 | TyI64 | TyChar | TyBool | TyError -> true
    | TySeq TyChar -> true
    | _ -> false

let boundsOf (t: Ty) : (bigint * bigint) option =
    match t with
    | TyI32 -> Some(bigint System.Int32.MinValue, bigint System.Int32.MaxValue)
    | TyI64 -> Some(bigint System.Int64.MinValue, bigint System.Int64.MaxValue)
    | _ -> None

let isBounded (t: Ty) = (boundsOf t).IsSome

/// The name bound to the k-th lemma call of a function (`name(args);`): no source variable can
/// have it (a dot), it is a valid SMT symbol, and the code generators skip it.
let lemmaBinding (k: int) = "lemma." + string k
let isLemmaBinding (name: string) = name.StartsWith "lemma."

/// `Types`: every struct and enum, each after those it holds.
type TProgram = { Types: DataDecl list; Fns: TFn list }

let rec tyText (t: Ty) =
    match t with
    | TyInt -> "int"
    | TyNat -> "nat"
    | TyBool -> "bool"
    | TyChar -> "char"
    | TyI32 -> "i32"
    | TyI64 -> "i64"
    | TyData d -> d.DataName
    | TySeq TyChar -> "string"
    | TySeq e -> "seq<" + tyText e + ">"
    | TyMap(k, v) -> "map<" + tyText k + ", " + tyText v + ">"
    | TySet e -> "set<" + tyText e + ">"
    | TyTuple ts -> "(" + (ts |> List.map tyText |> String.concat ", ") + ")"
    | TyError -> "<error>"

let rec ofSyntax (t: TypeExpr) =
    match t with
    | TypeExpr.TInt -> TyInt
    | TypeExpr.TNat -> TyNat
    | TypeExpr.TBool -> TyBool
    | TypeExpr.TSeq e -> TySeq(ofSyntax e)
    | TypeExpr.TMap(k, v) -> TyMap(ofSyntax k, ofSyntax v)
    | TypeExpr.TSet e -> TySet(ofSyntax e)
    | TypeExpr.TChar -> TyChar
    | TypeExpr.TI32 -> TyI32
    | TypeExpr.TI64 -> TyI64
    | TypeExpr.TNamed(n, _) -> failwith ("the type checker resolves the name " + n)
    | TypeExpr.TTuple ts -> TyTuple(List.map ofSyntax ts)

/// A typed expression back as a syntax tree: to print it (docstrings), or to compare two
/// expressions by their text, whatever their positions (contract style).
let rec toSyntax (e: TExpr) : Syntax.Expr =
    let mk k : Syntax.Expr = { Kind = k; Span = e.Span }
    let u = toSyntax
    match e.Kind with
    | EInt n when e.Ty = TyChar -> mk (Syntax.CharLit(int n))
    | EInt n -> mk (Syntax.IntLit n)
    | ESeq xs when e.Ty = TySeq TyChar && xs |> List.forall (fun x -> match x.Kind with EInt _ -> true | _ -> false) ->
        mk (Syntax.StrLit(xs |> List.map (fun x -> match x.Kind with EInt n -> int n | _ -> 0)))
    | EConvert x -> mk (Syntax.Call((match e.Ty with TyChar -> "char_of" | TyI32 -> "to_i32" | TyI64 -> "to_i64" | _ -> "code"), [ u x ]))
    | EBool b -> mk (Syntax.BoolLit b)
    | EVar n -> mk (Syntax.Var n)
    | EResult -> mk Syntax.Result
    | ESeq xs -> mk (Syntax.SeqLit(List.map u xs))
    | ETuple xs -> mk (Syntax.TupleLit(List.map u xs))
    | EIndex(s, i) -> mk (Syntax.Index(u s, u i))
    | ESlice(s, a, b) -> mk (Syntax.Slice(u s, Option.map u a, Option.map u b))
    | EProj(t, k) -> mk (Syntax.Proj(u t, k))
    | ECons(k, xs) ->
        let name = (match e.Ty with TyData d -> d.DataCases.[k].CaseName | _ -> "?")
        if xs.IsEmpty then mk (Syntax.Var name) else mk (Syntax.Call(name, List.map u xs))
    | EField(a, k, i) ->
        let name = (match a.Ty with TyData d -> fst d.DataCases.[k].Fields.[i] | _ -> "?")
        mk (Syntax.Field(u a, name))
    | EMatch(s, arms) ->
        let cases = (match s.Ty with TyData d -> d.DataCases | _ -> [])
        mk (Syntax.Match(u s, arms |> List.map (fun (k, names, body) ->
            ({ Case = Some cases.[k].CaseName; Binders = names; Body = u body; ArmSpan = e.Span }: Syntax.MatchArm))))
    | ELen s -> mk (Syntax.Call("len", [ u s ]))
    | ECol(Has, [ c; k ]) -> mk (Syntax.Member(u k, u c))
    | ECol(Get, [ m; k ]) -> mk (Syntax.Index(u m, u k))
    | ECol(op, args) ->
        let name =
            match op with
            | MapOf -> "map_of" | SetOf -> "set_of" | Put -> "put" | MapRemove | SetRemove -> "remove" | SetAdd -> "add"
            | Keys -> "keys" | Union -> "union" | Inter -> "inter" | Diff -> "diff" | Subset -> "subset" | Has -> "has" | Get -> "get"
        mk (Syntax.Call(name, List.map u args))
    | EQuantIn(q, v, c, body) -> mk (Syntax.QuantIn(q, v, u c, u body))
    | ECall(f, args) -> mk (Syntax.Call(f, List.map u args))
    | ENeg x -> mk (Syntax.Unary(Syntax.Neg, u x))
    | ENot x -> mk (Syntax.Unary(Syntax.Not, u x))
    | EArith(op, a, b) ->
        let o = match op with OAdd -> Syntax.Add | OSub -> Syntax.Sub | OMul -> Syntax.Mul | ODiv -> Syntax.Div | OMod -> Syntax.Mod
        mk (Syntax.Binary(o, u a, u b))
    | EConcat(a, b) -> mk (Syntax.Binary(Syntax.Add, u a, u b))
    | ECmp(op, a, b) ->
        let o = match op with OLt -> Syntax.Lt | OLe -> Syntax.Le | OGt -> Syntax.Gt | OGe -> Syntax.Ge
        mk (Syntax.Binary(o, u a, u b))
    | EEq(a, b) -> mk (Syntax.Binary(Syntax.Eq, u a, u b))
    | ELogic(op, a, b) ->
        let o = match op with OAnd -> Syntax.And | OOr -> Syntax.Or | OImplies -> Syntax.Implies | OIff -> Syntax.Iff
        mk (Syntax.Binary(o, u a, u b))
    | EIf(c, a, b) -> mk (Syntax.IfExpr(u c, u a, u b))
    | EQuant(q, v, lo, hi, body) -> mk (Syntax.Quant(q, v, u lo, u hi, u body))
    | EToNat x -> u x
