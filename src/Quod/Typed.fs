/// The typed intermediate representation produced by the type checker. Names are resolved,
/// operators are disambiguated (integer `+` vs sequence concatenation), and every place where
/// an `int` is used as a `nat` is an explicit `EToNat` node: an obligation for the verifier.
/// Verification and code generation work on this representation, never on the raw syntax.
module Quod.Typed

open Quod.Syntax

type Ty =
    | TyInt
    | TyNat
    | TyBool
    | TySeq of Ty
    /// A Unicode scalar value: not an integer, though the verifier models it by one. `string` is `seq<char>`.
    | TyChar
    | TyTuple of Ty list
    /// The type of an expression that already produced an error: absorbs further checks,
    /// so that one mistake does not cascade into many messages.
    | TyError

type ArithOp =
    | OAdd | OSub | OMul | ODiv | OMod

type CmpOp =
    | OLt | OLe | OGt | OGe

type LogicOp =
    | OAnd | OOr | OImplies | OIff

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
    | ELen of TExpr
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
      /// Called from its own module only: no public method or function is generated for it.
      IsPrivate: bool
      Span: Span }

/// The name bound to the k-th lemma call of a function (`name(args);`): no source variable can
/// have it (a dot), it is a valid SMT symbol, and the code generators skip it.
let lemmaBinding (k: int) = "lemma." + string k
let isLemmaBinding (name: string) = name.StartsWith "lemma."

type TProgram = { Fns: TFn list }

let rec tyText (t: Ty) =
    match t with
    | TyInt -> "int"
    | TyNat -> "nat"
    | TyBool -> "bool"
    | TyChar -> "char"
    | TySeq TyChar -> "string"
    | TySeq e -> "seq<" + tyText e + ">"
    | TyTuple ts -> "(" + (ts |> List.map tyText |> String.concat ", ") + ")"
    | TyError -> "<error>"

let rec ofSyntax (t: TypeExpr) =
    match t with
    | TypeExpr.TInt -> TyInt
    | TypeExpr.TNat -> TyNat
    | TypeExpr.TBool -> TyBool
    | TypeExpr.TSeq e -> TySeq(ofSyntax e)
    | TypeExpr.TChar -> TyChar
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
    | EConvert x -> mk (Syntax.Call((if e.Ty = TyChar then "char_of" else "code"), [ u x ]))
    | EBool b -> mk (Syntax.BoolLit b)
    | EVar n -> mk (Syntax.Var n)
    | EResult -> mk Syntax.Result
    | ESeq xs -> mk (Syntax.SeqLit(List.map u xs))
    | ETuple xs -> mk (Syntax.TupleLit(List.map u xs))
    | EIndex(s, i) -> mk (Syntax.Index(u s, u i))
    | ESlice(s, a, b) -> mk (Syntax.Slice(u s, Option.map u a, Option.map u b))
    | EProj(t, k) -> mk (Syntax.Proj(u t, k))
    | ELen s -> mk (Syntax.Call("len", [ u s ]))
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
