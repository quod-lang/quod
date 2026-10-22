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
      Span: Span }

type TProgram = { Fns: TFn list }

let rec tyText (t: Ty) =
    match t with
    | TyInt -> "int"
    | TyNat -> "nat"
    | TyBool -> "bool"
    | TySeq e -> "seq<" + tyText e + ">"
    | TyTuple ts -> "(" + (ts |> List.map tyText |> String.concat ", ") + ")"
    | TyError -> "<error>"

let rec ofSyntax (t: TypeExpr) =
    match t with
    | TypeExpr.TInt -> TyInt
    | TypeExpr.TNat -> TyNat
    | TypeExpr.TBool -> TyBool
    | TypeExpr.TSeq e -> TySeq(ofSyntax e)
    | TypeExpr.TTuple ts -> TyTuple(List.map ofSyntax ts)
