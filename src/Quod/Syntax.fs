/// The Quod 0.1 syntax tree. Every node carries its source span, so that every diagnostic
/// (syntax, type, proof, completeness) can point at the exact place it is about.
module Quod.Syntax

/// 1-based line and column.
[<Struct>]
type Pos = { Line: int; Col: int }

[<Struct>]
type Span = { Start: Pos; End: Pos }

type TypeExpr =
    | TInt
    | TNat
    | TBool
    | TSeq of TypeExpr
    | TTuple of TypeExpr list

type UnOp =
    | Neg
    | Not

type BinOp =
    | Add | Sub | Mul | Div | Mod
    | Eq | Ne | Lt | Le | Gt | Ge
    | And | Or | Implies | Iff

type Quantifier =
    | Forall
    | Exists

type Expr = { Kind: ExprKind; Span: Span }

and ExprKind =
    | IntLit of bigint
    | BoolLit of bool
    | Var of string
    /// `result`, the value returned by the function (in `ensures` only)
    | Result
    | SeqLit of Expr list
    | TupleLit of Expr list
    | Index of Expr * Expr
    /// `s[a..b]`, either bound may be omitted
    | Slice of Expr * Expr option * Expr option
    /// `t.0`
    | Proj of Expr * int
    /// `f(args)`; `len` is a built-in function called the same way
    | Call of string * Expr list
    | Unary of UnOp * Expr
    | Binary of BinOp * Expr * Expr
    | IfExpr of Expr * Expr * Expr
    /// `forall i in lo..hi: body` (lo included, hi excluded)
    | Quant of Quantifier * string * Expr * Expr * Expr

type Stmt = { Kind: StmtKind; Span: Span }

and StmtKind =
    | Let of isMutable: bool * name: string * ty: TypeExpr option * value: Expr
    | Assign of name: string * value: Expr
    /// `else if` is an `IfStmt` alone in the else branch
    | IfStmt of cond: Expr * thenBranch: Stmt list * elseBranch: Stmt list option
    | While of cond: Expr * invariants: Expr list * decreases: Expr option * body: Stmt list
    | Assert of Expr
    | Return of Expr
    /// an expression ending a block, without `;`: the value of that block
    | FinalExpr of Expr

/// A body that is a single expression makes an *expression function*, usable in contracts.
/// Anything else is a *statement function*, known to its callers by its contract only.
type Body =
    | ExprBody of Expr
    | StmtBody of Stmt list

type Param = { Name: string; Type: TypeExpr; Span: Span }

type Loose = { Left: string; Right: string; Relation: Expr }

type FnDecl =
    { Name: string
      Params: Param list
      Ret: TypeExpr
      Requires: Expr list
      Ensures: Expr list
      Loose: Loose option
      Decreases: Expr option
      Body: Body
      Span: Span }

type Program = { Fns: FnDecl list }

let spanOf (a: Pos) (b: Pos) = { Start = a; End = b }
