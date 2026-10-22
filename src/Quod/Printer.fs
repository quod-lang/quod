/// Prints a syntax tree back as Quod source, with the fewest parentheses that keep its meaning.
/// Used for debugging (`quod parse`) and by the tests: parse(print(t)) must give t back.
module Quod.Printer

open System.Text
open Quod.Syntax

let rec typeText (t: TypeExpr) =
    match t with
    | TInt -> "int"
    | TNat -> "nat"
    | TBool -> "bool"
    | TSeq e -> "seq<" + typeText e + ">"
    | TTuple ts -> "(" + (ts |> List.map typeText |> String.concat ", ") + ")"

let private opText = function
    | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "%"
    | Eq -> "==" | Ne -> "!=" | Lt -> "<" | Le -> "<=" | Gt -> ">" | Ge -> ">="
    | And -> "&&" | Or -> "||" | Implies -> "==>" | Iff -> "<==>"

/// Binding strength, as in the parser: higher binds tighter.
let private prec = function
    | Iff -> 1 | Implies -> 2 | Or -> 3 | And -> 4
    | Eq | Ne | Lt | Le | Gt | Ge -> 5
    | Add | Sub -> 6
    | Mul | Div | Mod -> 7

let rec private exprPrec (e: Expr) =
    match e.Kind with
    | Binary(op, _, _) -> prec op
    | Unary _ -> 8
    | Quant _ | IfExpr _ -> 0
    | IntLit v when v.Sign < 0 -> 8 // printed as -v: behaves like a unary minus
    | _ -> 10

let rec exprText (e: Expr) : string =
    let wrap (min: int) (child: Expr) =
        let s = exprText child
        if exprPrec child < min then "(" + s + ")" else s
    match e.Kind with
    | IntLit v -> v.ToString()
    | BoolLit b -> if b then "true" else "false"
    | Var n -> n
    | Result -> "result"
    | SeqLit items -> "[" + (items |> List.map exprText |> String.concat ", ") + "]"
    | TupleLit items -> "(" + (items |> List.map exprText |> String.concat ", ") + ")"
    | Index(s, i) -> wrap 9 s + "[" + exprText i + "]"
    | Slice(s, lo, hi) ->
        let o = function Some x -> exprText x | None -> ""
        wrap 9 s + "[" + o lo + ".." + o hi + "]"
    | Proj(t, k) -> wrap 9 t + "." + string k
    | Call(f, args) -> f + "(" + (args |> List.map exprText |> String.concat ", ") + ")"
    | Unary(Neg, x) -> "-" + wrap 8 x
    | Unary(Not, x) -> "!" + wrap 8 x
    | Binary(op, l, r) ->
        let p = prec op
        let lmin, rmin =
            match op with
            | Implies -> p + 1, p // right-associative
            | Eq | Ne | Lt | Le | Gt | Ge -> p + 1, p + 1 // chains are printed as && of links
            | _ -> p, p + 1 // left-associative
        wrap lmin l + " " + opText op + " " + wrap rmin r
    | IfExpr(c, a, b) ->
        "if " + exprText c + " { " + exprText a + " } else { " + exprText b + " }"
    | Quant(q, v, lo, hi, body) ->
        let kw = match q with Forall -> "forall" | Exists -> "exists"
        kw + " " + v + " in " + wrap 6 lo + ".." + wrap 6 hi + ": " + exprText body

let rec private stmts (sb: StringBuilder) (indent: string) (items: Stmt list) =
    for s in items do
        sb.Append(indent) |> ignore
        match s.Kind with
        | Let(m, n, ty, v) ->
            sb.Append("let ").Append(if m then "mut " else "").Append(n) |> ignore
            match ty with
            | Some t -> sb.Append(": ").Append(typeText t) |> ignore
            | None -> ()
            sb.Append(" = ").Append(exprText v).Append(";\n") |> ignore
        | Assign(n, v) -> sb.Append(n).Append(" = ").Append(exprText v).Append(";\n") |> ignore
        | IfStmt(c, t, e) ->
            sb.Append("if ").Append(exprText c).Append(" {\n") |> ignore
            stmts sb (indent + "  ") t
            sb.Append(indent).Append("}") |> ignore
            match e with
            | Some [ { Kind = IfStmt _ } as inner ] ->
                sb.Append(" else ") |> ignore
                let nested = StringBuilder()
                stmts nested indent [ inner ]
                sb.Append(nested.ToString().TrimStart()) |> ignore
            | Some els ->
                sb.Append(" else {\n") |> ignore
                stmts sb (indent + "  ") els
                sb.Append(indent).Append("}\n") |> ignore
            | None -> sb.Append("\n") |> ignore
        | While(c, invs, dec, body) ->
            sb.Append("while ").Append(exprText c).Append("\n") |> ignore
            for i in invs do
                sb.Append(indent).Append("  invariant ").Append(exprText i).Append("\n") |> ignore
            match dec with
            | Some d -> sb.Append(indent).Append("  decreases ").Append(exprText d).Append("\n") |> ignore
            | None -> ()
            sb.Append(indent).Append("{\n") |> ignore
            stmts sb (indent + "  ") body
            sb.Append(indent).Append("}\n") |> ignore
        | Assert e -> sb.Append("assert ").Append(exprText e).Append(";\n") |> ignore
        | Return e -> sb.Append("return ").Append(exprText e).Append(";\n") |> ignore
        | FinalExpr e -> sb.Append(exprText e).Append("\n") |> ignore

let fnText (f: FnDecl) =
    let sb = StringBuilder()
    sb.Append("fn ").Append(f.Name).Append("(") |> ignore
    sb.Append(f.Params |> List.map (fun p -> p.Name + ": " + typeText p.Type) |> String.concat ", ") |> ignore
    sb.Append(") -> ").Append(typeText f.Ret).Append("\n") |> ignore
    for r in f.Requires do
        sb.Append("  requires ").Append(exprText r).Append("\n") |> ignore
    for e in f.Ensures do
        sb.Append("  ensures ").Append(exprText e).Append("\n") |> ignore
    match f.Loose with
    | Some l -> sb.Append("  loose (").Append(l.Left).Append(", ").Append(l.Right).Append(") => ").Append(exprText l.Relation).Append("\n") |> ignore
    | None -> ()
    match f.Decreases with
    | Some d -> sb.Append("  decreases ").Append(exprText d).Append("\n") |> ignore
    | None -> ()
    sb.Append("{\n") |> ignore
    match f.Body with
    | ExprBody e -> sb.Append("  ").Append(exprText e).Append("\n") |> ignore
    | StmtBody items -> stmts sb "  " items
    sb.Append("}\n") |> ignore
    sb.ToString()

let programText (p: Program) = p.Fns |> List.map fnText |> String.concat "\n"
