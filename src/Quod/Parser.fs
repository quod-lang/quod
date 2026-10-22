/// Recursive-descent parser for Quod 0.1. Stops at the first error, with a message that names
/// what was expected and, for habits carried over from Dafny or Rust, the Quod equivalent.
module Quod.Parser

open Quod.Syntax
open Quod.Lexer
open Quod.Diagnostics

/// A block holding only an expression (possibly a chain of if/else whose branches hold only an
/// expression) is an expression body; anything else is a statement body.
let private classify (items: Stmt list) : Body =
    let rec asExpr (items: Stmt list) : Expr option =
        match items with
        | [ { Kind = FinalExpr e } ] -> Some e
        | [ { Kind = IfStmt(c, t, Some e); Span = span } ] ->
            match asExpr t, asExpr e with
            | Some a, Some b -> Some { Kind = IfExpr(c, a, b); Span = span }
            | _ -> None
        | _ -> None
    match asExpr items with
    | Some e -> ExprBody e
    | None -> StmtBody items

type private Parser(file: string, toks: Token[]) =
    let mutable i = 0
    let mutable lastEnd = { Line = 1; Col = 1 }

    member _.Peek = toks.[i]
    member _.PeekAt(k: int) = toks.[min (i + k) (toks.Length - 1)]
    member _.LastEnd = lastEnd

    member _.Next() =
        let t = toks.[i]
        if i < toks.Length - 1 then i <- i + 1
        lastEnd <- t.Span.End
        t

    member p.Fail(span: Span, message: string) : 'a = raise (syntaxError file span message)

    member p.FailHere(expected: string) : 'a =
        let t = p.Peek
        p.Fail(t.Span, "expected " + expected + ", found " + describe t.Kind + p.Hint())

    /// Extra advice when the unexpected token looks like a Dafny or Rust habit.
    member p.Hint() : string =
        match p.Peek.Kind, (p.PeekAt 1).Kind with
        | TkSymbol ":", TkSymbol "=" -> " (Quod uses '=' for assignment and 'let' for declarations, not ':=')"
        | TkSymbol ":", TkSymbol ":" -> " (quantifiers are written 'forall i in lo..hi: P', not 'forall i :: P')"
        | TkIdent "method", _ | TkIdent "function", _ | TkIdent "predicate", _ -> " (every function is declared with 'fn')"
        | TkIdent "var", _ -> " (local variables are declared with 'let' or 'let mut')"
        | TkIdent "and", _ | TkIdent "or", _ | TkIdent "not", _ -> " (use '&&', '||' and '!')"
        | _ -> ""

    /// `:=` (Dafny's assignment) is lexed as ':' '=': catch it before ':' is read as a type.
    member p.RejectColonEquals() =
        if p.IsSym ":" && (p.PeekAt 1).Kind = TkSymbol "=" then
            p.Fail(p.Peek.Span, "Quod uses '=' for assignment and 'let' for declarations, not ':='")

    member p.IsSym(s: string) = (match p.Peek.Kind with TkSymbol x when x = s -> true | _ -> false)
    member p.IsKw(k: string) = (match p.Peek.Kind with TkKeyword x when x = k -> true | _ -> false)

    member p.Sym(s: string) =
        if p.IsSym s then p.Next() |> ignore else p.FailHere("'" + s + "'")

    member p.Kw(k: string) =
        if p.IsKw k then p.Next() |> ignore else p.FailHere("'" + k + "'")

    member p.Ident(what: string) : string =
        match p.Peek.Kind with
        | TkIdent n ->
            p.Next() |> ignore
            n
        | _ -> p.FailHere what

    // --- types --------------------------------------------------------------------

    member p.Type() : TypeExpr =
        match p.Peek.Kind with
        | TkKeyword "int" -> p.Next() |> ignore; TInt
        | TkKeyword "nat" -> p.Next() |> ignore; TNat
        | TkKeyword "bool" -> p.Next() |> ignore; TBool
        | TkKeyword "seq" ->
            p.Next() |> ignore
            p.Sym "<"
            let t = p.Type()
            p.Sym ">"
            TSeq t
        | TkSymbol "(" ->
            p.Next() |> ignore
            let first = p.Type()
            let rest = ResizeArray<TypeExpr>([ first ])
            while p.IsSym "," do
                p.Next() |> ignore
                rest.Add(p.Type())
            p.Sym ")"
            if rest.Count = 1 then first else TTuple(List.ofSeq rest)
        | _ -> p.FailHere "a type ('int', 'nat', 'bool', 'seq<T>' or a tuple '(T1, T2)')"

    // --- expressions --------------------------------------------------------------

    member p.Mk(kind: ExprKind, start: Pos) : Expr = { Kind = kind; Span = spanOf start p.LastEnd }

    member p.Expr() : Expr = p.Iff()

    member p.Iff() =
        let start = p.Peek.Span.Start
        let mutable left = p.Implies()
        while p.IsSym "<==>" do
            p.Next() |> ignore
            let right = p.Implies()
            left <- p.Mk(Binary(Iff, left, right), start)
        left

    /// `==>` is right-associative: a ==> b ==> c is a ==> (b ==> c).
    member p.Implies() : Expr =
        let start = p.Peek.Span.Start
        let left = p.Or()
        if p.IsSym "==>" then
            p.Next() |> ignore
            let right = p.Implies()
            p.Mk(Binary(Implies, left, right), start)
        else
            left

    member p.Or() =
        let start = p.Peek.Span.Start
        let mutable left = p.And()
        while p.IsSym "||" do
            p.Next() |> ignore
            let right = p.And()
            left <- p.Mk(Binary(Or, left, right), start)
        left

    member p.And() =
        let start = p.Peek.Span.Start
        let mutable left = p.Comparison()
        while p.IsSym "&&" do
            p.Next() |> ignore
            let right = p.Comparison()
            left <- p.Mk(Binary(And, left, right), start)
        left

    /// Comparisons can be chained in one direction, `0 <= i < n`, meaning `0 <= i && i < n`.
    member p.Comparison() : Expr =
        let start = p.Peek.Span.Start
        let first = p.Additive()
        let cmpOp () =
            match p.Peek.Kind with
            | TkSymbol "==" -> Some Eq | TkSymbol "!=" -> Some Ne
            | TkSymbol "<" -> Some Lt | TkSymbol "<=" -> Some Le
            | TkSymbol ">" -> Some Gt | TkSymbol ">=" -> Some Ge
            | _ -> None
        let links = ResizeArray<BinOp * Expr * Span>()
        let mutable go = true
        while go do
            match cmpOp () with
            | Some op ->
                let opSpan = p.Next().Span
                links.Add(op, p.Additive(), opSpan)
            | None -> go <- false
        if links.Count = 0 then
            first
        else
            let ops = links |> Seq.map (fun (o, _, _) -> o) |> List.ofSeq
            if links.Count > 1 then
                let up = ops |> List.forall (fun o -> o = Lt || o = Le)
                let down = ops |> List.forall (fun o -> o = Gt || o = Ge)
                let eqs = ops |> List.forall (fun o -> o = Eq)
                if not (up || down || eqs) then
                    let (_, _, s) = links.[1]
                    p.Fail(s, "a chain of comparisons must go in one direction ('a <= b < c' or 'a >= b > c'); split it with '&&'")
            let mutable prev = first
            let mutable acc: Expr option = None
            for (op, right, _) in links do
                let link = p.Mk(Binary(op, prev, right), prev.Span.Start)
                acc <- Some(match acc with
                            | None -> link
                            | Some a -> p.Mk(Binary(And, a, link), start))
                prev <- right
            acc.Value

    member p.Additive() =
        let start = p.Peek.Span.Start
        let mutable left = p.Multiplicative()
        let mutable go = true
        while go do
            match p.Peek.Kind with
            | TkSymbol "+" -> p.Next() |> ignore; left <- p.Mk(Binary(Add, left, p.Multiplicative()), start)
            | TkSymbol "-" -> p.Next() |> ignore; left <- p.Mk(Binary(Sub, left, p.Multiplicative()), start)
            | _ -> go <- false
        left

    member p.Multiplicative() =
        let start = p.Peek.Span.Start
        let mutable left = p.Unary()
        let mutable go = true
        while go do
            match p.Peek.Kind with
            | TkSymbol "*" -> p.Next() |> ignore; left <- p.Mk(Binary(Mul, left, p.Unary()), start)
            | TkSymbol "/" -> p.Next() |> ignore; left <- p.Mk(Binary(Div, left, p.Unary()), start)
            | TkSymbol "%" -> p.Next() |> ignore; left <- p.Mk(Binary(Mod, left, p.Unary()), start)
            | _ -> go <- false
        left

    member p.Unary() : Expr =
        let start = p.Peek.Span.Start
        match p.Peek.Kind with
        | TkSymbol "-" ->
            p.Next() |> ignore
            let e = p.Unary()
            match e.Kind with
            | IntLit v -> p.Mk(IntLit(-v), start) // fold -1 into a literal
            | _ -> p.Mk(Unary(Neg, e), start)
        | TkSymbol "!" ->
            p.Next() |> ignore
            p.Mk(Unary(Not, p.Unary()), start)
        | _ -> p.Postfix()

    member p.Postfix() : Expr =
        let start = p.Peek.Span.Start
        let mutable e = p.Primary()
        let mutable go = true
        while go do
            if p.IsSym "[" then
                p.Next() |> ignore
                if p.IsSym ".." then
                    p.Next() |> ignore
                    let hi = if p.IsSym "]" then None else Some(p.Additive())
                    p.Sym "]"
                    e <- p.Mk(Slice(e, None, hi), start)
                else
                    let idx = p.Additive()
                    if p.IsSym ".." then
                        p.Next() |> ignore
                        let hi = if p.IsSym "]" then None else Some(p.Additive())
                        p.Sym "]"
                        e <- p.Mk(Slice(e, Some idx, hi), start)
                    else
                        p.Sym "]"
                        e <- p.Mk(Index(e, idx), start)
            elif p.IsSym "." then
                p.Next() |> ignore
                match p.Peek.Kind with
                | TkInt k when k < bigint 1000 ->
                    p.Next() |> ignore
                    e <- p.Mk(Proj(e, int k), start)
                | _ -> p.FailHere "a tuple component number after '.' (as in 't.0')"
            else
                go <- false
        e

    member p.Args() : Expr list =
        p.Sym "("
        let args = ResizeArray<Expr>()
        if not (p.IsSym ")") then
            args.Add(p.Expr())
            while p.IsSym "," do
                p.Next() |> ignore
                if not (p.IsSym ")") then args.Add(p.Expr())
        p.Sym ")"
        List.ofSeq args

    member p.Primary() : Expr =
        let t = p.Peek
        let start = t.Span.Start
        match t.Kind with
        | TkInt v ->
            p.Next() |> ignore
            p.Mk(IntLit v, start)
        | TkKeyword "true" -> p.Next() |> ignore; p.Mk(BoolLit true, start)
        | TkKeyword "false" -> p.Next() |> ignore; p.Mk(BoolLit false, start)
        | TkKeyword "result" -> p.Next() |> ignore; p.Mk(Result, start)
        | TkIdent name ->
            p.Next() |> ignore
            if p.IsSym "(" then p.Mk(Call(name, p.Args()), start) else p.Mk(Var name, start)
        | TkSymbol "(" ->
            p.Next() |> ignore
            let first = p.Expr()
            if p.IsSym "," then
                let items = ResizeArray<Expr>([ first ])
                while p.IsSym "," do
                    p.Next() |> ignore
                    items.Add(p.Expr())
                p.Sym ")"
                p.Mk(TupleLit(List.ofSeq items), start)
            else
                p.Sym ")"
                first
        | TkSymbol "[" ->
            p.Next() |> ignore
            let items = ResizeArray<Expr>()
            if not (p.IsSym "]") then
                items.Add(p.Expr())
                while p.IsSym "," do
                    p.Next() |> ignore
                    if not (p.IsSym "]") then items.Add(p.Expr())
            p.Sym "]"
            p.Mk(SeqLit(List.ofSeq items), start)
        | TkKeyword "if" -> p.IfExpression()
        | TkKeyword "forall" | TkKeyword "exists" ->
            let q = if t.Kind = TkKeyword "forall" then Forall else Exists
            p.Next() |> ignore
            let v = p.Ident "a bound variable after the quantifier"
            p.Kw "in"
            let lo = p.Additive()
            p.Sym ".."
            let hi = p.Additive()
            p.Sym ":"
            let body = p.Expr()
            p.Mk(Quant(q, v, lo, hi, body), start)
        | _ -> p.FailHere "an expression"

    /// `if c { a } else { b }` in expression position: both branches are single expressions.
    member p.IfExpression() : Expr =
        let start = p.Peek.Span.Start
        p.Kw "if"
        let c = p.Expr()
        p.Sym "{"
        let a = p.Expr()
        p.Sym "}"
        if not (p.IsKw "else") then
            p.FailHere "'else': an if expression needs both branches"
        p.Next() |> ignore
        let b =
            if p.IsKw "if" then
                p.IfExpression()
            else
                p.Sym "{"
                let b = p.Expr()
                p.Sym "}"
                b
        p.Mk(IfExpr(c, a, b), start)

    // --- statements ---------------------------------------------------------------

    member p.MkS(kind: StmtKind, start: Pos) : Stmt = { Kind = kind; Span = spanOf start p.LastEnd }

    member p.Block() : Stmt list =
        p.Sym "{"
        let items = ResizeArray<Stmt>()
        while not (p.IsSym "}") do
            if p.Peek.Kind = TkEof then p.FailHere "'}'"
            let s = p.Statement()
            match s.Kind with
            | FinalExpr _ when not (p.IsSym "}") ->
                if p.Hint() <> "" then p.FailHere "an operator or '}'" // e.g. `a and b`
                p.Fail(s.Span, "an expression can only end a block; to compute a value, use 'let', or 'return' it")
            | _ -> ()
            items.Add s
        p.Sym "}"
        List.ofSeq items

    member p.Statement() : Stmt =
        let start = p.Peek.Span.Start
        match p.Peek.Kind with
        | TkKeyword "let" ->
            p.Next() |> ignore
            let isMut = p.IsKw "mut"
            if isMut then p.Next() |> ignore
            let name = p.Ident "a variable name after 'let'"
            p.RejectColonEquals()
            let ty =
                if p.IsSym ":" then
                    p.Next() |> ignore
                    Some(p.Type())
                else
                    None
            p.Sym "="
            let v = p.Expr()
            p.Sym ";"
            p.MkS(Let(isMut, name, ty, v), start)
        | TkKeyword "if" -> p.IfStatement()
        | TkKeyword "while" ->
            p.Next() |> ignore
            let c = p.Expr()
            let invs = ResizeArray<Expr>()
            let mutable dec = None
            let mutable go = true
            while go do
                if p.IsKw "invariant" then
                    p.Next() |> ignore
                    invs.Add(p.Expr())
                elif p.IsKw "decreases" then
                    let s = p.Next().Span
                    if dec.IsSome then p.Fail(s, "a loop has at most one 'decreases' clause")
                    dec <- Some(p.Expr())
                else
                    go <- false
            let body = p.Block()
            p.MkS(While(c, List.ofSeq invs, dec, body), start)
        | TkKeyword "assert" ->
            p.Next() |> ignore
            let e = p.Expr()
            p.Sym ";"
            p.MkS(Assert e, start)
        | TkKeyword "return" ->
            p.Next() |> ignore
            let e = p.Expr()
            p.Sym ";"
            p.MkS(Return e, start)
        | TkIdent _ when (p.PeekAt 1).Kind = TkSymbol ":" && (p.PeekAt 2).Kind = TkSymbol "=" ->
            p.Next() |> ignore
            p.RejectColonEquals()
            p.FailHere "'='"
        | TkIdent name when (p.PeekAt 1).Kind = TkSymbol "=" ->
            p.Next() |> ignore
            p.Next() |> ignore
            let v = p.Expr()
            p.Sym ";"
            p.MkS(Assign(name, v), start)
        | _ ->
            let e = p.Expr()
            if p.IsSym ";" then
                p.Fail(e.Span, "this expression has no effect (Quod functions are pure); 'return' it or bind it with 'let'")
            p.MkS(FinalExpr e, start)

    member p.IfStatement() : Stmt =
        let start = p.Peek.Span.Start
        p.Kw "if"
        let c = p.Expr()
        let thenB = p.Block()
        let elseB =
            if p.IsKw "else" then
                p.Next() |> ignore
                if p.IsKw "if" then Some [ p.IfStatement() ] else Some(p.Block())
            else
                None
        p.MkS(IfStmt(c, thenB, elseB), start)

    // --- functions ----------------------------------------------------------------

    member p.Function() : FnDecl =
        let start = p.Peek.Span.Start
        p.Kw "fn"
        let name = p.Ident "a function name after 'fn'"
        p.Sym "("
        let ps = ResizeArray<Param>()
        if not (p.IsSym ")") then
            let param () =
                let s = p.Peek.Span.Start
                let n = p.Ident "a parameter name"
                p.Sym ":"
                let t = p.Type()
                ps.Add { Name = n; Type = t; Span = spanOf s p.LastEnd }
            param ()
            while p.IsSym "," do
                p.Next() |> ignore
                if not (p.IsSym ")") then param ()
        p.Sym ")"
        if not (p.IsSym "->") then
            p.FailHere "'->' and a return type (Quod functions are pure, they always return a value)"
        p.Next() |> ignore
        let ret = p.Type()
        let req = ResizeArray<Expr>()
        let ens = ResizeArray<Expr>()
        let mutable loose = None
        let mutable dec = None
        let mutable go = true
        while go do
            match p.Peek.Kind with
            | TkKeyword "requires" -> p.Next() |> ignore; req.Add(p.Expr())
            | TkKeyword "ensures" -> p.Next() |> ignore; ens.Add(p.Expr())
            | TkKeyword "loose" ->
                let s = p.Next().Span
                if loose.IsSome then p.Fail(s, "a function has at most one 'loose' clause")
                p.Sym "("
                let a = p.Ident "the name of the first result, as in 'loose (r1, r2) => ...'"
                p.Sym ","
                let b = p.Ident "the name of the second result"
                p.Sym ")"
                p.Sym "=>"
                loose <- Some { Left = a; Right = b; Relation = p.Expr() }
            | TkKeyword "decreases" ->
                let s = p.Next().Span
                if dec.IsSome then p.Fail(s, "a function has at most one 'decreases' clause")
                dec <- Some(p.Expr())
            | _ -> go <- false
        if not (p.IsSym "{") then
            p.FailHere "a contract clause ('requires', 'ensures', 'loose', 'decreases') or the body '{'"
        let items = p.Block()
        { Name = name
          Params = List.ofSeq ps
          Ret = ret
          Requires = List.ofSeq req
          Ensures = List.ofSeq ens
          Loose = loose
          Decreases = dec
          Body = classify items
          Span = spanOf start p.LastEnd }

    member p.Program() : Program =
        let fns = ResizeArray<FnDecl>()
        while p.Peek.Kind <> TkEof do
            if p.IsKw "fn" then fns.Add(p.Function()) else p.FailHere "'fn'"
        { Fns = List.ofSeq fns }

/// Parse a whole file. Raises QuodError on the first syntax error.
let parseProgram (file: string) (src: string) : Program =
    let toks = tokenize file src |> Array.ofList
    Parser(file, toks).Program()

/// Parse a single expression (used by tests and, later, by tools that check one contract).
let parseExpression (file: string) (src: string) : Expr =
    let toks = tokenize file src |> Array.ofList
    let p = Parser(file, toks)
    let e = p.Expr()
    if p.Peek.Kind <> TkEof then p.FailHere "end of the expression"
    e
