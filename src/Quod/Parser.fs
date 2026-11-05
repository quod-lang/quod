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

let private varMessage =
    "Quod declares locals with 'let', and 'let mut' for one that changes: 'let mut m = xs[0];', not 'var m := xs[0];'"

let private forMessage =
    "Quod has no 'for' loop: write 'let mut i = lo; while i < hi invariant lo <= i && i <= hi decreases hi - i "
    + "{ ...; i = i + 1; }'"

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
        | TkSymbol ":", TkSymbol "=" -> " (Quod uses '=' for assignment and 'let' for declarations, not ':=': 'let x = e;', 'let mut x = e;' for a local that changes, 'x = e;' to change it)"
        | TkSymbol ":", TkSymbol ":" -> " (quantifiers are written 'forall i in lo..hi: P', not 'forall i :: P')"
        | TkIdent "method", _ | TkIdent "function", _ | TkIdent "predicate", _ -> " (every function is declared with 'fn')"
        | TkIdent "var", _ -> " (local variables are declared with 'let' or 'let mut')"
        | TkIdent "and", _ | TkIdent "or", _ | TkIdent "not", _ -> " (use '&&', '||' and '!')"
        // the habits of a model that writes Dafny (VerifBench, Qwen 2.5 Coder 14B: 13 of 18 files
        // ended on a syntax error, most of them these)
        | TkKeyword "requires", _ | TkKeyword "ensures", _ | TkKeyword "decreases", _ ->
            " (contract clauses go between the signature and the body, each without ';': "
            + "'fn f(x: int) -> int requires P ensures Q { ... }')"
        | TkKeyword "invariant", _ -> " (loop invariants go between 'while c' and the '{' of the loop, without ';')"
        | TkIdent "for", _ ->
            " (Quod has no 'for': write a 'while' loop with 'invariant' and 'decreases'; in a contract, a quantifier "
            + "'forall i in lo..hi: P', or a helper function)"
        | TkKeyword "return", _ -> " (in an ensures, the returned value is 'result')"
        | TkKeyword "result", _ -> " ('result' names the returned value, in ensures only: give the local another name, e.g. 'res')"
        | _ -> ""

    /// `:=` (Dafny's assignment) is lexed as ':' '=': catch it before ':' is read as a type.
    member p.RejectColonEquals() =
        if p.IsSym ":" && (p.PeekAt 1).Kind = TkSymbol "=" then
            p.Fail(p.Peek.Span, "Quod uses '=' for assignment and 'let' for declarations, not ':=': 'let x = e;', 'let mut x = e;' for a local that changes, 'x = e;' to change it")

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
        // words only here: an existing variable may be called `string` or `char`
        | TkIdent "char" -> p.Next() |> ignore; TChar
        | TkIdent "i32" -> p.Next() |> ignore; TI32
        | TkIdent "i64" -> p.Next() |> ignore; TI64
        | TkIdent name when name <> "string" ->
            p.Next() |> ignore
            // `module.Type`
            let name =
                match p.Peek.Kind, (p.PeekAt 1).Kind with
                | TkSymbol ".", TkIdent t ->
                    p.Next() |> ignore
                    p.Next() |> ignore
                    name + "." + t
                | _ -> name
            if p.IsSym "<" then
                p.Next() |> ignore
                let args = ResizeArray<TypeExpr>()
                args.Add(p.Type())
                while p.IsSym "," do
                    p.Next() |> ignore
                    args.Add(p.Type())
                p.Sym ">"
                TNamed(name, List.ofSeq args)
            else
                TNamed(name, [])
        | TkIdent "string" -> p.Next() |> ignore; TSeq TChar
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
                | TkIdent field ->
                    p.Next() |> ignore
                    e <- p.Mk(Field(e, field), start)
                | _ -> p.FailHere "a tuple component number or a field name after '.' (as in 't.0', 'f.name')"
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
        | TkChar v -> p.Next() |> ignore; p.Mk(CharLit v, start)
        | TkString v -> p.Next() |> ignore; p.Mk(StrLit v, start)
        | TkKeyword "true" -> p.Next() |> ignore; p.Mk(BoolLit true, start)
        | TkKeyword "false" -> p.Next() |> ignore; p.Mk(BoolLit false, start)
        | TkKeyword "result" -> p.Next() |> ignore; p.Mk(Result, start)
        | TkIdent name ->
            p.Next() |> ignore
            // `match` is a word only here: an existing variable or function may have this name
            if name = "match" && (match p.Peek.Kind with TkIdent _ | TkKeyword "result" -> true | _ -> false) then
                p.MatchExpression start
            else
            // `module.function(...)`: a projection is `.` and a number, so this cannot be one
            match p.Peek.Kind, (p.PeekAt 1).Kind, (p.PeekAt 2).Kind with
            | TkSymbol ".", TkIdent g, TkSymbol "(" ->
                p.Next() |> ignore
                p.Next() |> ignore
                p.Mk(Call(name + "." + g, p.Args()), start)
            | _ -> if p.IsSym "(" then p.Mk(Call(name, p.Args()), start) else p.Mk(Var name, start)
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
    /// `match e { Case(a, _) => x, Other => y, _ => z }`, after the word `match`.
    member p.MatchExpression(start: Pos) : Expr =
        let scrutinee = p.Expr()
        p.Sym "{"
        let arms = ResizeArray<MatchArm>()
        while not (p.IsSym "}") do
            let at = p.Peek.Span
            let name = p.Ident "a case of the enum, or '_' for the others"
            let binders =
                if p.IsSym "(" then
                    p.Next() |> ignore
                    let names = ResizeArray<string>()
                    while not (p.IsSym ")") do
                        names.Add(p.Ident "a name for this field of the case, or '_'")
                        if p.IsSym "," then p.Next() |> ignore
                    p.Sym ")"
                    List.ofSeq names
                else []
            p.Sym "=>"
            let body = p.Expr()
            arms.Add { Case = (if name = "_" then None else Some name); Binders = binders; Body = body; ArmSpan = at }
            if p.IsSym "," then p.Next() |> ignore
            elif not (p.IsSym "}") then p.FailHere "',' or '}' after a case of 'match'"
        p.Sym "}"
        p.Mk(Match(scrutinee, List.ofSeq arms), start)

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
        // `var m := e` and `for i := a to b`, as statements (review of 0.1.3: both fell on the message
        // for an expression in the middle of a block)
        | TkIdent "var" when (match (p.PeekAt 1).Kind with TkIdent _ -> true | _ -> false) ->
            p.Fail(p.Peek.Span, varMessage)
        | TkIdent "for" when (match (p.PeekAt 1).Kind with TkIdent _ -> true | _ -> false) ->
            p.Fail(p.Peek.Span, forMessage)
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
                match e.Kind with
                | Call(name, args) when name <> "len" ->
                    // a lemma call; the type checker rejects it if `name` is not a lemma
                    p.Next() |> ignore
                    p.MkS(Use(name, args), start)
                | _ -> p.Fail(e.Span, "this expression has no effect (Quod functions are pure); 'return' it or bind it with 'let'")
            else
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

    /// `fn name(params) -> type contract { body }`, or `lemma name(params) contract { steps }`.
    /// `<T, U>` after the name of a function or of a type, if there is one.
    member p.Generics() : string list =
        if p.IsSym "<" then
            p.Next() |> ignore
            let names = ResizeArray<string>()
            names.Add(p.Ident "the name of a type parameter")
            while p.IsSym "," do
                p.Next() |> ignore
                names.Add(p.Ident "the name of a type parameter")
            p.Sym ">"
            List.ofSeq names
        else []

    member p.Function() : FnDecl =
        let start = p.Peek.Span.Start
        let isLemma = p.IsKw "lemma"
        p.Next() |> ignore
        let name = p.Ident(if isLemma then "a lemma name after 'lemma'" else "a function name after 'fn'")
        let generics = p.Generics()
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
        let ret =
            if isLemma then
                if p.IsSym "->" then
                    p.Fail(p.Peek.Span, "a lemma has no result: what it proves goes in its 'ensures' clauses")
                TBool
            else
                if not (p.IsSym "->") then
                    p.FailHere "'->' and a return type (Quod functions are pure, they always return a value)"
                p.Next() |> ignore
                p.Type()
        let req = ResizeArray<Expr>()
        let ens = ResizeArray<Expr>()
        let mutable loose = None
        let mutable dec = None
        let mutable runBy = None
        let mutable go = true
        while go do
            match p.Peek.Kind with
            | TkKeyword "requires" -> p.Next() |> ignore; req.Add(p.Expr())
            | TkKeyword "ensures" -> p.Next() |> ignore; ens.Add(p.Expr())
            | TkKeyword "loose" ->
                let s = p.Next().Span
                if isLemma then p.Fail(s, "a lemma has no result, so no 'loose' clause")
                if loose.IsSome then p.Fail(s, "a function has at most one 'loose' clause")
                p.Sym "("
                let a = p.Ident "the name of the first result, as in 'loose (r1, r2) => ...'"
                p.Sym ","
                let b = p.Ident "the name of the second result"
                p.Sym ")"
                p.Sym "=>"
                loose <- Some { Left = a; Right = b; Relation = p.Expr() }
            | TkIdent "run_by" ->
                let s = p.Next().Span
                if runBy.IsSome then p.Fail(s, "a function has at most one 'run_by' clause")
                runBy <- Some(p.Ident "the name of the function that runs this one")
            | TkKeyword "decreases" ->
                let s = p.Next().Span
                if dec.IsSome then p.Fail(s, "a function has at most one 'decreases' clause")
                dec <- Some(p.Expr())
            | _ -> go <- false
        if p.IsSym ";" then
            p.Fail(p.Peek.Span, "no ';' after a contract clause: write the next clause, or the body '{', directly")
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
          Body = (if isLemma then StmtBody items else classify items)
          IsLemma = isLemma
          RunBy = runBy
          TypeParams = generics
          IsPrivate = false
          Span = spanOf start p.LastEnd }

    /// `struct Name { a: int, b: string }`, or `enum Name { A, B(int, string) }`.
    member p.TypeDeclaration() : TypeDecl =
        let start = p.Peek.Span.Start
        let isStruct = p.Peek.Kind = TkIdent "struct"
        p.Next() |> ignore
        let name = p.Ident(if isStruct then "a name after 'struct'" else "a name after 'enum'")
        let generics = p.Generics()
        p.Sym "{"
        let items = ResizeArray<string * (string * TypeExpr) list>()
        let fields = ResizeArray<string * TypeExpr>()
        while not (p.IsSym "}") do
            let n = p.Ident(if isStruct then "a field name" else "a case name")
            if isStruct then
                p.Sym ":"
                fields.Add((n, p.Type()))
            else
                let parts =
                    if p.IsSym "(" then
                        p.Next() |> ignore
                        let ts = ResizeArray<string * TypeExpr>()
                        while not (p.IsSym ")") do
                            // `Accepted(value: int)`, or `Accepted(int)`: the name is for who reads the value outside
                            let field =
                                match p.Peek.Kind, (p.PeekAt 1).Kind with
                                | TkIdent f, TkSymbol ":" ->
                                    p.Next() |> ignore
                                    p.Next() |> ignore
                                    f
                                | _ -> "f" + string ts.Count
                            ts.Add((field, p.Type()))
                            if p.IsSym "," then p.Next() |> ignore
                        p.Sym ")"
                        List.ofSeq ts
                    else []
                items.Add((n, parts))
            if p.IsSym "," then p.Next() |> ignore
            elif not (p.IsSym "}") then p.FailHere "',' or '}'"
        p.Sym "}"
        { TypeName = name
          Generics = generics
          IsStruct = isStruct
          TypeCases = (if isStruct then [ name, List.ofSeq fields ] else List.ofSeq items)
          TypeSpan = spanOf start p.LastEnd }

    member p.Program() : Program =
        let imports = ResizeArray<string * Span>()
        let fns = ResizeArray<FnDecl>()
        let types = ResizeArray<TypeDecl>()
        // `import` and `private` are words only here: an existing variable may have these names
        while p.Peek.Kind = TkIdent "import" do
            let at = p.Next().Span
            let name = p.Ident "a module name after 'import', the name of a file without '.quod'"
            imports.Add((name, at))
        while p.Peek.Kind <> TkEof do
            if p.Peek.Kind = TkIdent "private" && (match (p.PeekAt 1).Kind with TkKeyword "fn" | TkKeyword "lemma" -> true | _ -> false) then
                p.Next() |> ignore
                fns.Add({ p.Function() with IsPrivate = true })
            elif (p.Peek.Kind = TkIdent "struct" || p.Peek.Kind = TkIdent "enum") && (match (p.PeekAt 1).Kind with TkIdent _ -> true | _ -> false) then
                types.Add(p.TypeDeclaration())
            elif p.IsKw "fn" || p.IsKw "lemma" then fns.Add(p.Function())
            elif p.Peek.Kind = TkIdent "import" then p.Fail(p.Peek.Span, "an 'import' goes at the top of the file, before any function")
            else p.FailHere "'fn' or 'lemma'"
        { Imports = List.ofSeq imports; Types = List.ofSeq types; Fns = List.ofSeq fns }

/// Parse a whole file. Raises QuodError on the first syntax error.
let parseProgram (file: string) (src: string) : Program =
    let toks = tokenize file src |> Array.ofList
    Parser(file, toks).Program()

/// The habits of a writer of Dafny that a regular expression recognises in the source, everywhere in
/// the file. The parser stops at its first error; when it does, these are reported with it, so that
/// a model that brought several habits learns of them all in one answer (review of 0.1.3: eight
/// calls to fix a function of twelve lines, one error each). Only used on a file that does not
/// parse, so a false positive cannot reject a program.
let habits (file: string) (src: string) : Diagnostic list =
    let rx (pattern: string) = System.Text.RegularExpressions.Regex(pattern)
    let clause = rx @"^\s*(requires|ensures|decreases|invariant|loose)\b"
    let checks =
        [ rx @"(?<![|])\|(?![|\s])[^|\n]*[^|\s]\|(?![|])", "the length of a sequence is written len(s), not |s|"
          rx @"(?<!\bvar\s+\w+\s*)(?<!\bfor\s+\w+\s*):=", "Quod uses '=' for assignment and 'let' for declarations, not ':='"
          rx @"^\s*ensures\b.*\breturn\b", "in an ensures, the returned value is 'result'"
          rx @"\bforall\s+\w+(\s*:\s*\w+)?\s*::|\bexists\s+\w+(\s*:\s*\w+)?\s*::", "quantifiers are written 'forall i in lo..hi: P', not 'forall i :: P'"
          rx @"\bvar\s+\w+", varMessage
          rx @"\bfor\s+\w+\s*(:=|in\b)", forMessage
          rx @"^\s*(method|function|predicate)\s+\w+", "every function is declared with 'fn'"
          rx @"\blet\s+(mut\s+)?result\b", "'result' names the returned value, in ensures only: give the local another name, e.g. 'res'"
          rx @"\breturns\s*\(", "the result type follows '->': 'fn f(x: int) -> int', and the ensures call it 'result'" ]
    let lines = src.Replace("\r\n", "\n").Split('\n')
    let found = ResizeArray<Diagnostic>()
    let add (line: int) (col: int) (len: int) (message: string) =
        let sp = spanOf { Line = line; Col = col } { Line = line; Col = col + len }
        found.Add { File = file; Span = sp; Kind = "syntax"; Status = "error"; Severity = Error; Fn = None
                    Property = None; Counterexample = []; Reason = None; Evidence = None; Message = message }
    let mutable depth = 0 // of braces, to tell a contract clause in a body
    let mutable whileOpen = false // between `while` and its `{`, where invariants belong
    lines
    |> Array.iteri (fun k raw ->
        let text = match raw.IndexOf "//" with -1 -> raw | j -> raw.Substring(0, j)
        let line = k + 1
        for r, message in checks do
            for m in r.Matches text do
                add line (m.Index + 1) m.Length message
        let c = clause.Match text
        if c.Success then
            let word = c.Groups.[1].Value
            if depth > 0 && not (word = "invariant" || word = "decreases") then
                add line (c.Groups.[1].Index + 1) word.Length
                    "contract clauses go between the signature and the body, each without ';': 'fn f(x: int) -> int requires P ensures Q { ... }'"
            elif depth > 0 && not whileOpen then
                add line (c.Groups.[1].Index + 1) word.Length "loop invariants go between 'while c' and the '{' of the loop, without ';'"
            let t = text.TrimEnd()
            if t.EndsWith ";" then add line t.Length 1 "no ';' after a contract clause: write the next clause, or the body '{', directly"
        if (rx @"\b(while|for)\b").IsMatch text then whileOpen <- true
        for ch in text do
            if ch = '{' then
                depth <- depth + 1
                whileOpen <- false
            elif ch = '}' then depth <- max 0 (depth - 1))
    found |> Seq.sortBy (fun d -> d.Span.Start.Line, d.Span.Start.Col) |> List.ofSeq

/// The syntax error that stopped the parser, followed by the habits found elsewhere in the file.
let syntaxDiagnostics (file: string) (src: string) (first: Diagnostic) : Diagnostic list =
    let same (h: Diagnostic) = h.Span.Start.Line = first.Span.Start.Line && first.Message.Contains h.Message
    first :: (habits file src |> List.filter (fun h -> not (same h)))

/// Parse a single expression (used by tests and, later, by tools that check one contract).
let parseExpression (file: string) (src: string) : Expr =
    let toks = tokenize file src |> Array.ofList
    let p = Parser(file, toks)
    let e = p.Expr()
    if p.Peek.Kind <> TkEof then p.FailHere "end of the expression"
    e
