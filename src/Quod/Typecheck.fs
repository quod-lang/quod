/// Type checker for Quod 0.1: resolves names, checks types and the language rules, and builds
/// the typed representation (Typed.fs). Reports every error it finds, not just the first; an
/// expression that failed gets type TyError, which silences checks that depend on it.
module Quod.Typecheck

open System.Collections.Generic
open Quod.Syntax
open Quod.Typed
open Quod.Diagnostics

type private Binding =
    { Ty: Ty
      IsMutable: bool
      /// "parameter", "local", "bound variable", "result name": used in messages
      What: string }

/// Where an expression is checked: code, or a contract/assertion (specification).
type private Ctx =
    { InSpec: bool
      /// Some type inside `ensures`, where `result` is allowed
      ResultTy: Ty option
      FnName: string }

/// Do these statements return on every path? A loop does not count: it may run zero times.
let rec private alwaysReturns (stmts: TStmt list) : bool =
    stmts |> List.exists (fun s ->
        match s.Kind with
        | SReturn _ -> true
        | SIf(_, t, e) -> alwaysReturns t && alwaysReturns e
        | _ -> false)

type private Checker(file: string, fns: Map<string, FnDecl>) =
    let errors = ResizeArray<Diagnostic>()
    let scopes = Stack<Dictionary<string, Binding>>()

    member _.Errors = List.ofSeq errors

    member _.Error(span: Span, fn: string, message: string) =
        errors.Add
            { File = file; Span = span; Kind = "type"; Status = "error"; Severity = Error
              Fn = (if fn = "" then None else Some fn); Property = None; Message = message }

    // --- scopes -------------------------------------------------------------------

    member _.Push() = scopes.Push(Dictionary())
    member _.Pop() = scopes.Pop() |> ignore

    member _.Lookup(name: string) : Binding option =
        scopes |> Seq.tryPick (fun s -> match s.TryGetValue name with | true, b -> Some b | _ -> None)

    member c.Declare(name: string, b: Binding, span: Span, fn: string) =
        match c.Lookup name with
        | Some prev ->
            c.Error(span, fn, "'" + name + "' is already declared (as a " + prev.What + "); Quod does not allow shadowing, choose another name")
        | None -> ()
        scopes.Peek().[name] <- b

    // --- type relations -------------------------------------------------------------

    /// The common type of two branches or elements: equal types, or int when nat meets int.
    member c.Join(a: Ty, b: Ty) : Ty option =
        match a, b with
        | TyError, t | t, TyError -> Some t
        | x, y when x = y -> Some x
        | (TyNat | TyInt), (TyNat | TyInt) -> Some TyInt
        | TySeq x, TySeq y -> c.Join(x, y) |> Option.map TySeq
        | TyTuple xs, TyTuple ys when xs.Length = ys.Length ->
            let parts = List.map2 (fun x y -> c.Join(x, y)) xs ys
            if parts |> List.forall Option.isSome then Some(TyTuple(parts |> List.map Option.get)) else None
        | _ -> None

    /// Use `e` where `expected` is required: nat is accepted as int (and seq<nat> as seq<int>);
    /// int as nat becomes an EToNat node, a proof obligation. Anything else is an error.
    member c.Coerce(e: TExpr, expected: Ty, fn: string, what: string) : TExpr =
        let rec fits (actual: Ty) (exp: Ty) =
            match actual, exp with
            | TyError, _ | _, TyError -> true
            | x, y when x = y -> true
            | TyNat, TyInt -> true
            | TySeq x, TySeq y -> fits x y
            | TyTuple xs, TyTuple ys when xs.Length = ys.Length -> List.forall2 fits xs ys
            | _ -> false
        if fits e.Ty expected then e
        elif e.Ty = TyInt && expected = TyNat then { Kind = EToNat e; Ty = TyNat; Span = e.Span }
        else
            c.Error(e.Span, fn, what + " has type " + tyText e.Ty + ", but " + tyText expected + " is expected")
            { e with Ty = TyError }

    member c.ExpectBool(e: TExpr, ctx: Ctx, what: string) =
        if e.Ty <> TyBool && e.Ty <> TyError then
            c.Error(e.Span, ctx.FnName, what + " must be a bool, not " + tyText e.Ty)

    member c.ExpectInt(e: TExpr, ctx: Ctx, what: string) =
        match e.Ty with
        | TyInt | TyNat | TyError -> ()
        | t -> c.Error(e.Span, ctx.FnName, what + " must be an int, not " + tyText t)

    // --- expressions --------------------------------------------------------------

    member c.Expr(e: Expr, ctx: Ctx, expected: Ty option) : TExpr =
        let mk kind ty = { Kind = kind; Ty = ty; Span = e.Span }
        let fail () = mk (EBool false) TyError
        match e.Kind with
        | IntLit v -> mk (EInt v) TyInt
        | BoolLit b -> mk (EBool b) TyBool
        | Var name ->
            match c.Lookup name with
            | Some b -> mk (EVar name) b.Ty
            | None ->
                if fns.ContainsKey name then
                    c.Error(e.Span, ctx.FnName, "'" + name + "' is a function: call it with arguments, as in " + name + "(...)")
                else
                    c.Error(e.Span, ctx.FnName, "unknown variable '" + name + "'")
                fail ()
        | Result ->
            match ctx.ResultTy with
            | Some t -> mk EResult t
            | None ->
                c.Error(e.Span, ctx.FnName, "'result' can only be used in an 'ensures' clause")
                fail ()
        | SeqLit items ->
            let elemHint = match expected with Some(TySeq t) -> Some t | _ -> None
            let typed = items |> List.map (fun x -> c.Expr(x, ctx, elemHint))
            let elem =
                match elemHint, typed with
                | Some t, _ -> Some t
                | None, [] -> None
                | None, first :: rest ->
                    rest |> List.fold (fun acc x -> acc |> Option.bind (fun a -> c.Join(a, x.Ty))) (Some first.Ty)
            match elem with
            | Some t ->
                let items = typed |> List.map (fun x -> c.Coerce(x, t, ctx.FnName, "this element"))
                mk (ESeq items) (TySeq t)
            | None when items.IsEmpty ->
                c.Error(e.Span, ctx.FnName, "the type of '[]' cannot be inferred here; give the variable a type, as in 'let xs: seq<int> = []'")
                fail ()
            | None ->
                c.Error(e.Span, ctx.FnName, "the elements of this sequence do not all have the same type")
                fail ()
        | TupleLit items ->
            let hints =
                match expected with
                | Some(TyTuple ts) when ts.Length = items.Length -> List.map Some ts
                | _ -> items |> List.map (fun _ -> None)
            let typed = List.map2 (fun x h -> c.Expr(x, ctx, h)) items hints
            mk (ETuple typed) (TyTuple(typed |> List.map (fun t -> t.Ty)))
        | Index(s, i) ->
            let ts = c.Expr(s, ctx, None)
            let ti = c.Expr(i, ctx, None)
            c.ExpectInt(ti, ctx, "an index")
            match ts.Ty with
            | TySeq t -> mk (EIndex(ts, ti)) t
            | TyError -> fail ()
            | t ->
                c.Error(s.Span, ctx.FnName, "only sequences can be indexed, this is a " + tyText t)
                fail ()
        | Slice(s, lo, hi) ->
            let ts = c.Expr(s, ctx, None)
            let bound (b: Expr option) =
                b |> Option.map (fun x ->
                    let t = c.Expr(x, ctx, None)
                    c.ExpectInt(t, ctx, "a slice bound")
                    t)
            let tlo, thi = bound lo, bound hi
            match ts.Ty with
            | TySeq _ | TyError -> mk (ESlice(ts, tlo, thi)) ts.Ty
            | t ->
                c.Error(s.Span, ctx.FnName, "only sequences can be sliced, this is a " + tyText t)
                fail ()
        | Proj(t, k) ->
            let tt = c.Expr(t, ctx, None)
            match tt.Ty with
            | TyTuple ts when k < ts.Length -> mk (EProj(tt, k)) ts.[k]
            | TyTuple ts ->
                c.Error(e.Span, ctx.FnName, "this tuple has " + string ts.Length + " components, numbered from 0: '." + string k + "' does not exist")
                fail ()
            | TyError -> fail ()
            | other ->
                c.Error(e.Span, ctx.FnName, "'." + string k + "' needs a tuple, this is a " + tyText other)
                fail ()
        | Call("len", args) ->
            match args with
            | [ a ] ->
                let ta = c.Expr(a, ctx, None)
                match ta.Ty with
                | TySeq _ | TyError -> mk (ELen ta) TyNat
                | t ->
                    c.Error(a.Span, ctx.FnName, "len() needs a sequence, this is a " + tyText t)
                    fail ()
            | _ ->
                c.Error(e.Span, ctx.FnName, "len() takes exactly one argument")
                fail ()
        | Call(name, args) ->
            match fns.TryFind name with
            | None ->
                c.Error(e.Span, ctx.FnName, "unknown function '" + name + "'")
                fail ()
            | Some f ->
                let isExprFn = match f.Body with ExprBody _ -> true | StmtBody _ -> false
                if ctx.InSpec && not isExprFn then
                    c.Error(e.Span, ctx.FnName, "'" + name + "' has a statement body, so it cannot be used in a contract; only functions whose body is a single expression can")
                if args.Length <> f.Params.Length then
                    c.Error(e.Span, ctx.FnName, "'" + name + "' takes " + string f.Params.Length + " argument(s), " + string args.Length + " given")
                    fail ()
                else
                    let targs =
                        List.map2 (fun (a: Expr) (p: Param) ->
                            let pt = ofSyntax p.Type
                            c.Coerce(c.Expr(a, ctx, Some pt), pt, ctx.FnName, "argument '" + p.Name + "'")) args f.Params
                    mk (ECall(name, targs)) (ofSyntax f.Ret)
        | Unary(Neg, x) ->
            let tx = c.Expr(x, ctx, None)
            c.ExpectInt(tx, ctx, "the operand of '-'")
            mk (ENeg tx) TyInt
        | Unary(Not, x) ->
            let tx = c.Expr(x, ctx, None)
            c.ExpectBool(tx, ctx, "the operand of '!'")
            mk (ENot tx) TyBool
        | Binary(op, l, r) -> c.Binary(e, op, l, r, ctx, expected)
        | IfExpr(cond, a, b) ->
            let tc = c.Expr(cond, ctx, None)
            c.ExpectBool(tc, ctx, "the condition of 'if'")
            let ta = c.Expr(a, ctx, expected)
            let tb = c.Expr(b, ctx, expected)
            match c.Join(ta.Ty, tb.Ty) with
            | Some t -> mk (EIf(tc, c.Coerce(ta, t, ctx.FnName, "this branch"), c.Coerce(tb, t, ctx.FnName, "this branch"))) t
            | None ->
                c.Error(e.Span, ctx.FnName, "the two branches have different types, " + tyText ta.Ty + " and " + tyText tb.Ty)
                fail ()
        | Quant(q, v, lo, hi, body) ->
            if not ctx.InSpec then
                c.Error(e.Span, ctx.FnName, "quantifiers can only be used in contracts and assertions")
            let tlo = c.Expr(lo, ctx, None)
            let thi = c.Expr(hi, ctx, None)
            c.ExpectInt(tlo, ctx, "the lower bound")
            c.ExpectInt(thi, ctx, "the upper bound")
            c.Push()
            c.Declare(v, { Ty = TyInt; IsMutable = false; What = "bound variable" }, e.Span, ctx.FnName)
            let tbody = c.Expr(body, ctx, None)
            c.Pop()
            c.ExpectBool(tbody, ctx, "the body of a quantifier")
            mk (EQuant(q, v, tlo, thi, tbody)) TyBool

    member c.Binary(e: Expr, op: BinOp, l: Expr, r: Expr, ctx: Ctx, expected: Ty option) : TExpr =
        let mk kind ty = { Kind = kind; Ty = ty; Span = e.Span }
        match op with
        | Add | Sub | Mul | Div | Mod ->
            let tl = c.Expr(l, ctx, (if op = Add then expected else None))
            let tr = c.Expr(r, ctx, (if op = Add then expected else None))
            match op, tl.Ty, tr.Ty with
            | Add, TySeq _, _ | Add, _, TySeq _ ->
                match c.Join(tl.Ty, tr.Ty) with
                | Some t -> mk (EConcat(tl, tr)) t
                | None ->
                    c.Error(e.Span, ctx.FnName, "'+' joins two sequences of the same type, here " + tyText tl.Ty + " and " + tyText tr.Ty)
                    mk (EConcat(tl, tr)) TyError
            | _ ->
                let sym = match op with Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | _ -> "%"
                c.ExpectInt(tl, ctx, "the left operand of '" + sym + "'")
                c.ExpectInt(tr, ctx, "the right operand of '" + sym + "'")
                let aop = match op with Add -> OAdd | Sub -> OSub | Mul -> OMul | Div -> ODiv | _ -> OMod
                mk (EArith(aop, tl, tr)) TyInt
        | Lt | Le | Gt | Ge ->
            let tl = c.Expr(l, ctx, None)
            let tr = c.Expr(r, ctx, None)
            c.ExpectInt(tl, ctx, "a compared value")
            c.ExpectInt(tr, ctx, "a compared value")
            let cop = match op with Lt -> OLt | Le -> OLe | Gt -> OGt | _ -> OGe
            mk (ECmp(cop, tl, tr)) TyBool
        | Eq | Ne ->
            let tl = c.Expr(l, ctx, None)
            let tr = c.Expr(r, ctx, Some tl.Ty)
            if (c.Join(tl.Ty, tr.Ty)).IsNone then
                c.Error(e.Span, ctx.FnName, "values of different types cannot be compared: " + tyText tl.Ty + " and " + tyText tr.Ty)
            let eq = mk (EEq(tl, tr)) TyBool
            if op = Eq then eq else mk (ENot eq) TyBool
        | And | Or | Implies | Iff ->
            let tl = c.Expr(l, ctx, None)
            let tr = c.Expr(r, ctx, None)
            let sym = match op with And -> "&&" | Or -> "||" | Implies -> "==>" | _ -> "<==>"
            c.ExpectBool(tl, ctx, "the left operand of '" + sym + "'")
            c.ExpectBool(tr, ctx, "the right operand of '" + sym + "'")
            let lop = match op with And -> OAnd | Or -> OOr | Implies -> OImplies | _ -> OIff
            mk (ELogic(lop, tl, tr)) TyBool

    /// A boolean contract clause, an assertion or an invariant.
    member c.Spec(e: Expr, fn: string, resultTy: Ty option, what: string) : TExpr =
        let t = c.Expr(e, { InSpec = true; ResultTy = resultTy; FnName = fn }, None)
        c.ExpectBool(t, { InSpec = true; ResultTy = resultTy; FnName = fn }, what)
        t

    member c.Measure(e: Expr, fn: string) : TExpr =
        let ctx = { InSpec = true; ResultTy = None; FnName = fn }
        let t = c.Expr(e, ctx, None)
        c.ExpectInt(t, ctx, "a 'decreases' measure")
        t

    // --- statements ---------------------------------------------------------------

    /// `tail`: these statements end the function, so a final expression is its returned value.
    member c.Stmts(items: Stmt list, f: FnDecl, ret: Ty, tail: bool) : TStmt list =
        let code = { InSpec = false; ResultTy = None; FnName = f.Name }
        let n = items.Length
        items
        |> List.mapi (fun idx (s: Stmt) ->
            let last = tail && idx = n - 1
            let mk k : TStmt = { Kind = k; Span = s.Span }
            match s.Kind with
            | Let(isMut, name, ty, value) ->
                let declared = ty |> Option.map ofSyntax
                let tv = c.Expr(value, code, declared)
                let vty, tv =
                    match declared with
                    | Some t -> t, c.Coerce(tv, t, f.Name, "the value of '" + name + "'")
                    | None ->
                        // A variable is a nat only when declared so: inferred nat widens to int.
                        let t = match tv.Ty with TyNat -> TyInt | t -> t
                        t, tv
                c.Declare(name, { Ty = vty; IsMutable = isMut; What = "local" }, s.Span, f.Name)
                mk (SLet(isMut, name, vty, tv))
            | Assign(name, value) ->
                match c.Lookup name with
                | Some b when b.IsMutable ->
                    let tv = c.Coerce(c.Expr(value, code, Some b.Ty), b.Ty, f.Name, "the assigned value")
                    mk (SAssign(name, tv))
                | Some b ->
                    let advice = if b.What = "local" then "; declare it with 'let mut' to change it" else ""
                    c.Error(s.Span, f.Name, "'" + name + "' is a " + b.What + " and cannot be assigned" + advice)
                    mk (SAssign(name, c.Expr(value, code, None)))
                | None ->
                    c.Error(s.Span, f.Name, "unknown variable '" + name + "'")
                    mk (SAssign(name, c.Expr(value, code, None)))
            | IfStmt(cond, thenB, elseB) ->
                let tc = c.Expr(cond, code, None)
                c.ExpectBool(tc, code, "the condition of 'if'")
                c.Push()
                let tt = c.Stmts(thenB, f, ret, last)
                c.Pop()
                c.Push()
                let te = c.Stmts(defaultArg elseB [], f, ret, last)
                c.Pop()
                mk (SIf(tc, tt, te))
            | While(cond, invs, dec, body) ->
                let tc = c.Expr(cond, code, None)
                c.ExpectBool(tc, code, "the condition of 'while'")
                let tinvs = invs |> List.map (fun i -> c.Spec(i, f.Name, None, "an invariant"))
                let tdec =
                    match dec with
                    | Some d -> c.Measure(d, f.Name)
                    | None ->
                        c.Error(s.Span, f.Name, "a loop needs a 'decreases' clause: an int that gets smaller at each iteration and stays >= 0 (for example 'decreases hi - lo')")
                        { Kind = EInt 0I; Ty = TyInt; Span = s.Span }
                c.Push()
                let tb = c.Stmts(body, f, ret, false)
                c.Pop()
                mk (SWhile(tc, tinvs, tdec, tb))
            | Assert e -> mk (SAssert(c.Spec(e, f.Name, None, "an assertion")))
            | Return e -> mk (SReturn(c.Coerce(c.Expr(e, code, Some ret), ret, f.Name, "the returned value")))
            | FinalExpr e ->
                if not last then
                    c.Error(s.Span, f.Name, "a value can only end the function body (or the branches of its last 'if'); use 'return' here")
                mk (SReturn(c.Coerce(c.Expr(e, code, Some ret), ret, f.Name, "the returned value"))))

    member c.Function(f: FnDecl, recursive: bool) : TFn =
        let ret = ofSyntax f.Ret
        c.Push()
        let ps =
            f.Params |> List.map (fun p ->
                let t = ofSyntax p.Type
                c.Declare(p.Name, { Ty = t; IsMutable = false; What = "parameter" }, p.Span, f.Name)
                { Name = p.Name; Ty = t; Span = p.Span })
        let req = f.Requires |> List.map (fun r -> c.Spec(r, f.Name, None, "a 'requires' clause"))
        let ens = f.Ensures |> List.map (fun e -> c.Spec(e, f.Name, Some ret, "an 'ensures' clause"))
        let loose =
            f.Loose |> Option.map (fun l ->
                c.Push()
                c.Declare(l.Left, { Ty = ret; IsMutable = false; What = "result name" }, f.Span, f.Name)
                c.Declare(l.Right, { Ty = ret; IsMutable = false; What = "result name" }, f.Span, f.Name)
                let rel = c.Spec(l.Relation, f.Name, None, "a 'loose' relation")
                c.Pop()
                { Left = l.Left; Right = l.Right; Relation = rel })
        if f.Loose.IsSome && f.Ensures.IsEmpty then
            c.Error(f.Span, f.Name, "'loose' declares which results may differ, but there is no 'ensures' clause to relax")
        let dec = f.Decreases |> Option.map (fun d -> c.Measure(d, f.Name))
        if recursive && dec.IsNone then
            c.Error(f.Span, f.Name, "'" + f.Name + "' is recursive, so it needs a 'decreases' clause: an int that gets smaller at each recursive call and stays >= 0")
        let body, isExpr =
            match f.Body with
            | ExprBody e ->
                let code = { InSpec = false; ResultTy = None; FnName = f.Name }
                TExprBody(c.Coerce(c.Expr(e, code, Some ret), ret, f.Name, "the body")), true
            | StmtBody items ->
                let ts = c.Stmts(items, f, ret, true)
                if not (alwaysReturns ts) then
                    c.Error(f.Span, f.Name, "not every path returns a value: end the body with 'return' (a loop alone does not count, it may run zero times)")
                TStmtBody ts, false
        c.Pop()
        { Name = f.Name; Params = ps; Ret = ret; Requires = req; Ensures = ens; Loose = loose
          Decreases = dec; Body = body; IsExprFn = isExpr; IsRecursive = recursive; Span = f.Span }

/// Names of the functions called in an expression or statement list (bodies only).
let rec private callsExpr (acc: HashSet<string>) (e: Expr) =
    let go = callsExpr acc
    match e.Kind with
    | Call(n, args) ->
        acc.Add n |> ignore
        List.iter go args
    | SeqLit xs | TupleLit xs -> List.iter go xs
    | Index(a, b) -> go a; go b
    | Slice(a, b, c) -> go a; Option.iter go b; Option.iter go c
    | Proj(a, _) | Unary(_, a) -> go a
    | Binary(_, a, b) -> go a; go b
    | IfExpr(a, b, c) -> go a; go b; go c
    | Quant(_, _, a, b, c) -> go a; go b; go c
    | IntLit _ | BoolLit _ | Var _ | Result -> ()

let rec private callsStmts (acc: HashSet<string>) (ss: Stmt list) =
    for s in ss do
        match s.Kind with
        | Let(_, _, _, v) | Assign(_, v) | Assert v | Return v | FinalExpr v -> callsExpr acc v
        | IfStmt(c, t, e) ->
            callsExpr acc c
            callsStmts acc t
            Option.iter (callsStmts acc) e
        | While(c, invs, d, b) ->
            callsExpr acc c
            List.iter (callsExpr acc) invs
            Option.iter (callsExpr acc) d
            callsStmts acc b

/// Functions that belong to a call cycle (direct or mutual recursion), by Tarjan's algorithm.
let private recursiveFns (fns: FnDecl list) : Set<string> =
    let graph =
        fns |> List.map (fun f ->
            let acc = HashSet<string>()
            match f.Body with
            | ExprBody e -> callsExpr acc e
            | StmtBody ss -> callsStmts acc ss
            f.Name, acc)
        |> dict
    let index = Dictionary<string, int>()
    let low = Dictionary<string, int>()
    let onStack = HashSet<string>()
    let stack = Stack<string>()
    let mutable counter = 0
    let mutable result = Set.empty
    let rec strong (v: string) =
        index.[v] <- counter
        low.[v] <- counter
        counter <- counter + 1
        stack.Push v
        onStack.Add v |> ignore
        for w in graph.[v] do
            if graph.ContainsKey w then
                if not (index.ContainsKey w) then
                    strong w
                    low.[v] <- min low.[v] low.[w]
                elif onStack.Contains w then
                    low.[v] <- min low.[v] index.[w]
        if low.[v] = index.[v] then
            let comp = ResizeArray<string>()
            let mutable go = true
            while go do
                let w = stack.Pop()
                onStack.Remove w |> ignore
                comp.Add w
                go <- w <> v
            if comp.Count > 1 || graph.[v].Contains v then
                result <- Set.union result (set comp)
    for f in fns do
        if not (index.ContainsKey f.Name) then strong f.Name
    result

/// Check a parsed program. Returns the typed program and every type error found.
let check (file: string) (program: Program) : TProgram * Diagnostic list =
    let dups = ResizeArray<Diagnostic>()
    let mutable fns = Map.empty
    for f in program.Fns do
        if fns.ContainsKey f.Name then
            dups.Add
                { File = file; Span = f.Span; Kind = "type"; Status = "error"; Severity = Error; Fn = Some f.Name
                  Property = None; Message = "a function named '" + f.Name + "' is already defined" }
        elif f.Name = "len" then
            dups.Add
                { File = file; Span = f.Span; Kind = "type"; Status = "error"; Severity = Error; Fn = Some f.Name
                  Property = None; Message = "'len' is a built-in function and cannot be redefined" }
        else
            fns <- fns.Add(f.Name, f)
    let recursive = recursiveFns program.Fns
    let checker = Checker(file, fns)
    let typed = program.Fns |> List.map (fun f -> checker.Function(f, recursive.Contains f.Name))
    { Fns = typed }, List.ofSeq dups @ checker.Errors
