/// Type checker for Quod 0.1: resolves names, checks types and the language rules, and builds
/// the typed representation (Typed.fs). Reports every error it finds, not just the first; an
/// expression that failed gets type TyError, which silences checks that depend on it.
module Quod.Typecheck

open System
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
/// In a file without `import`, a name with a dot is a module that was not imported.
let private unknownFunction (name: string) =
    match name.IndexOf '.' with
    | -1 -> "unknown function '" + name + "'"
    | k -> "'" + name + "': add 'import " + name.Substring(0, k) + "' at the top of this file"

let rec private alwaysReturns (stmts: TStmt list) : bool =
    stmts |> List.exists (fun s ->
        match s.Kind with
        | SReturn _ -> true
        | SIf(_, t, e) -> alwaysReturns t && alwaysReturns e
        | _ -> false)

/// The name of a copy of a generic, from the types it is for: `Option_int`, `first__seq_int`.
let rec private tySuffix (t: Ty) =
    match t with
    | TySeq TyChar -> "string"
    | TySeq e -> "seq_" + tySuffix e
    | TyTuple ts -> "tuple_" + (ts |> List.map tySuffix |> String.concat "_")
    | TyData d -> d.DataName.Replace('.', '_')
    | t -> tyText t

/// A resolved type back as syntax, to put it where a type parameter was.
let rec private typeExprOf (t: Ty) : TypeExpr =
    match t with
    | TyInt | TyError -> TInt
    | TyNat -> TNat
    | TyBool -> TBool
    | TyChar -> TChar
    | TyI32 -> TI32
    | TyI64 -> TI64
    | TySeq e -> TSeq(typeExprOf e)
    | TyTuple ts -> TTuple(List.map typeExprOf ts)
    | TyData d -> TNamed(d.DataName, [])

let rec private substType (env: Map<string, TypeExpr>) (t: TypeExpr) : TypeExpr =
    match t with
    | TSeq e -> TSeq(substType env e)
    | TTuple ts -> TTuple(List.map (substType env) ts)
    | TNamed(n, []) when env.ContainsKey n -> env.[n]
    | TNamed(n, args) -> TNamed(n, List.map (substType env) args)
    | other -> other

let rec private substStmt (env: Map<string, TypeExpr>) (s: Stmt) : Stmt =
    let block = List.map (substStmt env)
    let kind =
        match s.Kind with
        | Let(m, n, t, v) -> Let(m, n, Option.map (substType env) t, v)
        | IfStmt(c, a, b) -> IfStmt(c, block a, Option.map block b)
        | While(c, i, d, b) -> While(c, i, d, block b)
        | other -> other
    { s with Kind = kind }

type private Checker(file: string, initialFns: Map<string, FnDecl>, types: TypeDecl list) =
    let errors = ResizeArray<Diagnostic>()
    let mutable fns = initialFns
    /// The copies of generic functions still to check: each with the name of its generic.
    let pending = Queue<FnDecl * string>()
    let mutable declared = types |> List.map (fun t -> t.TypeName, t) |> Map.ofList
    let resolved = Dictionary<string, DataDecl>()
    let order = ResizeArray<DataDecl>()
    let origins = Dictionary<string, string * Ty list>()
    /// The type and the case of each constructor.
    let constructors =
        types
        |> List.collect (fun t -> t.TypeCases |> List.mapi (fun k (c, _) -> c, (t.TypeName, k)))
        |> Map.ofList
    let scopes = Stack<Dictionary<string, Binding>>()
    /// Lemma calls seen so far in the current function (to name their bindings).
    let mutable lemmaCalls = 0

    member _.Errors = List.ofSeq errors

    /// The structs and enums, each after those it holds.
    member _.DataTypes = List.ofSeq order

    member _.NextCopy() = if pending.Count > 0 then Some(pending.Dequeue()) else None

    /// Which types the parameters stand for, from a type and what is there instead. A conflict
    /// keeps the first: the call is then checked against it, and says what is wrong.
    member private c.Unify(pattern: TypeExpr, actual: Ty, names: string list, env: Map<string, TypeExpr>) : Map<string, TypeExpr> =
        match pattern, actual with
        | _, TyError -> env
        | TNamed(n, []), _ when List.contains n names ->
            if env.ContainsKey n then env
            else env.Add(n, typeExprOf (match actual with TyNat -> TyInt | t -> t))
        | TSeq p, TySeq a -> c.Unify(p, a, names, env)
        | TTuple ps, TyTuple xs when ps.Length = xs.Length -> List.fold2 (fun e p x -> c.Unify(p, x, names, e)) env ps xs
        | TNamed(n, args), TyData d when d.Origin = n && args.Length = d.TypeArgs.Length ->
            List.fold2 (fun e p x -> c.Unify(p, x, names, e)) env args d.TypeArgs
        | _ -> env

    /// The types of these arguments, for an inference only: errors are reported when they are checked.
    member private c.QuietTypes(args: Expr list, ctx: Ctx) : Ty list =
        let before = errors.Count
        let types = args |> List.map (fun a -> (c.Expr(a, ctx, None)).Ty)
        errors.RemoveRange(before, errors.Count - before)
        types

    /// The copy of a generic function for the types of this call.
    member private c.Copy(e: Expr, f: FnDecl, args: Expr list, ctx: Ctx, expected: Ty option) : FnDecl option =
        if args.Length <> f.Params.Length then
            c.Error(e.Span, ctx.FnName, "'" + f.Name + "' takes " + string f.Params.Length + " argument(s), " + string args.Length + " given")
            None
        else
            let fromArgs = List.fold2 (fun env (p: Param) t -> c.Unify(p.Type, t, f.TypeParams, env)) Map.empty f.Params (c.QuietTypes(args, ctx))
            let env = match expected with Some t -> c.Unify(f.Ret, t, f.TypeParams, fromArgs) | None -> fromArgs
            match f.TypeParams |> List.tryFind (fun n -> not (env.ContainsKey n)) with
            | Some n ->
                c.Error(e.Span, ctx.FnName, "nothing here says what the type parameter " + n + " of '" + f.Name + "' is: give a variable or a result its type")
                None
            | None ->
                let suffix = f.TypeParams |> List.map (fun n -> tySuffix (c.Ty env.[n])) |> String.concat "__"
                let name = f.Name + "__" + suffix
                match fns.TryFind name with
                | Some copy -> Some copy
                | None ->
                    let copy =
                        { f with
                            Name = name
                            TypeParams = []
                            Params = f.Params |> List.map (fun p -> { p with Type = substType env p.Type })
                            Ret = substType env f.Ret
                            Body =
                                match f.Body with
                                | StmtBody items -> StmtBody(List.map (substStmt env) items)
                                | b -> b }
                    fns <- fns.Add(name, copy)
                    pending.Enqueue((copy, f.Name))
                    Some copy

    /// A constructor by its name here: in full, or by its short name inside its module.
    member private c.Constructor(name: string, fn: string) =
        match constructors.TryFind name with
        | Some x -> Some x
        | None ->
            match fn.IndexOf '.' with
            | -1 -> None
            | k -> constructors.TryFind(fn.Substring(0, k + 1) + name)

    /// The data type of a constructor here: a generic one from what is expected, or from the fields given.
    member private c.DataOf(e: Expr, tn: string, k: int, args: Expr list, ctx: Ctx, expected: Ty option) : DataDecl option =
        let decl = declared.[tn]
        if decl.Generics.IsEmpty then
            match c.Ty(TNamed(tn, [])) with
            | TyData d -> Some d
            | _ -> None
        else
            match expected with
            | Some(TyData d) when d.Origin = tn -> Some d
            | _ ->
                let fields = snd decl.TypeCases.[k] |> List.map snd
                if fields.Length <> args.Length then
                    c.Error(e.Span, ctx.FnName, "'" + fst decl.TypeCases.[k] + "' takes " + string fields.Length + " value(s), " + string args.Length + " given")
                    None
                else
                    let env = List.fold2 (fun env p t -> c.Unify(p, t, decl.Generics, env)) Map.empty fields (c.QuietTypes(args, ctx))
                    match decl.Generics |> List.tryFind (fun n -> not (env.ContainsKey n)) with
                    | Some n ->
                        c.Error(e.Span, ctx.FnName, "nothing here says what " + n + " is in this '" + tn + "': give a variable or a result its type, as in 'let x: " + tn + "<int> = ...'")
                        None
                    | None ->
                        match c.Ty(TNamed(tn, decl.Generics |> List.map (fun n -> env.[n]))) with
                        | TyData d -> Some d
                        | _ -> None

    /// A type of the syntax. A struct or an enum is resolved once. It cannot hold itself.
    member c.Ty(t: TypeExpr) : Ty = c.TyWithin(t, [])

    member private c.TyWithin(t: TypeExpr, within: string list) : Ty =
        match t with
        | TSeq e -> TySeq(c.TyWithin(e, within))
        | TTuple ts -> TyTuple(ts |> List.map (fun x -> c.TyWithin(x, within)))
        | TNamed(n, args) when (match declared.TryFind n with Some d -> not d.Generics.IsEmpty | None -> false) ->
            let d = declared.[n]
            if args.Length <> d.Generics.Length then
                c.Error(d.TypeSpan, "", "'" + n + "' takes " + string d.Generics.Length + " type(s), " + string args.Length + " given")
                TyError
            else
                let tys = args |> List.map (fun a -> c.TyWithin(a, within))
                let name = n + "_" + (tys |> List.map tySuffix |> String.concat "_")
                if not (declared.ContainsKey name) then
                    let env = List.zip d.Generics (tys |> List.map typeExprOf) |> Map.ofList
                    declared <-
                        declared.Add(name,
                            { d with
                                TypeName = name
                                Generics = []
                                TypeCases = d.TypeCases |> List.map (fun (cn, fs) -> cn, fs |> List.map (fun (f, ft) -> f, substType env ft)) })
                    origins.[name] <- (n, tys)
                c.TyWithin(TNamed(name, []), within)
        | TNamed(n, _) ->
            match resolved.TryGetValue n with
            | true, d -> TyData d
            | _ ->
                match declared.TryFind n with
                | None ->
                    c.Error({ Start = { Line = 1; Col = 1 }; End = { Line = 1; Col = 1 } }, "", "unknown type '" + n + "'")
                    TyError
                | Some d when List.contains n within ->
                    c.Error(d.TypeSpan, "", "the type '" + n + "' holds itself: recursive types are not in Quod 0.3, since a value must be copied as it is")
                    TyError
                | Some d ->
                    let cases =
                        d.TypeCases |> List.map (fun (name, fields) ->
                            { CaseName = name; Fields = fields |> List.map (fun (f, ft) -> f, c.TyWithin(ft, n :: within)) })
                    let origin, tys = match origins.TryGetValue n with | true, x -> x | _ -> n, []
                    let data = { DataName = n; Origin = origin; TypeArgs = tys; IsStruct = d.IsStruct; DataCases = cases }
                    resolved.[n] <- data
                    order.Add data
                    TyData data
        | other -> ofSyntax other

    member private c.Build(e: Expr, data: DataDecl, k: int, args: Expr list, ctx: Ctx) : TExpr =
        let case = data.DataCases.[k]
        if args.Length <> case.Fields.Length then
            c.Error(e.Span, ctx.FnName, "'" + case.CaseName + "' takes " + string case.Fields.Length + " value(s), " + string args.Length + " given")
            { Kind = EBool false; Ty = TyError; Span = e.Span }
        else
            let parts =
                List.map2 (fun (a: Expr) (name: string, t: Ty) ->
                    c.Coerce(c.Expr(a, ctx, Some t), t, ctx.FnName, "the field '" + name + "' of '" + case.CaseName + "'")) args case.Fields
            { Kind = ECons(k, parts); Ty = TyData data; Span = e.Span }

    member _.Error(span: Span, fn: string, message: string) =
        errors.Add
            { File = file; Span = span; Kind = "type"; Status = "error"; Severity = Error
              Fn = (if fn = "" then None else Some fn); Property = None; Counterexample = []; Reason = None; Evidence = None; Message = message }

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
        | TyI32, TyI64 | TyI64, TyI32 -> Some TyI64
        | (TyI32 | TyI64), (TyNat | TyInt) | (TyNat | TyInt), (TyI32 | TyI64) -> Some TyInt
        // under a sequence or a tuple the representation differs: a seq<i32> is not a seq<int>
        | TySeq x, TySeq y when isBounded x || isBounded y -> None
        | TySeq x, TySeq y -> c.Join(x, y) |> Option.map TySeq
        | TyTuple xs, TyTuple ys when xs.Length = ys.Length && List.exists2 (fun x y -> x <> y && (isBounded x || isBounded y)) xs ys -> None
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
        // `[]` where a string is expected is the empty string: the generators must know it
        if expected = TySeq TyChar && e.Kind = ESeq [] then { e with Ty = expected }
        elif (match e.Kind, boundsOf expected with EInt _, Some _ -> e.Ty = TyInt | _ -> false) then c.Literal(e, expected, fn)
        elif fits e.Ty expected then e
        // always exact: a bounded integer is an integer, and an i32 an i64
        elif (isBounded e.Ty && expected = TyInt) || (e.Ty = TyI32 && expected = TyI64) then e
        elif (e.Ty = TyInt || isBounded e.Ty) && expected = TyNat then { Kind = EToNat e; Ty = TyNat; Span = e.Span }
        else
            // a literal (or an if) is coerced part by part: (x, n + 1) as (int, nat) proves n + 1 >= 0
            match e.Kind, expected with
            | ETuple xs, TyTuple ts when xs.Length = ts.Length ->
                let parts = List.map2 (fun x t -> c.Coerce(x, t, fn, what)) xs ts
                { e with Kind = ETuple parts; Ty = TyTuple(parts |> List.map (fun p -> p.Ty)) }
            | ESeq xs, TySeq t when not xs.IsEmpty ->
                let parts = xs |> List.map (fun x -> c.Coerce(x, t, fn, what))
                { e with Kind = ESeq parts; Ty = TySeq t }
            | EIf(cond, a, b), _ ->
                let ta, tb = c.Coerce(a, expected, fn, what), c.Coerce(b, expected, fn, what)
                { e with Kind = EIf(cond, ta, tb); Ty = (if ta.Ty = TyError || tb.Ty = TyError then TyError else expected) }
            | _ ->
                let hint = if isBounded expected && (match e.Ty with TyInt | TyNat | TyI64 -> true | _ -> false) then " (nothing narrows by itself: write to_" + tyText expected + "(...), which must then be proved to fit)" else ""
                c.Error(e.Span, fn, what + " has type " + tyText e.Ty + ", but " + tyText expected + " is expected" + hint)
                { e with Ty = TyError }

    /// An integer literal takes the bounded type its context wants, if it fits.
    member c.Literal(e: TExpr, t: Ty, fn: string) : TExpr =
        match e.Kind, boundsOf t with
        | EInt v, Some(lo, hi) ->
            if v < lo || v > hi then
                c.Error(e.Span, fn, v.ToString() + " does not fit in " + tyText t)
                { e with Ty = TyError }
            else
                { e with Ty = t }
        | _ -> e

    /// A literal next to a bounded integer takes its type: `x + 1`, `x < 10`.
    member c.Adopt(a: TExpr, b: TExpr, fn: string) : TExpr * TExpr =
        let isLiteral (e: TExpr) = match e.Kind with EInt _ -> e.Ty = TyInt | _ -> false
        if isLiteral a && isBounded b.Ty then c.Literal(a, b.Ty, fn), b
        elif isLiteral b && isBounded a.Ty then a, c.Literal(b, a.Ty, fn)
        else a, b

    member c.ExpectBool(e: TExpr, ctx: Ctx, what: string) =
        if e.Ty <> TyBool && e.Ty <> TyError then
            c.Error(e.Span, ctx.FnName, what + " must be a bool, not " + tyText e.Ty)

    member c.ExpectInt(e: TExpr, ctx: Ctx, what: string) =
        match e.Ty with
        | TyInt | TyNat | TyI32 | TyI64 | TyError -> ()
        | t -> c.Error(e.Span, ctx.FnName, what + " must be an int, not " + tyText t)

    // --- expressions --------------------------------------------------------------

    member c.Expr(e: Expr, ctx: Ctx, expected: Ty option) : TExpr =
        let mk kind ty = { Kind = kind; Ty = ty; Span = e.Span }
        let fail () = mk (EBool false) TyError
        match e.Kind with
        | IntLit v -> mk (EInt v) TyInt
        | BoolLit b -> mk (EBool b) TyBool
        | CharLit v -> mk (EInt(bigint v)) TyChar
        | StrLit vs -> mk (ESeq(vs |> List.map (fun v -> mk (EInt(bigint v)) TyChar))) (TySeq TyChar)
        // `module.Case`, a case without fields: a module is not a value
        | Field({ Kind = Var m }, name) when (c.Lookup m).IsNone && constructors.ContainsKey(m + "." + name) ->
            let tn, k = constructors.[m + "." + name]
            match c.DataOf(e, tn, k, [], ctx, expected) with
            | Some d -> c.Build(e, d, k, [], ctx)
            | None -> fail ()
        | Field(a, name) ->
            let ta = c.Expr(a, ctx, None)
            match ta.Ty with
            | TyData d when d.IsStruct ->
                match d.DataCases.[0].Fields |> List.tryFindIndex (fun (f, _) -> f = name) with
                | Some i -> mk (EField(ta, 0, i)) (snd d.DataCases.[0].Fields.[i])
                | None ->
                    c.Error(e.Span, ctx.FnName, "'" + d.DataName + "' has no field '" + name + "'")
                    fail ()
            | TyError -> fail ()
            | t ->
                c.Error(e.Span, ctx.FnName, "'." + name + "' needs a struct, this is " + tyText t + (match t with TyData _ -> ": an enum is read with 'match'" | _ -> ""))
                fail ()
        | Match(scrutinee, arms) ->
            let ts = c.Expr(scrutinee, ctx, None)
            match ts.Ty with
            | TyData d ->
                let seen = Dictionary<int, string list * TExpr>()
                let mutable others: Expr option = None
                let mutable joined: Ty option = expected
                let typedArm (case: DataCase) (binders: string list) (body: Expr) =
                    c.Push()
                    List.iter2 (fun (n: string) (_, t: Ty) ->
                        if n <> "_" then c.Declare(n, { Ty = t; IsMutable = false; What = "pattern variable" }, body.Span, ctx.FnName)) binders case.Fields
                    let tb = c.Expr(body, ctx, expected)
                    c.Pop()
                    joined <-
                        match joined with
                        | None -> Some tb.Ty
                        | Some j ->
                            match c.Join(j, tb.Ty) with
                            | Some t -> Some t
                            | None ->
                                c.Error(body.Span, ctx.FnName, "the cases of this 'match' have different types, " + tyText j + " and " + tyText tb.Ty)
                                Some j
                    tb
                for arm in arms do
                    match arm.Case with
                    | None ->
                        if others.IsSome then c.Error(arm.ArmSpan, ctx.FnName, "'_' can appear once in a 'match'")
                        others <- Some arm.Body
                    | Some name ->
                        if others.IsSome then c.Error(arm.ArmSpan, ctx.FnName, "'_' comes last: it covers every case not named before it")
                        match d.DataCases |> List.tryFindIndex (fun x -> x.CaseName = name || shortName x.CaseName = name) with
                        | None -> c.Error(arm.ArmSpan, ctx.FnName, "'" + d.DataName + "' has no case '" + name + "'")
                        | Some k when seen.ContainsKey k -> c.Error(arm.ArmSpan, ctx.FnName, "the case '" + name + "' appears twice in this 'match'")
                        | Some k ->
                            let case = d.DataCases.[k]
                            if arm.Binders.Length <> case.Fields.Length then
                                c.Error(arm.ArmSpan, ctx.FnName, "the case '" + name + "' has " + string case.Fields.Length + " field(s), " + string arm.Binders.Length + " named")
                            else
                                seen.[k] <- (arm.Binders, typedArm case arm.Binders arm.Body)
                let missing = d.DataCases |> List.indexed |> List.filter (fun (k, _) -> not (seen.ContainsKey k))
                match others with
                | Some body ->
                    for k, case in missing do
                        seen.[k] <- (case.Fields |> List.map (fun _ -> "_"), typedArm case (case.Fields |> List.map (fun _ -> "_")) body)
                | None ->
                    if not missing.IsEmpty then
                        c.Error(e.Span, ctx.FnName, "this 'match' forgets the case(s) " + String.Join(", ", missing |> List.map (fun (_, x) -> "'" + x.CaseName + "'")))
                if seen.Count <> d.DataCases.Length then fail ()
                else
                    let ty = defaultArg joined TyError
                    mk (EMatch(ts, [ for k in 0 .. d.DataCases.Length - 1 -> (let names, b = seen.[k] in k, names, c.Coerce(b, ty, ctx.FnName, "this case of 'match'")) ])) ty
            | TyError -> fail ()
            | t ->
                c.Error(scrutinee.Span, ctx.FnName, "'match' needs an enum, this is " + tyText t)
                fail ()
        | Var name when (c.Lookup name).IsNone && (c.Constructor(name, ctx.FnName)).IsSome ->
            let tn, k = (c.Constructor(name, ctx.FnName)).Value
            match c.DataOf(e, tn, k, [], ctx, expected) with
            | Some d -> c.Build(e, d, k, [], ctx)
            | None -> fail ()
        | Call(name, args) when not (fns.ContainsKey name) && (c.Constructor(name, ctx.FnName)).IsSome ->
            let tn, k = (c.Constructor(name, ctx.FnName)).Value
            match c.DataOf(e, tn, k, args, ctx, expected) with
            | Some d -> c.Build(e, d, k, args, ctx)
            | None -> fail ()
        | Call(name, args) when (match fns.TryFind name with Some f -> not f.TypeParams.IsEmpty | None -> false) ->
            match c.Copy(e, fns.[name], args, ctx, expected) with
            | Some copy -> c.Expr({ e with Kind = Call(copy.Name, args) }, ctx, expected)
            | None -> fail ()
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
        | Call("code", [ a ]) when not (fns.ContainsKey "code") ->
            let ta = c.Expr(a, ctx, None)
            match ta.Ty with
            | TyChar -> mk (EConvert ta) TyNat
            | TyError -> fail ()
            | t ->
                c.Error(a.Span, ctx.FnName, "code() takes a char, this is " + tyText t)
                fail ()
        | Call(("to_i32" | "to_i64") as conversion, [ a ]) when not (fns.ContainsKey conversion) ->
            let ta = c.Expr(a, ctx, None)
            c.ExpectInt(ta, ctx, "the argument of " + conversion)
            mk (EConvert ta) (if conversion = "to_i32" then TyI32 else TyI64)
        | Call("char_of", [ a ]) when not (fns.ContainsKey "char_of") ->
            let ta = c.Expr(a, ctx, None)
            c.ExpectInt(ta, ctx, "the argument of char_of")
            mk (EConvert ta) TyChar
        | Call(name, args) ->
            match fns.TryFind name with
            | None ->
                c.Error(e.Span, ctx.FnName, unknownFunction name)
                fail ()
            | Some f when f.IsLemma ->
                // a lemma has no value: nothing proved by it can flow into the computed result
                c.Error(e.Span, ctx.FnName, "'" + name + "' is a lemma: it has no value, so it is not used in an expression; call it as a proof step, '" + name + "(...);'")
                fail ()
            | Some f ->
                let isExprFn = match f.Body with ExprBody _ -> true | StmtBody _ -> false
                if ctx.InSpec && not isExprFn then
                    c.Error(e.Span, ctx.FnName, "'" + name + "' has a statement body, so it cannot be used in a contract; only functions whose body is a single expression can")
                match c.Args(e, f, args, ctx) with
                | Some targs -> mk (ECall(name, targs)) (c.Ty f.Ret)
                | None -> fail ()
        | Unary(Neg, x) ->
            let tx = c.Expr(x, ctx, None)
            c.ExpectInt(tx, ctx, "the operand of '-'")
            mk (ENeg tx) (if isBounded tx.Ty && not ctx.InSpec then tx.Ty else TyInt)
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

    /// The arguments of a call to f, typed against its parameters (None: wrong count).
    member c.Args(e: Expr, f: FnDecl, args: Expr list, ctx: Ctx) : TExpr list option =
        if args.Length <> f.Params.Length then
            c.Error(e.Span, ctx.FnName, "'" + f.Name + "' takes " + string f.Params.Length + " argument(s), " + string args.Length + " given")
            None
        else
            Some(
                List.map2 (fun (a: Expr) (p: Param) ->
                    let pt = c.Ty p.Type
                    c.Coerce(c.Expr(a, ctx, Some pt), pt, ctx.FnName, "argument '" + p.Name + "'")) args f.Params)

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
                let tl, tr = c.Adopt(tl, tr, ctx.FnName)
                // two literals, where a bounded integer is expected
                let tl, tr =
                    match expected with
                    | Some t when isBounded t && not ctx.InSpec && tl.Ty = TyInt && tr.Ty = TyInt ->
                        (match tl.Kind with EInt _ -> c.Literal(tl, t, ctx.FnName) | _ -> tl), (match tr.Kind with EInt _ -> c.Literal(tr, t, ctx.FnName) | _ -> tr)
                    | _ -> tl, tr
                // in a contract, arithmetic is mathematical; in code, two bounded operands stay bounded
                let ty =
                    if ctx.InSpec then TyInt
                    else
                        match tl.Ty, tr.Ty with
                        | TyI64, (TyI32 | TyI64) | TyI32, TyI64 -> TyI64
                        | TyI32, TyI32 -> TyI32
                        | _ -> TyInt
                mk (EArith(aop, tl, tr)) ty
        | Lt | Le | Gt | Ge ->
            let tl = c.Expr(l, ctx, None)
            let tr = c.Expr(r, ctx, None)
            // two chars compare by their scalar values, without any locale
            if not (tl.Ty = TyChar && tr.Ty = TyChar) then
                c.ExpectInt(tl, ctx, "a compared value")
                c.ExpectInt(tr, ctx, "a compared value")
            let tl, tr = c.Adopt(tl, tr, ctx.FnName)
            let cop = match op with Lt -> OLt | Le -> OLe | Gt -> OGt | _ -> OGe
            mk (ECmp(cop, tl, tr)) TyBool
        | Eq | Ne ->
            let tl = c.Expr(l, ctx, None)
            let tr = c.Expr(r, ctx, Some tl.Ty)
            let tl, tr = c.Adopt(tl, tr, ctx.FnName)
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
                let declared = ty |> Option.map c.Ty
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
            | Return _ | FinalExpr _ when f.IsLemma ->
                c.Error(s.Span, f.Name, "a lemma returns nothing: its body is proof steps (asserts, lemma calls, 'if' to split cases), and what it proves goes in its 'ensures'")
                mk (SAssert { Kind = EBool true; Ty = TyBool; Span = s.Span })
            | Use(name, args) ->
                let ok = { Kind = EBool true; Ty = TyBool; Span = s.Span }
                match fns.TryFind name with
                | Some g when g.IsLemma ->
                    let callExpr: Expr = { Kind = Call(name, args); Span = s.Span }
                    match c.Args(callExpr, g, args, code) with
                    | Some targs ->
                        lemmaCalls <- lemmaCalls + 1
                        mk (SLet(false, lemmaBinding lemmaCalls, TyBool, { Kind = ECall(name, targs); Ty = TyBool; Span = s.Span }))
                    | None -> mk (SAssert ok)
                | Some _ ->
                    c.Error(s.Span, f.Name, "this call has no effect (Quod functions are pure); 'return' it or bind it with 'let' (only a lemma is called on its own)")
                    mk (SAssert ok)
                | None ->
                    c.Error(s.Span, f.Name, unknownFunction name)
                    mk (SAssert ok)
            | Return e -> mk (SReturn(c.Coerce(c.Expr(e, code, Some ret), ret, f.Name, "the returned value")))
            | FinalExpr e ->
                if not last then
                    c.Error(s.Span, f.Name, "a value can only end the function body (or the branches of its last 'if'); use 'return' here")
                mk (SReturn(c.Coerce(c.Expr(e, code, Some ret), ret, f.Name, "the returned value"))))

    member c.Function(f: FnDecl, cycle: int option) : TFn =
        let recursive = cycle.IsSome
        let ret = c.Ty f.Ret
        lemmaCalls <- 0
        c.Push()
        let ps =
            f.Params |> List.map (fun p ->
                let t = c.Ty p.Type
                c.Declare(p.Name, { Ty = t; IsMutable = false; What = "parameter" }, p.Span, f.Name)
                { Name = p.Name; Ty = t; Span = p.Span })
        let req = f.Requires |> List.map (fun r -> c.Spec(r, f.Name, None, "a 'requires' clause"))
        let ens = f.Ensures |> List.map (fun e -> c.Spec(e, f.Name, (if f.IsLemma then None else Some ret), "an 'ensures' clause"))
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
            | StmtBody items when f.IsLemma ->
                // the steps, then the implicit end: a lemma "returns" true, which its callers ignore
                let ts = c.Stmts(items, f, ret, false)
                TStmtBody(ts @ [ { Kind = SReturn { Kind = EBool true; Ty = TyBool; Span = f.Span }; Span = f.Span } ]), false
            | StmtBody items ->
                let ts = c.Stmts(items, f, ret, true)
                if not (alwaysReturns ts) then
                    c.Error(f.Span, f.Name, "not every path returns a value: end the body with 'return' (a loop alone does not count, it may run zero times)")
                TStmtBody ts, false
        c.Pop()
        { Name = f.Name; Params = ps; Ret = ret; Requires = req; Ensures = ens; Loose = loose
          Decreases = dec; Body = body; IsExprFn = isExpr; IsRecursive = recursive
          Cycle = defaultArg cycle -1; IsLemma = f.IsLemma; RunBy = f.RunBy; IsPrivate = f.IsPrivate; Span = f.Span }

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
    | IntLit _ | BoolLit _ | CharLit _ | StrLit _ | Var _ | Result -> ()
    | Field(a, _) -> go a
    | Match(a, arms) -> go a; arms |> List.iter (fun x -> go x.Body)

let rec private callsStmts (acc: HashSet<string>) (ss: Stmt list) =
    for s in ss do
        match s.Kind with
        | Let(_, _, _, v) | Assign(_, v) | Assert v | Return v | FinalExpr v -> callsExpr acc v
        | Use(n, args) ->
            acc.Add n |> ignore
            List.iter (callsExpr acc) args
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
let private recursiveFns (fns: FnDecl list) : Map<string, int> =
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
    let mutable result = Map.empty
    let mutable cycles = 0
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
                for w in comp do
                    result <- result.Add(w, cycles)
                cycles <- cycles + 1
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
                  Property = None; Counterexample = []; Reason = None; Evidence = None; Message = "a function named '" + f.Name + "' is already defined" }
        elif f.Name = "len" then
            dups.Add
                { File = file; Span = f.Span; Kind = "type"; Status = "error"; Severity = Error; Fn = Some f.Name
                  Property = None; Counterexample = []; Reason = None; Evidence = None; Message = "'len' is a built-in function and cannot be redefined" }
        else
            fns <- fns.Add(f.Name, f)
    let recursive = recursiveFns program.Fns
    let checker = Checker(file, fns, program.Types)
    // a name means one thing: the two cases of two enums, or a case and a function, would need a qualifier
    let names = Dictionary<string, string>()
    for t in program.Types do
        let what = if t.IsStruct then "struct" else "enum"
        for name, fields in t.TypeCases do
            if names.ContainsKey name || fns.ContainsKey name then
                dups.Add
                    { File = file; Span = t.TypeSpan; Kind = "type"; Status = "error"; Severity = Error; Fn = None
                      Property = None; Counterexample = []; Reason = None; Evidence = None
                      Message = "'" + name + "' of this " + what + " is already the name of " + (match names.TryGetValue name with | true, w -> w | _ -> "a function") }
            names.[name] <- "a case or a struct"
            if (fields |> List.map fst |> List.distinct).Length <> fields.Length then
                dups.Add
                    { File = file; Span = t.TypeSpan; Kind = "type"; Status = "error"; Severity = Error; Fn = None
                      Property = None; Counterexample = []; Reason = None; Evidence = None; Message = "'" + name + "' has two fields of the same name" }
    for t in program.Types do
        if t.Generics.IsEmpty then checker.Ty(TNamed(t.TypeName, [])) |> ignore
    // a generic function is checked, and proved, for the types it is used with
    let typed = program.Fns |> List.filter (fun f -> f.TypeParams.IsEmpty) |> List.map (fun f -> checker.Function(f, recursive.TryFind f.Name))
    let copies = ResizeArray<TFn>()
    let rec drain () =
        match checker.NextCopy() with
        | Some(copy, origin) ->
            copies.Add(checker.Function(copy, recursive.TryFind origin))
            drain ()
        | None -> ()
    drain ()
    let all = typed @ List.ofSeq copies
    // `run_by`: the same parameters, and a contract that says it is the same function
    for f in all do
        match f.RunBy with
        | None -> ()
        | Some name ->
            let refuse (message: string) =
                dups.Add
                    { File = file; Span = f.Span; Kind = "type"; Status = "error"; Severity = Error; Fn = Some f.Name
                      Property = None; Counterexample = []; Reason = None; Evidence = None; Message = message }
            match all |> List.tryFind (fun g -> g.Name = name) with
            | None -> refuse ("'run_by " + name + "': there is no such function")
            | Some g ->
                let sameShape = g.Ret = f.Ret && g.Params.Length = f.Params.Length && List.forall2 (fun (a: TParam) (b: TParam) -> a.Name = b.Name && a.Ty = b.Ty) g.Params f.Params
                let isEquality (e: TExpr) =
                    match e.Kind with
                    | EEq({ Kind = EResult }, { Kind = ECall(n, args) }) ->
                        n = f.Name && args.Length = f.Params.Length
                        && List.forall2 (fun (a: TExpr) (p: TParam) -> match a.Kind with EVar v -> v = p.Name | _ -> false) args f.Params
                    | _ -> false
                if not sameShape then refuse ("'run_by " + name + "': it must have the same parameters and the same result as '" + f.Name + "'")
                elif not f.IsExprFn then refuse ("'run_by' is for a function whose body is an expression: '" + f.Name + "' is the one contracts read")
                elif not (g.Ensures |> List.exists isEquality) then
                    refuse ("'run_by " + name + "': its contract must state 'ensures result == " + f.Name + "(" + String.Join(", ", f.Params |> List.map (fun p -> p.Name)) + ")'")
    { Types = checker.DataTypes; Fns = all }, List.ofSeq dups @ checker.Errors
