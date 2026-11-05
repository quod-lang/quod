/// Modules: a file is a module, and `import name` finds `name.quod` next to the importing file.
/// The whole graph is flattened into one program, in which a function of an imported module is
/// named `module.function`. Type checking and proofs then treat it as they treat a file, and a file
/// without `import` is exactly the program it was before (see docs/design/modules.fr.md).
module Quod.Modules

open System
open System.Collections.Generic
open System.IO
open Quod.Syntax
open Quod.Diagnostics

type Loaded =
    { Program: Program
      /// The file of each imported module.
      Files: Map<string, string>
      /// A local file that hides a module of the standard library.
      Warnings: Diagnostic list }

/// A module of the standard library, embedded in the binary: None if there is no such module.
let private standard (name: string) =
    use stream = Reflection.Assembly.GetExecutingAssembly().GetManifestResourceStream("stdlib/" + name + ".quod")
    if isNull stream then None
    else
        use reader = new StreamReader(stream)
        Some(reader.ReadToEnd().Replace("\r\n", "\n"))

let private error (file: string) (span: Span) (fn: string option) (message: string) : Diagnostic =
    { File = file; Span = span; Kind = "type"; Status = "error"; Severity = Error; Fn = fn
      Property = None; Counterexample = []; Reason = None; Evidence = None; Message = message }

/// The module of a flattened name, and the function in it: `a.f` is (Some "a", "f").
let split (name: string) =
    match name.IndexOf '.' with
    | -1 -> None, name
    | k -> Some(name.Substring(0, k)), name.Substring(k + 1)

/// The same calls under other names. `rename` gets the span, to report what it refuses.
let rec private expr (rename: Span -> string -> string) (e: Expr) : Expr =
    let go = expr rename
    let kind =
        match e.Kind with
        | IntLit _ | BoolLit _ | CharLit _ | StrLit _ | Var _ | Result -> e.Kind
        | SeqLit xs -> SeqLit(List.map go xs)
        | TupleLit xs -> TupleLit(List.map go xs)
        | Index(a, b) -> Index(go a, go b)
        | Slice(a, b, c) -> Slice(go a, Option.map go b, Option.map go c)
        | Proj(a, k) -> Proj(go a, k)
        | Field(a, n) -> Field(go a, n)
        | Match(a, arms) -> Match(go a, arms |> List.map (fun x -> { x with Body = go x.Body }))
        | Call("len", args) -> Call("len", List.map go args)
        | Call(f, args) -> Call(rename e.Span f, List.map go args)
        | Unary(op, a) -> Unary(op, go a)
        | Binary(op, a, b) -> Binary(op, go a, go b)
        | IfExpr(a, b, c) -> IfExpr(go a, go b, go c)
        | Quant(q, v, a, b, c) -> Quant(q, v, go a, go b, go c)
    { e with Kind = kind }

let rec private stmt (rename: Span -> string -> string) (ty: TypeExpr -> TypeExpr) (s: Stmt) : Stmt =
    let e = expr rename
    let block = List.map (stmt rename ty)
    let kind =
        match s.Kind with
        | Let(m, n, t, v) -> Let(m, n, Option.map ty t, e v)
        | Assign(n, v) -> Assign(n, e v)
        | IfStmt(c, a, b) -> IfStmt(e c, block a, Option.map block b)
        | While(c, invs, d, b) -> While(e c, List.map e invs, Option.map e d, block b)
        | Assert x -> Assert(e x)
        | Return x -> Return(e x)
        | FinalExpr x -> FinalExpr(e x)
        | Use(f, args) -> Use(rename s.Span f, List.map e args)
    { s with Kind = kind }

/// Read the file and everything it imports, and flatten them. A syntax error anywhere, an import
/// that cannot be found, a cycle or a call a module may not make is an error of that module's file.
let load (file: string) (src: string) : Result<Loaded, Diagnostic list> =
    let errors = ResizeArray<Diagnostic>()
    let parse (path: string) (text: string) =
        try
            Some(Parser.parseProgram path text)
        with QuodError d ->
            errors.AddRange(Parser.syntaxDiagnostics path text d)
            None
    match parse file src with
    | None -> Result.Error(List.ofSeq errors)
    | Some root when root.Imports.IsEmpty -> Ok { Program = root; Files = Map.empty; Warnings = [] }
    | Some root ->
        let dir = Path.GetDirectoryName file
        let rootName = Path.GetFileNameWithoutExtension file
        // dependencies first: an imported module comes before the modules that import it
        let modules = ResizeArray<string * string * Program>()
        let known = HashSet<string>()
        let warnings = ResizeArray<Diagnostic>()
        let rec visit (path: string) (stack: string list) (program: Program) =
            for name, span in program.Imports do
                if name = rootName || List.contains name stack then
                    let cycle = List.rev ((stack |> List.takeWhile (fun m -> m <> name)) @ [ name ]) @ [ name ]
                    errors.Add(error path span None ("import cycle: " + String.Join(" -> ", cycle)))
                elif known.Add name then
                    let wanted = name + ".quod"
                    let target = Path.Combine(dir, wanted)
                    // the exact name: a program must not compile on Windows and fail on Linux
                    let look = if String.IsNullOrEmpty dir then "." else dir
                    let found = Directory.Exists look && (Directory.GetFiles(look, wanted) |> Array.exists (fun f -> Path.GetFileName f = wanted))
                    let library = standard name
                    if found && library.IsSome then
                        warnings.Add { error path span None ("the file " + wanted + " hides the module '" + name + "' of the standard library") with Severity = Warning; Status = "shadow" }
                    if not found && library.IsNone then
                        errors.Add(error path span None ("no module '" + name + "': there is no file " + wanted + " next to " + Path.GetFileName path + ", and the standard library has none"))
                    else
                        let target = if found then target else "stdlib/" + wanted
                        let text = if found then File.ReadAllText target else library.Value
                        match parse target text with
                        | None -> ()
                        | Some program' ->
                            visit target (name :: stack) program'
                            modules.Add((name, target, program'))
        visit file [ rootName ] root
        if errors.Count > 0 then Result.Error(List.ofSeq errors)
        else
            let byName = modules |> Seq.map (fun (n, _, p) -> n, p) |> Map.ofSeq
            let flattenTypes (name: string option) (program: Program) =
                let flat (f: string) = match name with Some m -> m + "." + f | None -> f
                let typeNames = program.Types |> List.map (fun t -> t.TypeName) |> Set.ofList
                let rec ty (t: TypeExpr) =
                    match t with
                    | TSeq e -> TSeq(ty e)
                    | TTuple ts -> TTuple(List.map ty ts)
                    | TNamed(n, args) when typeNames.Contains n -> TNamed(flat n, List.map ty args)
                    | TNamed(n, args) -> TNamed(n, List.map ty args)
                    | other -> other
                program.Types
                |> List.map (fun t ->
                    { t with
                        TypeName = flat t.TypeName
                        TypeCases = t.TypeCases |> List.map (fun (c, fields) -> flat c, fields |> List.map (fun (f, ft) -> f, ty ft)) })
            let flatten (name: string option) (path: string) (program: Program) =
                let locals = program.Fns |> List.map (fun f -> f.Name) |> Set.ofList
                let imports = program.Imports |> List.map fst |> Set.ofList
                let flat (f: string) = match name with Some m -> m + "." + f | None -> f
                let constructors = program.Types |> List.collect (fun t -> t.TypeCases |> List.map fst) |> Set.ofList
                let typeNames = program.Types |> List.map (fun t -> t.TypeName) |> Set.ofList
                let rec ty (t: TypeExpr) =
                    match t with
                    | TSeq e -> TSeq(ty e)
                    | TTuple ts -> TTuple(List.map ty ts)
                    | TNamed(n, args) when typeNames.Contains n -> TNamed(flat n, List.map ty args)
                    | TNamed(n, args) -> TNamed(n, List.map ty args)
                    | other -> other
                program.Fns
                |> List.map (fun f ->
                    let rename (span: Span) (callee: string) =
                        let refuse (message: string) =
                            errors.Add(error path span (Some(flat f.Name)) message)
                            callee
                        match split callee with
                        | Some m, g when Some m = name || (name.IsNone && m = rootName) ->
                            refuse ("a function of this module is called by its short name: '" + g + "', not '" + callee + "'")
                        | Some m, _ when not (imports.Contains m) ->
                            refuse ("'" + callee + "': add 'import " + m + "' at the top of this file")
                        | Some m, g ->
                            match byName.[m].Fns |> List.tryFind (fun x -> x.Name = g) with
                            | None when byName.[m].Types |> List.exists (fun t -> t.TypeCases |> List.exists (fun (c, _) -> c = g)) -> callee
                            | None -> refuse ("module '" + m + "' has no function '" + g + "'")
                            | Some x when x.IsPrivate -> refuse ("'" + g + "' is private to module '" + m + "'")
                            | Some _ -> callee
                        | None, g when locals.Contains g -> flat g
                        | None, g when constructors.Contains g -> flat g
                        | None, ("code" | "char_of" | "to_i32" | "to_i64") -> callee // built in, unless the module defines it
                        | None, g ->
                            let elsewhere = program.Imports |> List.map fst |> List.filter (fun m -> byName.[m].Fns |> List.exists (fun x -> x.Name = g && not x.IsPrivate))
                            match elsewhere with
                            | m :: _ -> refuse ("unknown function '" + g + "': a function of another module is called by its full name, '" + m + "." + g + "'")
                            | [] -> refuse ("unknown function '" + g + "'")
                    let e = expr rename
                    { f with
                        Name = flat f.Name
                        Params = f.Params |> List.map (fun p -> { p with Type = ty p.Type })
                        Ret = ty f.Ret
                        Requires = List.map e f.Requires
                        Ensures = List.map e f.Ensures
                        Loose = f.Loose |> Option.map (fun l -> { l with Relation = e l.Relation })
                        Decreases = Option.map e f.Decreases
                        Body =
                            match f.Body with
                            | ExprBody x -> ExprBody(e x)
                            | StmtBody items -> StmtBody(List.map (stmt rename ty) items) })
            let imported = modules |> Seq.collect (fun (n, path, p) -> flatten (Some n) path p) |> List.ofSeq
            let own = flatten None file root
            if errors.Count > 0 then Result.Error(List.ofSeq errors)
            else
                let types = (modules |> Seq.collect (fun (n, _, p) -> flattenTypes (Some n) p) |> List.ofSeq) @ flattenTypes None root
                Ok { Program = { Imports = []; Types = types; Fns = imported @ own }
                     Files = modules |> Seq.map (fun (n, path, _) -> n, path) |> Map.ofSeq
                     Warnings = List.ofSeq warnings }

/// A diagnostic about a function of an imported module belongs to that module's file.
let inFile (files: Map<string, string>) (d: Diagnostic) : Diagnostic =
    match d.Fn |> Option.map split with
    | Some(Some m, _) when files.ContainsKey m -> { d with File = files.[m] }
    | _ -> d
