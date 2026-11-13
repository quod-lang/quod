/// The `quod` command line: `parse`, `check` (types, proofs, completeness), `build`, `mcp`.
module Quod.Program

open System
open System.IO
open Quod.Diagnostics

let private usage =
    "usage: quod <command> FILE [options]\n"
    + "  parse   read FILE, report the first syntax error, or print the program back\n"
    + "  check   type-check FILE, prove its contracts, check that they are complete\n"
    + "  build   check FILE, then generate code (only for a verified program)\n"
    + "  run     check FILE, then run its main(c: console.Console) and print what it writes (--function NAME for another)
"
    + "  mcp     serve check, build, run and the language reference to an AI agent (MCP, stdio)\n"
    + "  contract FILE CASES --function NAME   evaluate a contract on the arguments and results of a JSON file\n"
    + "  reference [SECTION]   print the language reference (all there is to know to write Quod),\n"
    + "          or one section of it, e.g. quod reference \"Hints and lemmas\"\n"
    + "options:\n"
    + "  --json              diagnostics as JSON\n"
    + "  --z3 PATH           the z3 executable (default: next to quod, $QUOD_Z3, then PATH)\n"
    + "  --timeout SECONDS   limit per proof obligation, in solver operations: 4000 per ms (default 10)\n"
    + "  --budget SECONDS    time limit of the whole check (default 300, 60 for mcp, 0 for none): the obligations\n"
    + "                      left when it is used up are reported as not attempted\n"
    + "  --require-contracts a function without a contract, or a 'loose' that accepts every result, is an\n"
    + "                      error (check, build, mcp); expression functions that another function calls\n"
    + "                      are explained by their definition\n"
    + "  --smt-log FILE      write every command sent to z3 to FILE\n"
    + "  --target TARGET     code generation target (build): python (default) or csharp\n"
    + "  --namespace NAME    namespace of the generated C# (default Quod.Generated)\n"
    + "  --check-requires all  also check the quantified requires when a public function is called\n"
    + "  -o DIR              output directory (build; default: next to FILE)\n"
    + "  --output-file FILE  the generated file itself (build), instead of -o\n"
    + "  --format msbuild    diagnostics as MSBuild reads them, each with a code QUOD0001...\n"
    + "  --files DIR         the directory a program run by `quod run` reads and writes (a main that takes a Files)\n"
    + "  --runtime-checks    build even if some proofs fail: their contracts become run-time\n"
    + "                      assertions (an underspecified contract still blocks the build)"

type private Options =
    { Json: bool
      Settings: Pipeline.Settings
      Target: string
      Namespace: string option
      AllRequires: bool
      OutDir: string option
      OutputFile: string option
      Function: string option
      BuildFormat: bool
      RuntimeChecks: bool
      /// --budget was given (quod mcp has its own default otherwise)
      BudgetGiven: bool
      /// the directory a program run by `quod run` reads and writes (--files)
      FilesDir: string option }

let private parseOptions (args: string list) : Options * string list =
    let rec go (o: Options) (rest: string list) (positional: string list) =
        let s = o.Settings
        match rest with
        | "--json" :: tl -> go { o with Json = true } tl positional
        | "--z3" :: p :: tl -> go { o with Settings = { s with Z3 = Some p } } tl positional
        | "--timeout" :: n :: tl -> go { o with Settings = { s with Timeout = int n } } tl positional
        | "--budget" :: n :: tl -> go { o with Settings = { s with Budget = int n }; BudgetGiven = true } tl positional
        | "--require-contracts" :: tl -> go { o with Settings = { s with RequireContracts = true } } tl positional
        | "--smt-log" :: p :: tl -> go { o with Settings = { s with SmtLog = Some p } } tl positional
        | "--target" :: t :: tl -> go { o with Target = t } tl positional
        | "--namespace" :: n :: tl -> go { o with Namespace = Some n } tl positional
        | "--check-requires" :: "all" :: tl -> go { o with AllRequires = true } tl positional
        | "-o" :: d :: tl -> go { o with OutDir = Some d } tl positional
        | "--output-file" :: f :: tl -> go { o with OutputFile = Some f } tl positional
        | "--function" :: f :: tl -> go { o with Function = Some f } tl positional
        | "--files" :: d :: tl -> go { o with FilesDir = Some d } tl positional
        | "--format" :: "msbuild" :: tl -> go { o with BuildFormat = true } tl positional
        | "--runtime-checks" :: tl -> go { o with RuntimeChecks = true } tl positional
        | x :: tl -> go o tl (positional @ [ x ])
        | [] -> o, positional
    go { Json = false; Settings = Pipeline.defaultSettings; Target = "python"; Namespace = None; AllRequires = false; OutDir = None; OutputFile = None; Function = None; BuildFormat = false; RuntimeChecks = false; BudgetGiven = false; FilesDir = None } args []

let private report (o: Options) (ds: Diagnostic list) =
    if o.Json then Console.WriteLine(toJson ds)
    else for d in ds do if d.Severity <> Info then Console.Error.WriteLine((if o.BuildFormat then toBuildText else toText) d) // notes: in the summary

let private withFile (file: string) (action: string -> int) =
    if File.Exists file then action (File.ReadAllText file)
    else
        Console.Error.WriteLine("error: " + file + " not found")
        2

let private parseCommand (file: string) (o: Options) =
    withFile file (fun src ->
        try
            let program = Parser.parseProgram file src
            if o.Json then report o [] else Console.Write(Printer.programText program)
            0
        with QuodError d ->
            report o (Parser.syntaxDiagnostics file src d)
            1)

/// Check, and report the diagnostics. Ok with the typed program and the verification result,
/// or Error with the exit code once everything has been reported.
let private verifyFile (file: string) (src: string) (o: Options) : Result<Typed.TProgram * Vcgen.VerifyResult, int> =
    match Pipeline.check file src o.Settings with
    | Pipeline.Checked(typed, result) ->
        report o result.Diagnostics
        Ok(typed, result)
    | Pipeline.Rejected ds ->
        report o ds
        Result.Error 1
    | Pipeline.Failure(message, code) ->
        Console.Error.WriteLine("error: " + message)
        Result.Error code

let private checkCommand (file: string) (o: Options) =
    withFile file (fun src ->
        match verifyFile file src o with
        | Result.Error code -> code
        | Ok(_, result) ->
            let errors = Pipeline.errorsOf result
            if not o.Json then
                let line = (if errors.IsEmpty then "verified: " else "rejected: ") + Pipeline.summary result
                if errors.IsEmpty then Console.WriteLine line else Console.Error.WriteLine line
            if errors.IsEmpty then 0 else 1) // an inconclusive completeness verdict is a warning only

let private buildCommand (file: string) (o: Options) =
    match Pipeline.targetOf o.Target o.Namespace o.AllRequires with
    | Result.Error why ->
        Console.Error.WriteLine("error: " + why)
        2
    | Ok target ->
        withFile file (fun src ->
            match verifyFile file src o with
            | Result.Error code -> code
            | Ok(typed, result) ->
                match Pipeline.generate target file typed result o.RuntimeChecks with
                | Result.Error why ->
                    Console.Error.WriteLine why
                    1
                | Ok generated ->
                    let code, unproved = generated.Code, generated.Unproved
                    let dir = defaultArg o.OutDir (Path.GetDirectoryName(Path.GetFullPath file))
                    Directory.CreateDirectory dir |> ignore
                    let written = defaultArg o.OutputFile (Path.Combine(dir, Pipeline.outputOf target file))
                    let writtenDir = Path.GetDirectoryName(Path.GetFullPath written)
                    Directory.CreateDirectory writtenDir |> ignore
                    File.WriteAllText(written, code)
                    // the imported modules go next to it: Python finds them there, and C# compiles them
                    // with --output-file (Quod.Build), the names of the caller's convention: `name.g.cs`
                    for m, text in generated.Imported do
                        let name = if o.OutputFile.IsSome then m + ".g.cs" else Pipeline.outputOf target (m + ".quod")
                        File.WriteAllText(Path.Combine(writtenDir, name), text)
                    if not o.Json then
                        Console.WriteLine("built " + written + " (" + Pipeline.summary result + ")")
                        if not unproved.IsEmpty then
                            Console.Error.WriteLine(
                                "warning: not fully proved, contracts checked at run time in: " + String.Join(", ", unproved))
                    0)

/// The text of a string value of the evaluator.
let private stringOfValue (v: Eval.Value) =
    match v with
    | Eval.VSeq cs -> String.Join("", cs |> List.map (function Eval.VChar c -> Char.ConvertFromUtf32 c | _ -> ""))
    | _ -> ""

let private valueOfString (s: string) = Eval.VSeq [ for r in s.EnumerateRunes() -> Eval.VChar r.Value ]

/// A path of the model is a relative path with no `..`: the files a program names stay under the directory.
let private safeRelative (path: string) =
    path <> "" && not (Path.IsPathRooted path) && not (path.Split([| '/'; '\\' |]) |> Array.exists (fun part -> part = ".." || part = "."))

/// The files under a directory, by path with `/`: the disk a program starts from (at most 1000 files, 1 MB each, UTF-8).
let private loadDisk (dir: string) : Result<(string * string) list, string> =
    let root = Path.GetFullPath dir
    let all = Directory.GetFiles(root, "*", SearchOption.AllDirectories)
    if all.Length > 1000 then Result.Error("more than 1000 files under " + dir + ": give a smaller directory to --files")
    else
        let utf8 = Text.UTF8Encoding(false, true)
        let rows =
            [ for f in all ->
                  let rel = Path.GetRelativePath(root, f).Replace('\\', '/')
                  let info = FileInfo f
                  if info.Length > 1000000L then Result.Error(rel + " is larger than 1 MB")
                  else
                      try Ok(rel, utf8.GetString(File.ReadAllBytes f))
                      with _ -> Result.Error(rel + " is not UTF-8 text") ]
        match rows |> List.tryPick (function Result.Error e -> Some e | _ -> None) with
        | Some e -> Result.Error("cannot start from " + dir + ": " + e + " (put the files the program needs in a directory of their own)")
        | None -> Ok(rows |> List.choose (function Ok x -> Some x | _ -> None))

/// `quod run FILE`: check the program, then run `main` (capabilities in, capabilities out) with the evaluator.
/// The console is the standard input and output (the lines written are printed when the run ends); the files
/// are those under `--files DIR`, and what the program leaves is written back there when it ends.
/// The program is run as it is proved, with no Python or .NET involved.
let private runCommand (file: string) (o: Options) =
    withFile file (fun src ->
        match verifyFile file src o with
        | Result.Error code -> code
        | Ok(typed, result) ->
            let errors = Pipeline.errorsOf result
            let name = defaultArg o.Function "main"
            let capabilityName (t: Typed.Ty) = match t with Typed.TyData d when Capabilities.capabilityTypes.Contains d.DataName -> Some d.DataName | _ -> None
            if not errors.IsEmpty then
                Console.Error.WriteLine("rejected: " + Pipeline.summary result + "; the program is not run")
                1
            else
                match typed.Fns |> List.tryFind (fun f -> f.Name = name) with
                | None ->
                    Console.Error.WriteLine("error: " + file + " has no function '" + name + "' to run (quod run FILE [--function NAME] [--files DIR])")
                    2
                | Some f when not f.Params.IsEmpty && f.Params |> List.forall (fun p -> (capabilityName p.Ty).IsSome) && Capabilities.isCapability f.Ret ->
                    let wantsFiles = f.Params |> List.exists (fun p -> capabilityName p.Ty = Some Capabilities.filesType)
                    let disk =
                        match o.FilesDir with
                        | Some dir when wantsFiles ->
                            if Directory.Exists dir then loadDisk dir else Result.Error("no directory " + dir)
                        | _ when wantsFiles -> Result.Error("'" + name + "' takes a Files: say where they are with --files DIR (what it writes is written there)")
                        | _ -> Ok []
                    match disk with
                    | Result.Error why ->
                        Console.Error.WriteLine("error: " + why)
                        2
                    | Ok initial ->
                        // what the program reads is standard input, all of it up front (none when it is a terminal)
                        let input =
                            if Console.IsInputRedirected && f.Params |> List.exists (fun p -> capabilityName p.Ty = Some Capabilities.capabilityType) then
                                Console.In.ReadToEnd().Replace("\r\n", "\n").Split('\n')
                                |> Array.toList
                                |> (fun ls -> match List.rev ls with "" :: rest -> List.rev rest | _ -> ls)
                            else []
                        let start (p: Typed.TParam) =
                            match capabilityName p.Ty with
                            | Some n when n = Capabilities.filesType ->
                                let entries = initial |> List.fold (fun m (path, text) -> Eval.putEntry m (valueOfString path) (valueOfString text)) []
                                Eval.VData(n, [ Eval.VMap entries ])
                            | Some n -> Eval.VData(n, [ Eval.VSeq []; Eval.VSeq(input |> List.map valueOfString) ])
                            | None -> Eval.VBool false
                        let fns = typed.Fns |> List.map (fun g -> g.Name, g) |> Map.ofList
                        let ev = Eval.Evaluator(fns, false)
                        try
                            let out = Eval.withBigStack (fun () -> ev.Run(f, f.Params |> List.map start))
                            let parts = match out with Eval.VTuple xs -> xs | x -> [ x ]
                            // the files first, then what was said
                            let mutable code = 0
                            for part in parts do
                                match part with
                                | Eval.VData(n, [ Eval.VMap entries ]) when n = Capabilities.filesType ->
                                    let final = entries |> List.map (fun (k, v) -> stringOfValue k, stringOfValue v)
                                    let root = Path.GetFullPath o.FilesDir.Value
                                    let unsafe = final |> List.filter (fun (k, _) -> not (safeRelative k))
                                    if not unsafe.IsEmpty then
                                        Console.Error.WriteLine("error: the program names a path that leaves the directory: " + fst unsafe.Head)
                                        code <- 1
                                    else
                                        let before = Map.ofList initial
                                        let after = Map.ofList final
                                        let utf8 = Text.UTF8Encoding(false)
                                        for (k, v) in final do
                                            if before.TryFind k <> Some v then
                                                let full = Path.Combine(root, k)
                                                Directory.CreateDirectory(Path.GetDirectoryName full) |> ignore
                                                File.WriteAllText(full, v, utf8)
                                        for (k, _) in initial do
                                            if not (after.ContainsKey k) then File.Delete(Path.Combine(root, k))
                                | _ -> ()
                            for part in parts do
                                match part with
                                | Eval.VData(n, [ Eval.VSeq lines; _ ]) when n = Capabilities.capabilityType ->
                                    for line in lines do Console.WriteLine(stringOfValue line)
                                | _ -> ()
                            code
                        with
                        | Eval.Violation(label, _) ->
                            Console.Error.WriteLine("error: " + label + " fails while running '" + name + "'")
                            1
                        | Eval.CannotEvaluate why ->
                            Console.Error.WriteLine("error: cannot run '" + name + "': " + why)
                            1
                | Some _ ->
                    Console.Error.WriteLine("error: '" + name + "' must take capabilities and return them: fn " + name + "(c: console.Console, f: files.Files) -> (console.Console, files.Files)")
                    2)

[<EntryPoint>]
let main argv =
    let o, args = parseOptions (List.ofArray argv)
    match args with
    | [ "parse"; file ] -> parseCommand file o
    | [ "check"; file ] -> checkCommand file o
    | [ "build"; file ] -> buildCommand file o
    | [ "run"; file ] -> runCommand file o
    | [ "contract"; file; cases ] when o.Function.IsSome ->
        withFile file (fun src ->
            match Mcp.contractCases file src o.Function.Value (File.ReadAllText cases) with
            | Ok text ->
                Console.WriteLine text
                0
            | Result.Error why ->
                Console.Error.WriteLine("error: " + why)
                1)
    | [ "mcp" ] -> Mcp.serve (if o.BudgetGiven then o.Settings else { o.Settings with Budget = Mcp.defaultBudget })
    | "reference" :: title ->
        match Mcp.referenceText (if title.IsEmpty then None else Some(String.Join(" ", title))) with
        | Ok text ->
            Console.Write text
            0
        | Result.Error message ->
            Console.Error.WriteLine message
            2
    | [ "--version" ] ->
        Console.WriteLine("quod " + Diagnostics.quodVersion)
        0
    | _ ->
        Console.Error.WriteLine(usage)
        2
