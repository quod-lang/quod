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
    + "  mcp     serve check, build, run and the language reference to an AI agent (MCP, stdio)\n"
    + "options:\n"
    + "  --json              diagnostics as JSON\n"
    + "  --z3 PATH           the z3 executable (default: next to quod, $QUOD_Z3, then PATH)\n"
    + "  --timeout SECONDS   time limit per proof obligation (default 10)\n"
    + "  --budget SECONDS    time limit of the whole check (default 300, 0 for none): the obligations\n"
    + "                      left when it is used up are reported as not attempted\n"
    + "  --smt-log FILE      write every command sent to z3 to FILE\n"
    + "  --target python     code generation target (build; python is the only one in 0.1)\n"
    + "  -o DIR              output directory (build; default: next to FILE)\n"
    + "  --runtime-checks    build even if some proofs fail: their contracts become run-time\n"
    + "                      assertions (an underspecified contract still blocks the build)"

type private Options =
    { Json: bool
      Settings: Pipeline.Settings
      Target: string
      OutDir: string option
      RuntimeChecks: bool }

let private parseOptions (args: string list) : Options * string list =
    let rec go (o: Options) (rest: string list) (positional: string list) =
        let s = o.Settings
        match rest with
        | "--json" :: tl -> go { o with Json = true } tl positional
        | "--z3" :: p :: tl -> go { o with Settings = { s with Z3 = Some p } } tl positional
        | "--timeout" :: n :: tl -> go { o with Settings = { s with Timeout = int n } } tl positional
        | "--budget" :: n :: tl -> go { o with Settings = { s with Budget = int n } } tl positional
        | "--smt-log" :: p :: tl -> go { o with Settings = { s with SmtLog = Some p } } tl positional
        | "--target" :: t :: tl -> go { o with Target = t } tl positional
        | "-o" :: d :: tl -> go { o with OutDir = Some d } tl positional
        | "--runtime-checks" :: tl -> go { o with RuntimeChecks = true } tl positional
        | x :: tl -> go o tl (positional @ [ x ])
        | [] -> o, positional
    go { Json = false; Settings = Pipeline.defaultSettings; Target = "python"; OutDir = None; RuntimeChecks = false } args []

let private report (o: Options) (ds: Diagnostic list) =
    if o.Json then Console.WriteLine(toJson ds)
    else for d in ds do if d.Severity <> Info then Console.Error.WriteLine(toText d) // notes: in the summary

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
            report o [ d ]
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
    if o.Target <> "python" then
        Console.Error.WriteLine("error: unknown target '" + o.Target + "' (Quod 0.1 generates python only)")
        2
    else
        withFile file (fun src ->
            match verifyFile file src o with
            | Result.Error code -> code
            | Ok(typed, result) ->
                match Pipeline.generate file typed result o.RuntimeChecks with
                | Result.Error why ->
                    Console.Error.WriteLine why
                    1
                | Ok(code, unproved) ->
                    let dir = defaultArg o.OutDir (Path.GetDirectoryName(Path.GetFullPath file))
                    Directory.CreateDirectory dir |> ignore
                    let target = Path.Combine(dir, Path.GetFileNameWithoutExtension file + ".py")
                    File.WriteAllText(target, code)
                    if not o.Json then
                        Console.WriteLine("built " + target + " (" + Pipeline.summary result + ")")
                        if not unproved.IsEmpty then
                            Console.Error.WriteLine(
                                "warning: not fully proved, contracts checked at run time in: " + String.Join(", ", unproved))
                    0)

[<EntryPoint>]
let main argv =
    let o, args = parseOptions (List.ofArray argv)
    match args with
    | [ "parse"; file ] -> parseCommand file o
    | [ "check"; file ] -> checkCommand file o
    | [ "build"; file ] -> buildCommand file o
    | [ "mcp" ] -> Mcp.serve o.Settings
    | [ "--version" ] ->
        Console.WriteLine("quod " + Diagnostics.quodVersion)
        0
    | _ ->
        Console.Error.WriteLine(usage)
        2
