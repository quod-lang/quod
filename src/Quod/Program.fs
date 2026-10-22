/// The `quod` command line. 0.1 in progress: `parse`, `check` (types and proofs), later `build`.
module Quod.Program

open System
open System.IO
open Quod.Diagnostics

let private usage =
    "usage: quod <command> FILE [options]\n"
    + "  parse   read FILE, report the first syntax error, or print the program back\n"
    + "  check   parse, type-check and prove FILE\n"
    + "options:\n"
    + "  --json              diagnostics as JSON\n"
    + "  --z3 PATH           the z3 executable (default: next to quod, $QUOD_Z3, then PATH)\n"
    + "  --timeout SECONDS   time limit per proof obligation (default 10)\n"
    + "  --smt-log FILE      write every command sent to z3 to FILE"

type private Options =
    { Json: bool
      Z3: string option
      Timeout: int
      SmtLog: string option }

let private parseOptions (args: string list) : Options * string list =
    let rec go (o: Options) (rest: string list) (positional: string list) =
        match rest with
        | "--json" :: tl -> go { o with Json = true } tl positional
        | "--z3" :: p :: tl -> go { o with Z3 = Some p } tl positional
        | "--timeout" :: s :: tl -> go { o with Timeout = int s } tl positional
        | "--smt-log" :: p :: tl -> go { o with SmtLog = Some p } tl positional
        | x :: tl -> go o tl (positional @ [ x ])
        | [] -> o, positional
    go { Json = false; Z3 = None; Timeout = 10; SmtLog = None } args []

let private report (o: Options) (ds: Diagnostic list) =
    if o.Json then Console.WriteLine(toJson ds)
    else for d in ds do Console.Error.WriteLine(toText d)

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

let private checkCommand (file: string) (o: Options) =
    withFile file (fun src ->
        try
            let program = Parser.parseProgram file src
            let typed, typeErrors = Typecheck.check file program
            if not typeErrors.IsEmpty then
                report o typeErrors
                1
            else
                match Smt.findZ3 o.Z3 with
                | None ->
                    Console.Error.WriteLine("error: z3 not found; put it next to quod, set QUOD_Z3, or pass --z3 PATH")
                    2
                | Some z3Path ->
                    use logWriter = (match o.SmtLog with Some p -> new StreamWriter(p) | None -> null)
                    let log = if isNull logWriter then None else Some(logWriter :> TextWriter)
                    use session = new Smt.Session(z3Path, o.Timeout * 1000, log)
                    let result = Vcgen.verify file typed session
                    report o result.Diagnostics
                    if not o.Json then
                        if result.Diagnostics.IsEmpty then
                            Console.WriteLine(
                                "verified: " + string typed.Fns.Length + " function(s), "
                                + string result.Proved + " proof obligation(s) proved")
                        else
                            Console.Error.WriteLine(
                                string result.Diagnostics.Length + " proof obligation(s) failed, "
                                + string result.Proved + " proved")
                    if result.Diagnostics.IsEmpty then 0 else 1
        with
        | QuodError d ->
            report o [ d ]
            1
        | Smt.SmtFailure message ->
            Console.Error.WriteLine("internal error while talking to z3: " + message)
            3)

[<EntryPoint>]
let main argv =
    let o, args = parseOptions (List.ofArray argv)
    match args with
    | [ "parse"; file ] -> parseCommand file o
    | [ "check"; file ] -> checkCommand file o
    | [ "--version" ] ->
        Console.WriteLine("quod 0.1.0-dev")
        0
    | _ ->
        Console.Error.WriteLine(usage)
        2
