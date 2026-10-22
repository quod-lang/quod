/// The `quod` command line. 0.1 in progress: `parse`, `check` (types only so far), later `build`.
module Quod.Program

open System
open System.IO
open Quod.Diagnostics

let private usage =
    "usage: quod <command> FILE [--json]\n"
    + "  parse   read FILE, report the first syntax error, or print the program back\n"
    + "  check   parse and type-check FILE (proofs are not implemented yet)"

let private report (json: bool) (ds: Diagnostic list) =
    if json then Console.WriteLine(toJson ds)
    else for d in ds do Console.Error.WriteLine(toText d)

let private withFile (file: string) (action: string -> int) =
    if File.Exists file then action (File.ReadAllText file)
    else
        Console.Error.WriteLine("error: " + file + " not found")
        2

let private parseCommand (file: string) (json: bool) =
    withFile file (fun src ->
        try
            let program = Parser.parseProgram file src
            if json then report true [] else Console.Write(Printer.programText program)
            0
        with QuodError d ->
            report json [ d ]
            1)

let private checkCommand (file: string) (json: bool) =
    withFile file (fun src ->
        try
            let program = Parser.parseProgram file src
            let typed, errors = Typecheck.check file program
            report json errors
            if errors.IsEmpty then
                if not json then
                    Console.WriteLine(
                        "types ok: " + string typed.Fns.Length + " function(s). "
                        + "Contracts are NOT proved yet: verification comes with the next step of 0.1.")
                0
            else 1
        with QuodError d ->
            report json [ d ]
            1)

[<EntryPoint>]
let main argv =
    let args = List.ofArray argv
    let json = List.contains "--json" args
    match args |> List.filter (fun a -> a <> "--json") with
    | [ "parse"; file ] -> parseCommand file json
    | [ "check"; file ] -> checkCommand file json
    | [ "--version" ] ->
        Console.WriteLine("quod 0.1.0-dev")
        0
    | _ ->
        Console.Error.WriteLine(usage)
        2
