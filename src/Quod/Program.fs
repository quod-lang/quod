/// The `quod` command line. Step 1 of 0.1: `quod parse` (later: `check`, `build`).
module Quod.Program

open System
open System.IO
open Quod.Diagnostics

let private usage =
    "usage: quod parse FILE [--json]\n"
    + "  parse   read FILE, report the first syntax error, or print the program back"

let private parseCommand (file: string) (json: bool) =
    if not (File.Exists file) then
        Console.Error.WriteLine("error: " + file + " not found")
        2
    else
        try
            let program = Parser.parseProgram file (File.ReadAllText file)
            if json then Console.WriteLine(toJson []) else Console.Write(Printer.programText program)
            0
        with QuodError d ->
            if json then Console.WriteLine(toJson [ d ]) else Console.Error.WriteLine(toText d)
            1

[<EntryPoint>]
let main argv =
    let args = List.ofArray argv
    let json = List.contains "--json" args
    match args |> List.filter (fun a -> a <> "--json") with
    | [ "parse"; file ] -> parseCommand file json
    | [ "--version" ] ->
        Console.WriteLine("quod 0.1.0-dev")
        0
    | _ ->
        Console.Error.WriteLine(usage)
        2
