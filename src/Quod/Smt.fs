/// Talking to Z3: one persistent `z3 -in` process per compilation, driven in SMT-LIB text with
/// push/pop, plus a small S-expression reader for its answers (models, values).
module Quod.Smt

open System
open System.Diagnostics
open System.IO
open System.Text

// --- S-expressions --------------------------------------------------------------------

type SExpr =
    | Atom of string
    | List of SExpr list

let parseSExprs (text: string) : SExpr list =
    let mutable i = 0
    let n = text.Length
    let rec skip () =
        while i < n && Char.IsWhiteSpace text.[i] do
            i <- i + 1
        if i < n && text.[i] = ';' then
            while i < n && text.[i] <> '\n' do
                i <- i + 1
            skip ()
    let rec one () : SExpr =
        skip ()
        if text.[i] = '(' then
            i <- i + 1
            let items = ResizeArray<SExpr>()
            skip ()
            while i < n && text.[i] <> ')' do
                items.Add(one ())
                skip ()
            i <- i + 1
            List(List.ofSeq items)
        elif text.[i] = '"' then
            let start = i
            i <- i + 1
            while i < n && not (text.[i] = '"' && (i + 1 >= n || text.[i + 1] <> '"')) do
                i <- i + (if text.[i] = '"' then 2 else 1)
            i <- i + 1
            Atom(text.Substring(start, i - start))
        elif text.[i] = '|' then
            let start = i
            i <- i + 1
            while i < n && text.[i] <> '|' do
                i <- i + 1
            i <- i + 1
            Atom(text.Substring(start + 1, i - start - 2))
        else
            let start = i
            while i < n && not (Char.IsWhiteSpace text.[i]) && text.[i] <> '(' && text.[i] <> ')' do
                i <- i + 1
            Atom(text.Substring(start, i - start))
    let out = ResizeArray<SExpr>()
    skip ()
    while i < n do
        out.Add(one ())
        skip ()
    List.ofSeq out

let rec sexprText (e: SExpr) =
    match e with
    | Atom a -> a
    | List xs -> "(" + (xs |> List.map sexprText |> String.concat " ") + ")"

// --- the Z3 process -------------------------------------------------------------------

type CheckResult =
    | Sat
    | Unsat
    | Unknown of reason: string

exception SmtFailure of string

/// Where to find z3: an explicit path, next to the quod binary, QUOD_Z3, then PATH.
let findZ3 (explicitPath: string option) : string option =
    let exe = if OperatingSystem.IsWindows() then "z3.exe" else "z3"
    let candidates =
        [ yield! Option.toList explicitPath
          yield Path.Combine(AppContext.BaseDirectory, exe)
          match Environment.GetEnvironmentVariable "QUOD_Z3" with
          | null | "" -> ()
          | p -> yield p
          match Environment.GetEnvironmentVariable "PATH" with
          | null -> ()
          | path ->
              for dir in path.Split(Path.PathSeparator) do
                  if dir <> "" then yield Path.Combine(dir, exe) ]
    candidates |> List.tryFind File.Exists

/// A running `z3 -in` process. Commands are written as SMT-LIB text; answers are read back
/// as balanced S-expressions. `log` receives every command, to replay a session by hand.
type Session(z3Path: string, timeoutMs: int, log: TextWriter option) =
    let psi = ProcessStartInfo(z3Path, "-in -smt2")
    do
        psi.RedirectStandardInput <- true
        psi.RedirectStandardOutput <- true
        psi.RedirectStandardError <- true
        psi.UseShellExecute <- false
    let proc = Process.Start psi
    let input = proc.StandardInput
    let output = proc.StandardOutput

    /// Read one complete answer: an atom line, or a parenthesised block spanning lines.
    let readAnswer () : string =
        let sb = StringBuilder()
        let mutable depth = 0
        let mutable started = false
        let mutable fin = false
        while not fin do
            let line = output.ReadLine()
            if isNull line then raise (SmtFailure("z3 stopped unexpectedly: " + proc.StandardError.ReadToEnd()))
            let t = line.Trim()
            if t <> "" then
                sb.AppendLine(line) |> ignore
                for ch in line do
                    if ch = '(' then
                        depth <- depth + 1
                        started <- true
                    elif ch = ')' then depth <- depth - 1
                if depth <= 0 then fin <- true
        let answer = sb.ToString().Trim()
        if answer.StartsWith "(error" then raise (SmtFailure("z3 rejected a command: " + answer))
        answer

    do
        input.AutoFlush <- false

    member _.Send(command: string) =
        log |> Option.iter (fun w -> w.WriteLine command)
        input.WriteLine command

    member s.Init() =
        s.Send "(set-option :print-success false)"
        s.Send "(set-option :produce-models true)"
        // As Dafny does: quantifiers are instantiated by their triggers only (no model-based
        // instantiation). A failing check then answers "unknown" quickly, with a candidate
        // model, instead of searching for an exact model until the time limit.
        s.Send "(set-option :smt.mbqi false)"
        s.Send("(set-option :timeout " + string timeoutMs + ")")
        s.Send "(set-logic ALL)"

    /// Change the time limit of the following checks (milliseconds).
    member s.SetTimeout(ms: int) = s.Send("(set-option :timeout " + string ms + ")")

    /// The time limit given at start, to restore after a temporary change.
    member _.DefaultTimeout = timeoutMs

    member s.Push() = s.Send "(push 1)"
    member s.Pop() = s.Send "(pop 1)"

    member s.Check() : CheckResult =
        s.Send "(check-sat)"
        input.Flush()
        match readAnswer () with
        | "sat" -> Sat
        | "unsat" -> Unsat
        | "unknown" ->
            s.Send "(get-info :reason-unknown)"
            input.Flush()
            let r = readAnswer ()
            Unknown(if r.Contains "timeout" || r.Contains "canceled" then "timeout" else r)
        | other -> raise (SmtFailure("unexpected answer from z3: " + other))

    /// Values of terms in the current model, as S-expressions.
    member s.Values(terms: string list) : SExpr list =
        if terms.IsEmpty then []
        else
            s.Send("(get-value (" + String.Join(" ", terms) + "))")
            input.Flush()
            try
                match parseSExprs (readAnswer ()) with
                | [ List pairs ] -> pairs |> List.map (function List [ _; v ] -> v | other -> other)
                | _ -> []
            with SmtFailure _ -> [] // no model available (e.g. after a timeout)

    interface IDisposable with
        member s.Dispose() =
            try
                s.Send "(exit)"
                input.Flush()
                if not (proc.WaitForExit 2000) then proc.Kill()
            with _ -> ()
            proc.Dispose()
