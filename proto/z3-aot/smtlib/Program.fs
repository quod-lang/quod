// Prototype B: Z3 as a separate process, spoken to in SMT-LIB text (as Boogie/Dafny do),
// compiled with Native AOT. Same three checks as prototype A. No Z3 library is linked: the
// compiler only needs a `z3` executable (next to it, in QUOD_Z3, or on PATH).
open System
open System.Diagnostics
open System.IO

let findZ3 () =
    let here = AppContext.BaseDirectory
    let candidates =
        [ Environment.GetEnvironmentVariable("QUOD_Z3")
          Path.Combine(here, "z3.exe")
          Path.Combine(here, "z3") ]
    match candidates |> List.tryFind (fun p -> not (String.IsNullOrEmpty p) && File.Exists p) with
    | Some p -> p
    | None -> "z3" // rely on PATH

/// Run one SMT-LIB script through `z3 -in` and return its output lines.
let runZ3 (z3: string) (script: string) =
    let psi = ProcessStartInfo(z3, "-in -smt2")
    psi.RedirectStandardInput <- true
    psi.RedirectStandardOutput <- true
    psi.UseShellExecute <- false
    use p = Process.Start(psi)
    p.StandardInput.Write(script)
    p.StandardInput.Close()
    let out = p.StandardOutput.ReadToEnd()
    p.WaitForExit()
    out.Split([| '\n' |], StringSplitOptions.RemoveEmptyEntries) |> Array.map (fun l -> l.Trim())

/// Prove `goal` (an SMT-LIB term) over integer constants `vars`, showing them on refutation.
let prove z3 (name: string) (vars: string list) (goal: string) =
    let decls = vars |> List.map (fun v -> "(declare-const " + v + " Int)") |> String.concat "\n"
    let script =
        decls + "\n(assert (not " + goal + "))\n(check-sat)\n"
        + "(get-value (" + String.Join(" ", vars) + "))\n"
    let lines = runZ3 z3 script
    match lines |> Array.tryHead with
    | Some "unsat" -> Console.WriteLine(name + ": proved")
    | Some "sat" ->
        // get-value answers ((x 1) (r1 0) ...): keep it as printed, one line.
        let model = String.Join(" ", lines |> Array.skip 1)
        Console.WriteLine(name + ": refuted, counterexample " + model)
    | other -> Console.WriteLine(name + ": unexpected answer " + String.Join(" | ", lines))

[<EntryPoint>]
let main _ =
    let clock = Stopwatch.StartNew()
    let z3 = findZ3 ()
    prove z3 "x > 0 ==> x + x > x" [ "x" ] "(=> (> x 0) (> (+ x x) x))"
    prove z3 "x + 1 > 2 * x" [ "x" ] "(> (+ x 1) (* 2 x))"
    let ensures r = "(and (>= " + r + " x) (<= " + r + " (+ x 1)))"
    prove z3 "uniqueness of (r >= x && r <= x + 1)" [ "x"; "r1"; "r2" ]
        ("(=> (and " + ensures "r1" + " " + ensures "r2" + ") (= r1 r2))")
    Console.WriteLine("z3 at " + z3 + ", total " + string clock.ElapsedMilliseconds + " ms")
    0
