# Prototype: F# + Native AOT + Z3

Question: can the Quod compiler be written in F# and shipped as a self-contained native binary
(no .NET runtime to install) that talks to Z3? Two ways were tried, with the same three checks:
a valid property (proved), a false one (refuted with a counterexample), and a Quod-style
completeness check (the contract `r >= x && r <= x + 1` admits two results: a witness).

Results (2026-10-22, Windows 11 x64, .NET 10 SDK, Visual Studio 2026 C++ tools):

| | A: official binding (`binding/`) | B: SMT-LIB to a `z3` process (`smtlib/`) |
|---|---|---|
| Shipped files | `Binding.exe` 2.3 MB + `libz3.dll` 16 MB | `SmtLib.exe` 2.6 MB + `z3.exe` 16.6 MB |
| AOT / trimming warnings | none | none |
| Time for the 3 checks | 67 ms | 134 ms (one process per check) |
| Results | correct | correct (SMT-LIB text answers) |
| Linux, macOS ARM | nuget.org `Microsoft.Z3` stops at 4.12.2 (2023), natives for win-x64 and osx-x64 only | official Z3 binaries for every platform |
| Solver hangs or crashes | take the compiler down | isolated, killable on timeout |
| Other solvers (cvc5) | no | yes, same SMT-LIB |
| Readable verification conditions | no | yes: text files, replayable with `z3` |

**Decision: B, SMT-LIB over a `z3` process**, kept alive for a whole compilation (`push` / `pop`)
so that the per-check process start-up disappears, as Boogie and Dafny do.

Build note: on Windows the Native AOT linker step needs `vswhere.exe` on `PATH`:

```powershell
$env:PATH = "${env:ProgramFiles(x86)}\Microsoft Visual Studio\Installer;" + $env:PATH
dotnet publish smtlib -c Release -r win-x64 -o out/smtlib
```

(The official Z3 5.3.1 .NET package is published on GitHub releases only, not on nuget.org.)
