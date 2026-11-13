/// Capabilities (design note capacites.fr.md): a function writes to the console only through a
/// `console.Console` it receives. The model is the list of the lines written, which contracts read as
/// `console.written(c)`; for that model to be true of the real console, a capability is used once
/// (each operation hands back the next one), cannot be built by a program, and cannot be read in code.
/// The module `console` of the standard library is trusted: its own functions are not checked.
module Quod.Capabilities

open Quod.Syntax
open Quod.Typed
open Quod.Diagnostics

/// The console, by its flattened name.
let capabilityType = "console.Console"

/// The files, by their flattened name.
let filesType = "files.Files"

/// Every capability type: a struct of a module of the standard library, which only that module builds.
let capabilityTypes = set [ capabilityType; filesType ]

/// The functions that read the model: contracts only.
let private modelFunctions = set [ "console.written"; "console.pending"; "files.contents" ]

let private isCapabilityData (t: Ty) = match t with TyData d -> capabilityTypes.Contains d.DataName | _ -> false

/// Is a capability held by a value of this type (itself, or a tuple that holds one)?
let rec isCapability (t: Ty) =
    match t with
    | TyData d -> capabilityTypes.Contains d.DataName
    | TyTuple ts -> List.exists isCapability ts
    | _ -> false

/// A type that keeps a capability where it could be copied or forgotten: a collection, a type argument, a field.
let rec private storesCapability (t: Ty) =
    match t with
    | TySeq e | TySet e -> isCapability e || storesCapability e
    | TyMap(k, v) -> isCapability k || isCapability v || storesCapability k || storesCapability v
    | TyTuple ts -> ts |> List.exists storesCapability
    | TyData d when capabilityTypes.Contains d.DataName -> false
    | TyData d -> d.TypeArgs |> List.exists (fun a -> isCapability a || storesCapability a)
    | _ -> false

let private inModule (name: string) = name.StartsWith "console." || name.StartsWith "files."

let private children (e: TExpr) : TExpr list =
    match e.Kind with
    | EInt _ | EBool _ | EVar _ | EResult -> []
    | ESeq xs | ETuple xs | ECons(_, xs) | ECol(_, xs) | ECall(_, xs) -> xs
    | EIndex(a, b) | EConcat(a, b) | EArith(_, a, b) | ECmp(_, a, b) | EEq(a, b) | ELogic(_, a, b) -> [ a; b ]
    | ESlice(s, lo, hi) -> s :: Option.toList lo @ Option.toList hi
    | EProj(x, _) | EField(x, _, _) | ELen x | ENeg x | ENot x | EToNat x | EConvert x -> [ x ]
    | EQuantIn(_, _, c, b) -> [ c; b ]
    | EQuant(_, _, lo, hi, b) -> [ lo; hi; b ]
    | EIf(c, a, b) -> [ c; a; b ]
    | EMatch(x, arms) -> x :: (arms |> List.map (fun (_, _, b) -> b))

/// The errors about the capabilities of a checked program.
let check (file: string) (prog: TProgram) : Diagnostic list =
    let errors = ResizeArray<Diagnostic>()
    let error (fn: string) (span: Span) (message: string) =
        errors.Add { File = file; Span = span; Kind = "type"; Status = "error"; Severity = Error; Fn = Some fn
                     Property = None; Counterexample = []; Reason = None; Evidence = None; Message = message }
    // a capability is kept nowhere but in a variable, a parameter, a result or a tuple
    for d in prog.Types do
        if not (capabilityTypes.Contains d.DataName) && d.DataCases |> List.exists (fun c -> c.Fields |> List.exists (fun (_, t) -> isCapability t || storesCapability t)) then
            let span = { Start = { Line = 1; Col = 1 }; End = { Line = 1; Col = 1 } }
            error d.DataName span ("'" + d.DataName + "' holds a Console in a field: a Console is passed and returned, not stored")
    for f in prog.Fns do
        if not (inModule f.Name) && not f.IsLemma then
            let fn = f.Name
            let consumed: Set<string> ref = ref Set.empty
            let dead = ref false
            // the types
            for p in f.Params do
                if storesCapability p.Ty then error fn p.Span "a Console cannot be put in a sequence, a map, a set or a type argument: it is passed and returned"
            if storesCapability f.Ret then error fn f.Span "a Console cannot be put in a sequence, a map, a set or a type argument: it is passed and returned"
            let taken (key: string) =
                let whole = key.Split('.').[0]
                consumed.Value |> Set.exists (fun k -> k = key || k = whole || k.StartsWith(key + "."))
            let take (key: string) (span: Span) =
                if taken key then
                    error fn span ("'" + key + "' is a Console that has already been used: a Console is used once, so go on with the one that the previous call returned, as in 'let c2 = console.say(c, ...)'")
                consumed.Value <- consumed.Value.Add key
            let release (name: string) =
                consumed.Value <- consumed.Value |> Set.filter (fun k -> k <> name && not (k.StartsWith(name + ".")))
            // one branch among several: what is used in any is used after, and a branch that returns counts for nothing
            let join (states: (Set<string> * bool) list) =
                let live = states |> List.filter (fun (_, d) -> not d)
                if live.IsEmpty then dead.Value <- true
                else
                    dead.Value <- false
                    consumed.Value <- live |> List.map fst |> Set.unionMany
            let rec code (e: TExpr) =
                match e.Kind with
                | EVar n when isCapability e.Ty -> take n e.Span
                | EProj({ Kind = EVar n; Ty = TyTuple ts }, k) when isCapability (TyTuple ts) ->
                    if isCapability ts.[k] then take (n + "." + string k) e.Span
                    elif consumed.Value.Contains n then error fn e.Span ("'" + n + "' has already been used")
                | ECall(name, args) when modelFunctions.Contains name ->
                    error fn e.Span ("'" + name + "' reads the model of a capability, for contracts: code cannot read it (what was written, what is left to read, what the files hold)")
                    ignore args
                | ECons(_, args) when isCapabilityData e.Ty ->
                    error fn e.Span "a capability (a Console, a Files) cannot be built: a program receives it, from whoever runs it"
                    ignore args
                | EField(x, _, _) when isCapabilityData x.Ty ->
                    error fn e.Span "the model of a capability (the lines of a Console, the files of a Files) is read in contracts, with console.written(c) or files.contents(f); code cannot read it"
                | EIf(c, a, b) ->
                    code c
                    let start = consumed.Value
                    code a
                    let sa = consumed.Value
                    consumed.Value <- start
                    code b
                    join [ sa, false; consumed.Value, false ]
                | EMatch(x, arms) ->
                    code x
                    let start = consumed.Value
                    let states =
                        [ for _, _, b in arms do
                              consumed.Value <- start
                              code b
                              yield consumed.Value, false ]
                    join states
                | _ -> for c in children e do code c
            let rec stmts (items: TStmt list) =
                for s in items do
                    if not dead.Value then stmt s
            and stmt (s: TStmt) =
                match s.Kind with
                | SLet(_, n, _, _) when isLemmaBinding n -> ()
                | SLet(_, n, ty, v) ->
                    if storesCapability ty then error fn s.Span "a Console cannot be put in a sequence, a map, a set or a type argument: it is passed and returned"
                    code v
                    release n
                | SAssign(n, v) ->
                    code v
                    release n
                | SIf(c, a, b) ->
                    code c
                    let start = consumed.Value
                    stmts a
                    let sa = consumed.Value, dead.Value
                    dead.Value <- false
                    consumed.Value <- start
                    stmts b
                    let sb = consumed.Value, dead.Value
                    join [ sa; sb ]
                | SWhile(c, _, _, body) ->
                    let entry = consumed.Value
                    code c
                    let afterTest = consumed.Value
                    stmts body
                    if not dead.Value && not (Set.isSubset consumed.Value entry) then
                        error fn s.Span "this loop uses a Console and does not hand it back: end the body by assigning the Console it went on with (c = ...), so that each turn starts with a Console that can be used"
                    dead.Value <- false
                    consumed.Value <- afterTest
                | SAssert _ -> ()
                | SReturn e ->
                    code e
                    dead.Value <- true
            match f.Body with
            | TExprBody e -> code e
            | TStmtBody items -> stmts items
    List.ofSeq errors

// --- the module `console` in the generated code -------------------------------------------------
// Not generated from stdlib/console.quod: there a Console is a list of lines, the model; in the code
// it writes to a stream. What the proofs say of `say` (one more line written) is what this does.

/// console.py: `Console()` writes to the standard output, `Console(stream)` to any text stream.
let pythonRuntime =
    String.concat "\n"
        [ "# Written by quod, with the program: the console capability (stdlib/console.quod). Not generated from Quod."
          "from __future__ import annotations"
          ""
          "import sys as _quod_sys"
          ""
          ""
          "import option as _quod_option"
          ""
          ""
          "class Console:"
          "    \"\"\"Where a program writes and reads. Console() is the standard output and input; Console(stream, source),"
          "    any text streams (a test gives io.StringIO objects). say(c, line) and read_line(c) return the same"
          "    Console: the proofs call it the next one, because a Console is used once.\"\"\""
          ""
          "    def __init__(self, stream=None, source=None):"
          "        self._stream = _quod_sys.stdout if stream is None else stream"
          "        self._source = _quod_sys.stdin if source is None else source"
          ""
          ""
          "def say(c: Console, line: str) -> Console:"
          "    if not isinstance(c, Console):"
          "        raise TypeError(\"a Console is expected\")"
          "    if not isinstance(line, str):"
          "        raise TypeError(\"a string is expected, not \" + type(line).__name__)"
          "    c._stream.write(line + \"\\n\")"
          "    return c"
          ""
          ""
          "def read_line(c: Console):"
          "    if not isinstance(c, Console):"
          "        raise TypeError(\"a Console is expected\")"
          "    line = c._source.readline()"
          "    if line == \"\":"
          "        return (c, _quod_option.Option__string_None())"
          "    if line.endswith(\"\\n\"):"
          "        line = line[:-1]"
          "    if line.endswith(\"\\r\"):"
          "        line = line[:-1]"
          "    return (c, _quod_option.Option__string_Some(line))"
          ""
          ""
          "__all__ = [\"Console\", \"say\", \"read_line\"]"
          "" ]

/// ConsoleModule.cs, in the namespace of the program: `new ConsoleModule.Console()` writes to the standard
/// output, `new ConsoleModule.Console(writer)` to any TextWriter (a test gives a StringWriter).
let csharpRuntime (ns: string) =
    String.concat "\n"
        [ "// Written by quod, with the program: the console capability (stdlib/console.quod). Not generated from Quod."
          "#pragma warning disable"
          "using System;"
          "using System.Collections.Generic;"
          "using System.IO;"
          ""
          "namespace " + ns
          "{"
          "    public static class ConsoleModule"
          "    {"
          "        /// <summary>Where a program writes and reads. Say and ReadLine return the same Console: the proofs call it the next one, because a Console is used once.</summary>"
          "        public sealed class Console"
          "        {"
          "            internal readonly TextWriter _out;"
          "            internal readonly TextReader _in;"
          ""
          "            public Console() : this(System.Console.Out, System.Console.In) { }"
          ""
          "            public Console(TextWriter output) : this(output, System.Console.In) { }"
          ""
          "            public Console(TextWriter output, TextReader input)"
          "            {"
          "                if (output == null) throw new ArgumentNullException(\"output\");"
          "                if (input == null) throw new ArgumentNullException(\"input\");"
          "                _out = output;"
          "                _in = input;"
          "            }"
          "        }"
          ""
          "        public static Console Say(Console c, string line)"
          "        {"
          "            if (c == null) throw new ArgumentNullException(\"c\");"
          "            if (line == null) throw new ArgumentNullException(\"line\");"
          "            c._out.WriteLine(line);"
          "            return c;"
          "        }"
          ""
          "        internal static Console _quod_pub_say(Console c, IReadOnlyList<int> line)"
          "        {"
          "            if (c == null) throw new ArgumentNullException(\"c\");"
          "            if (line == null) throw new ArgumentNullException(\"line\");"
          "            var b = new System.Text.StringBuilder(line.Count);"
          "            for (int i = 0; i < line.Count; i++) b.Append(char.ConvertFromUtf32(line[i]));"
          "            c._out.WriteLine(b.ToString());"
          "            return c;"
          "        }"
          ""
          "        /// <summary>The next line and the console that follows; None when there is nothing left to read.</summary>"
          "        public static (Console, Option.Option_string) ReadLine(Console c)"
          "        {"
          "            if (c == null) throw new ArgumentNullException(\"c\");"
          "            string line = c._in.ReadLine();"
          "            if (line == null) return (c, new Option.Option_string.None());"
          "            return (c, new Option.Option_string.Some(line));"
          "        }"
          ""
          "        internal static (Console, Option.Option_string) _quod_pub_read_line(Console c)"
          "        {"
          "            return ReadLine(c);"
          "        }"
          "    }"
          "}"
          "" ]

/// files.py: `Files(root)` reads and writes the files under `root` (the current directory by default), as UTF-8 text
/// without any change of the line ends. A path that is empty, absolute or that leaves the root is refused (ValueError).
let pythonFilesRuntime =
    String.concat "\n"
        [ "# Written by quod, with the program: the files capability (stdlib/files.quod). Not generated from Quod."
          "from __future__ import annotations"
          ""
          "import os as _quod_os"
          "import option as _quod_option"
          ""
          ""
          "class Files:"
          "    \"\"\"The files under a directory. Files(root) is rooted there; a path that leaves the root is refused."
          "    The functions return the same Files: the proofs call it the next one, because a Files is used once.\"\"\""
          ""
          "    def __init__(self, root=\".\"):"
          "        self._root = _quod_os.path.abspath(root)"
          ""
          "    def _resolve(self, path):"
          "        if not isinstance(path, str):"
          "            raise TypeError(\"a string is expected, not \" + type(path).__name__)"
          "        full = _quod_os.path.abspath(_quod_os.path.join(self._root, path))"
          "        try:"
          "            inside = path != \"\" and not _quod_os.path.isabs(path) and _quod_os.path.commonpath([self._root, full]) == self._root and full != self._root"
          "        except ValueError:"
          "            inside = False"
          "        if not inside:"
          "            raise ValueError(\"the path \" + repr(path) + \" is not a file under the root of this Files\")"
          "        return full"
          ""
          ""
          "def read_file(f: Files, path: str):"
          "    if not isinstance(f, Files):"
          "        raise TypeError(\"a Files is expected\")"
          "    full = f._resolve(path)"
          "    if not _quod_os.path.isfile(full):"
          "        return (f, _quod_option.Option__string_None())"
          "    with open(full, encoding=\"utf-8\", newline=\"\") as handle:"
          "        return (f, _quod_option.Option__string_Some(handle.read()))"
          ""
          ""
          "def write_file(f: Files, path: str, text: str) -> Files:"
          "    if not isinstance(f, Files):"
          "        raise TypeError(\"a Files is expected\")"
          "    if not isinstance(text, str):"
          "        raise TypeError(\"a string is expected, not \" + type(text).__name__)"
          "    full = f._resolve(path)"
          "    _quod_os.makedirs(_quod_os.path.dirname(full), exist_ok=True)"
          "    with open(full, \"w\", encoding=\"utf-8\", newline=\"\") as handle:"
          "        handle.write(text)"
          "    return f"
          ""
          ""
          "def delete_file(f: Files, path: str) -> Files:"
          "    if not isinstance(f, Files):"
          "        raise TypeError(\"a Files is expected\")"
          "    full = f._resolve(path)"
          "    if _quod_os.path.isfile(full):"
          "        _quod_os.remove(full)"
          "    return f"
          ""
          ""
          "__all__ = [\"Files\", \"read_file\", \"write_file\", \"delete_file\"]"
          "" ]

/// FilesModule.cs, in the namespace of the program: `new FilesModule.Files(root)`.
let csharpFilesRuntime (ns: string) =
    String.concat "\n"
        [ "// Written by quod, with the program: the files capability (stdlib/files.quod). Not generated from Quod."
          "#pragma warning disable"
          "using System;"
          "using System.Collections.Generic;"
          "using System.IO;"
          "using System.Text;"
          ""
          "namespace " + ns
          "{"
          "    public static class FilesModule"
          "    {"
          "        /// <summary>The files under a directory, read and written as UTF-8 text. A path that is empty, rooted or that leaves the directory is refused (ArgumentException). The functions return the same Files: the proofs call it the next one, because a Files is used once.</summary>"
          "        public sealed class Files"
          "        {"
          "            private readonly string _root;"
          ""
          "            public Files() : this(\".\") { }"
          ""
          "            public Files(string root)"
          "            {"
          "                if (root == null) throw new ArgumentNullException(\"root\");"
          "                _root = Path.GetFullPath(root).TrimEnd(Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar);"
          "            }"
          ""
          "            internal string _resolve(string path)"
          "            {"
          "                if (path == null) throw new ArgumentNullException(\"path\");"
          "                if (path.Length == 0 || Path.IsPathRooted(path)) throw new ArgumentException(\"the path '\" + path + \"' is not a file under the root of this Files\");"
          "                string full = Path.GetFullPath(Path.Combine(_root, path));"
          "                if (!full.StartsWith(_root + Path.DirectorySeparatorChar, StringComparison.Ordinal)) throw new ArgumentException(\"the path '\" + path + \"' is not a file under the root of this Files\");"
          "                return full;"
          "            }"
          "        }"
          ""
          "        private static string _text(IReadOnlyList<int> xs)"
          "        {"
          "            if (xs == null) throw new ArgumentNullException(\"xs\");"
          "            var b = new StringBuilder(xs.Count);"
          "            for (int i = 0; i < xs.Count; i++) b.Append(char.ConvertFromUtf32(xs[i]));"
          "            return b.ToString();"
          "        }"
          ""
          "        /// <summary>The text of a file, or None if there is no such file; the Files that follows.</summary>"
          "        public static (Files, Option.Option_string) ReadFile(Files f, string path)"
          "        {"
          "            if (f == null) throw new ArgumentNullException(\"f\");"
          "            string full = f._resolve(path);"
          "            if (!File.Exists(full)) return (f, new Option.Option_string.None());"
          "            return (f, new Option.Option_string.Some(File.ReadAllText(full, new UTF8Encoding(false, true))));"
          "        }"
          ""
          "        /// <summary>The Files, with the text written at the path (the file is created, or replaced).</summary>"
          "        public static Files WriteFile(Files f, string path, string text)"
          "        {"
          "            if (f == null) throw new ArgumentNullException(\"f\");"
          "            if (text == null) throw new ArgumentNullException(\"text\");"
          "            string full = f._resolve(path);"
          "            Directory.CreateDirectory(Path.GetDirectoryName(full));"
          "            File.WriteAllText(full, text, new UTF8Encoding(false));"
          "            return f;"
          "        }"
          ""
          "        /// <summary>The Files, without the file (nothing happens if there was none).</summary>"
          "        public static Files DeleteFile(Files f, string path)"
          "        {"
          "            if (f == null) throw new ArgumentNullException(\"f\");"
          "            string full = f._resolve(path);"
          "            if (File.Exists(full)) File.Delete(full);"
          "            return f;"
          "        }"
          ""
          "        internal static (Files, Option.Option_string) _quod_pub_read_file(Files f, IReadOnlyList<int> path) { return ReadFile(f, _text(path)); }"
          "        internal static Files _quod_pub_write_file(Files f, IReadOnlyList<int> path, IReadOnlyList<int> text) { return WriteFile(f, _text(path), _text(text)); }"
          "        internal static Files _quod_pub_delete_file(Files f, IReadOnlyList<int> path) { return DeleteFile(f, _text(path)); }"
          "    }"
          "}"
          "" ]
