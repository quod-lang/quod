# Quod.Build

Verifies the `.quod` files of a project and compiles them with it. A proof that fails makes the build
fail, and its message appears in the error list of Visual Studio.

```xml
<ItemGroup>
  <PackageReference Include="Quod.Build" Version="..." PrivateAssets="all" />
  <QuodCompile Include="Rules\**\*.quod" />
</ItemGroup>
```

Each file becomes a class, `Rules.quod` giving `Rules`, whose public methods can be called from C#. A module a file imports is compiled with it, and changing it verifies again, even if it is not listed. Each listed file verifies what it imports, so a module shared by several is proved several times. The
generated code stays within C# 7.3 and the standard library, for .NET Framework 4.7.2 as for .NET Core.
quod and z3 come with the package; the build runs on Windows x64, Linux x64 and macOS on Apple silicon.

| Property | Default | |
|---|---|---|
| `QuodNamespace` | `$(RootNamespace)` | The namespace of the generated classes |
| `QuodRequireContracts` | `false` | A function without a contract is an error |
| `QuodCheckAllRequires` | `false` | Public methods also check their quantified `requires`; defining `QUOD_CHECK_REQUIRES` does the same without generating again |
| `QuodBudget` | `300` | Seconds for the check of one file |
| `QuodBuildOptions` | | Other options of `quod build` |

An unchanged file is not verified again. Diagnostics have the codes `QUOD0001` (syntax), `QUOD0002` (type),
`QUOD0003` (proof), `QUOD0004` (completeness), `QUOD0005` (contract) and `QUOD0006` (`loose`), which `NoWarn` and
`WarningsAsErrors` understand. **A caller in C# proves nothing:** read in the comment of each method which
`requires` it leaves to its callers.
