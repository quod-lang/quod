"""Test the Quod.Build package in real projects, in a directory whose name has a space:

    python packaging/test_package.py --package Quod.Build.X.nupkg --version X

An SDK project on .NET, one on .NET Framework 4.7.2, and an old-style one with packages.config under
the MSBuild of Visual Studio. Each builds and runs; a build after no change does not verify again, one
after a change does; a wrong proof, an underspecified contract and a missing contract fail the build, with
their codes. NuGet's global cache is redirected, so that nothing stays behind. Stops at the first failure.
"""
from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

CLAMP = """fn clamp(x: int, lo: int, hi: int) -> int
  requires lo <= hi
  ensures lo <= result <= hi
  ensures x < lo ==> result == lo
  ensures x > hi ==> result == hi
  ensures lo <= x <= hi ==> result == x
{
  if x < lo { lo } else if x > hi { hi } else { x }
}
"""
WRONG_PROOF = "fn f(x: int) -> int\n  ensures result > x\n{\n  return x;\n}\n"
UNDERSPECIFIED = "fn f(x: int) -> int\n  ensures result > x\n{\n  return x + 1;\n}\n"
NO_CONTRACT = "fn f(x: int) -> int\n{\n  let y = x;\n  return y;\n}\n"

MAIN = """using System;
using System.Numerics;
class Program
{
    static void Main()
    {
        Console.WriteLine(App.Rules.Rules.Clamp(new BigInteger(12), new BigInteger(0), new BigInteger(10)));
        try { App.Rules.Rules.Clamp(new BigInteger(1), new BigInteger(5), new BigInteger(0)); }
        catch (ArgumentException) { Console.WriteLine("refused"); }
    }
}
"""

SDK_PROJECT = """<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <OutputType>Exe</OutputType>
    <TargetFramework>%s</TargetFramework>
    <LangVersion>7.3</LangVersion>
    <RootNamespace>App.Rules</RootNamespace>
    <TreatWarningsAsErrors>true</TreatWarningsAsErrors>
    %s
  </PropertyGroup>
  <ItemGroup>
    <PackageReference Include="Quod.Build" Version="%s" PrivateAssets="all" />
    <QuodCompile Include="Rules.quod" />
  </ItemGroup>
</Project>
"""

OLD_PROJECT = """<?xml version="1.0" encoding="utf-8"?>
<Project ToolsVersion="15.0" DefaultTargets="Build" xmlns="http://schemas.microsoft.com/developer/msbuild/2003">
  <Import Project="$(MSBuildExtensionsPath)\\$(MSBuildToolsVersion)\\Microsoft.Common.props" />
  <PropertyGroup>
    <Configuration Condition=" '$(Configuration)' == '' ">Release</Configuration>
    <Platform Condition=" '$(Platform)' == '' ">AnyCPU</Platform>
    <OutputType>Exe</OutputType>
    <RootNamespace>App.Rules</RootNamespace>
    <AssemblyName>Old</AssemblyName>
    <TargetFrameworkVersion>v4.7.2</TargetFrameworkVersion>
    <OutputPath>bin\\</OutputPath>
    <LangVersion>7.3</LangVersion>
  </PropertyGroup>
  <ItemGroup>
    <Reference Include="System" />
    <Compile Include="Program.cs" />
    <QuodCompile Include="Rules.quod" />
    <None Include="packages.config" />
  </ItemGroup>
  <Import Project="$(MSBuildToolsPath)\\Microsoft.CSharp.targets" />
  <Import Project="packages\\Quod.Build.%s\\build\\Quod.Build.targets" />
</Project>
"""


def fail(message: str) -> None:
    """Stop here. On GitHub Actions the message is also an annotation, readable without the logs."""
    if os.environ.get("GITHUB_ACTIONS"):
        print("::error::" + message.replace("%", "%25").replace("\r", "").replace("\n", "%0A"))
    sys.exit(message)


def run(cmd, cwd, env, expect=0):
    r = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, encoding="utf-8", errors="replace")
    out = r.stdout + r.stderr
    if expect is not None and (r.returncode == 0) != (expect == 0):
        fail(f"FAILED: {cmd} exit {r.returncode}\n{out[-2500:]}")
    return out


def check(condition, what, details=""):
    if not condition:
        fail(f"FAILED: {what}\n{details[-2500:]}")
    print("ok  ", what)


def msbuild_path() -> str | None:
    vswhere = Path(r"C:\Program Files (x86)\Microsoft Visual Studio\Installer\vswhere.exe")
    if not vswhere.exists():
        return None
    r = subprocess.run([str(vswhere), "-latest", "-products", "*", "-requires", "Microsoft.Component.MSBuild", "-find",
                        r"MSBuild\**\Bin\MSBuild.exe"], capture_output=True, text=True)
    lines = r.stdout.strip().splitlines()
    return lines[0] if lines else None


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--package", required=True, type=Path)
    p.add_argument("--version", required=True)
    a = p.parse_args()
    root = Path(tempfile.mkdtemp(prefix="quod pkg "))
    try:
        env = dict(os.environ, NUGET_PACKAGES=str(root / "cache"), DOTNET_CLI_UI_LANGUAGE="en", DOTNET_NOLOGO="1",
                   MSBUILDDISABLENODEREUSE="1")
        env.pop("QUOD_Z3", None)  # the z3 of the package
        feed = root / "feed"
        feed.mkdir()
        shutil.copy(a.package, feed)
        (root / "nuget.config").write_text(
            '<configuration><packageSources><clear /><add key="local" value="%s" /></packageSources></configuration>' % feed,
            encoding="utf-8")
        windows = os.name == "nt"

        def sdk(name, framework, source=CLAMP, extra=""):
            d = root / name
            d.mkdir()
            (d / "App.csproj").write_text(SDK_PROJECT % (framework, extra, a.version), encoding="utf-8")
            (d / "Rules.quod").write_text(source, encoding="utf-8")
            (d / "Program.cs").write_text(MAIN, encoding="utf-8")
            return d

        build = ["dotnet", "build", "-c", "Release", "--nologo", "-p:UseSharedCompilation=false"]

        d = sdk("sdk app", "net10.0")
        run(build, d, env)
        out = run(["dotnet", "run", "-c", "Release", "--no-build"], d, env)
        check("10" in out and "refused" in out, "an SDK project on .NET builds, and calls the proved function", out)
        generated = d / "obj" / "Release" / "net10.0" / "quod" / "Rules.g.cs"
        check(generated.exists(), "the generated file is under obj")
        first = generated.stat().st_mtime
        time.sleep(1.2)
        run(build, d, env)
        check(generated.stat().st_mtime == first, "a build after no change does not verify again")
        (d / "Rules.quod").write_text(CLAMP + "\nfn twice(x: int) -> int ensures result == 2 * x { 2 * x }\n", encoding="utf-8")
        run(build, d, env)
        check("Twice" in generated.read_text(encoding="utf-8"), "a build after a change does")
        (d / "Rules.quod").write_text(WRONG_PROOF, encoding="utf-8")
        out = run(build, d, env, expect=1)
        check(re.search(r"Rules\.quod\(\d+,\d+\): error QUOD0003", out) is not None, "a wrong proof fails the build, with its code and its place", out)
        check("MSB3073" not in out, "without a second error that repeats the command", out)

        d = sdk("sdk under", "net10.0", UNDERSPECIFIED)
        out = run(build, d, env, expect=1)
        check("error QUOD0004" in out, "an underspecified contract fails the build", out)

        d = sdk("sdk none", "net10.0", NO_CONTRACT, "<QuodRequireContracts>true</QuodRequireContracts>")
        out = run(build, d, env, expect=1)
        check("error QUOD0005" in out, "QuodRequireContracts refuses a function without a contract", out)

        d = sdk("sdk options", "net10.0", CLAMP + "\n" + NO_CONTRACT)
        run(build, d, env)
        out = run(build + ["-p:QuodRequireContracts=true"], d, env, expect=1)
        check("error QUOD0005" in out, "changing an option verifies again, without touching the file", out)

        if not windows:
            print("skip .NET Framework: Windows only")
            print("all passed")
            return

        d = sdk("sdk framework", "net472")
        run(build, d, env)
        exe = d / "bin" / "Release" / "net472" / "App.exe"
        out = run([str(exe)], d, env)
        check("10" in out and "refused" in out, "an SDK project on .NET Framework 4.7.2, with System.Numerics added", out)

        msbuild = msbuild_path()
        if msbuild is None:
            print("skip the old-style project: no MSBuild of Visual Studio")
            print("all passed")
            return
        d = root / "old app"
        d.mkdir()
        (d / "Old.csproj").write_text(OLD_PROJECT % a.version, encoding="utf-8")
        (d / "packages.config").write_text(
            '<?xml version="1.0" encoding="utf-8"?><packages><package id="Quod.Build" version="%s" targetFramework="net472" developmentDependency="true" /></packages>' % a.version,
            encoding="utf-8")
        (d / "Rules.quod").write_text(CLAMP, encoding="utf-8")
        (d / "Program.cs").write_text(MAIN, encoding="utf-8")
        run([msbuild, "Old.csproj", "-t:restore", "-p:RestorePackagesConfig=true", "-p:SolutionDir=" + str(d) + os.sep, "-nologo", "-v:q"], d, env)
        check((d / "packages" / f"Quod.Build.{a.version}").exists(), "packages.config restores the package")
        # the same with the MSBuild that comes with Visual Studio, as a solution of an older code base does
        out = run([msbuild, "Old.csproj", "-nologo", "-v:m", "-nodeReuse:false"], d, env)
        out = run([str(d / "bin" / "Old.exe")], d, env)
        check("10" in out and "refused" in out, "an old-style project with packages.config, under the MSBuild of Visual Studio", out)
        (d / "Rules.quod").write_text(WRONG_PROOF, encoding="utf-8")
        out = run([msbuild, "Old.csproj", "-nologo", "-v:m", "-nodeReuse:false"], d, env, expect=1)
        check(re.search(r"Rules\.quod\(\d+,\d+\): error QUOD0003", out) is not None, "and a wrong proof fails it too", out)
        print("all passed")
    finally:
        shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    main()
