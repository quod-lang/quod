module Solution {

  // Split p[i..] on '/', given current partial component `cur` and completed components `acc`.
  function SplitFrom(p: string, i: nat, cur: string, acc: seq<string>): seq<string>
    requires i <= |p|
    decreases |p| - i
  {
    if i == |p| then acc + [cur]
    else if p[i] == '/' then SplitFrom(p, i + 1, "", acc + [cur])
    else SplitFrom(p, i + 1, cur + [p[i]], acc)
  }

  function Split(p: string): seq<string>
  {
    SplitFrom(p, 0, "", [])
  }

  function Step(stack: seq<string>, c: string, abs: bool): seq<string>
  {
    if c == "" || c == "." then stack
    else if c == ".." then
      if |stack| > 0 && stack[|stack| - 1] != ".." then stack[..|stack| - 1]
      else if abs then stack
      else stack + [c]
    else stack + [c]
  }

  function ProcessFrom(comps: seq<string>, i: nat, stack: seq<string>, abs: bool): seq<string>
    requires i <= |comps|
    decreases |comps| - i
  {
    if i == |comps| then stack
    else ProcessFrom(comps, i + 1, Step(stack, comps[i], abs), abs)
  }

  function Join(s: seq<string>): string
  {
    if |s| == 0 then ""
    else if |s| == 1 then s[0]
    else Join(s[..|s| - 1]) + "/" + s[|s| - 1]
  }

  predicate IsAbs(p: string)
  {
    |p| > 0 && p[0] == '/'
  }

  function Normalize(p: string): string
  {
    var abs := IsAbs(p);
    var kept := ProcessFrom(Split(p), 0, [], abs);
    if abs then "/" + Join(kept)
    else if |kept| == 0 then "."
    else Join(kept)
  }

  method normalize_path(p: string) returns (r: string)
    ensures r == Normalize(p)
  {
    // Split
    var comps: seq<string> := [];
    var cur: string := "";
    var i := 0;
    while i < |p|
      invariant 0 <= i <= |p|
      invariant SplitFrom(p, i, cur, comps) == Split(p)
      decreases |p| - i
    {
      if p[i] == '/' {
        comps := comps + [cur];
        cur := "";
      } else {
        cur := cur + [p[i]];
      }
      i := i + 1;
    }
    comps := comps + [cur];

    // Process
    var abs := |p| > 0 && p[0] == '/';
    var stack: seq<string> := [];
    var j := 0;
    while j < |comps|
      invariant 0 <= j <= |comps|
      invariant ProcessFrom(comps, j, stack, abs) == ProcessFrom(comps, 0, [], abs)
      decreases |comps| - j
    {
      stack := Step(stack, comps[j], abs);
      j := j + 1;
    }

    // Join
    var joined: string := "";
    var k := 0;
    while k < |stack|
      invariant 0 <= k <= |stack|
      invariant joined == Join(stack[..k])
      decreases |stack| - k
    {
      assert stack[..k + 1][..k] == stack[..k];
      if k == 0 {
        joined := stack[0];
      } else {
        joined := joined + "/" + stack[k];
      }
      k := k + 1;
    }
    assert stack[..|stack|] == stack;

    if abs {
      r := "/" + joined;
    } else if |stack| == 0 {
      r := ".";
    } else {
      r := joined;
    }
  }
}
