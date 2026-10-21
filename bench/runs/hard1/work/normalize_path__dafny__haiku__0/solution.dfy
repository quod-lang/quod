module Solution {
  method normalize_path(p: string) returns (r: string)
    requires true
    ensures var is_abs := |p| > 0 && p[0] == '/';
            if is_abs then (|r| > 0 && r[0] == '/') else (r == "." || |r| > 0)
  {
    var is_absolute := |p| > 0 && p[0] == '/';

    // Split into components
    var components: seq<string> := [];
    var start := if is_absolute then 1 else 0;
    var i := start;
    var current: string := "";

    while i < |p|
      invariant start <= i <= |p|
      decreases |p| - i
    {
      if p[i] == '/' {
        components := components + [current];
        current := "";
      } else {
        current := current + [p[i]];
      }
      i := i + 1;
    }
    components := components + [current];

    // Process components
    var stack: seq<string> := [];
    var j := 0;

    while j < |components|
      invariant 0 <= j <= |components|
      invariant forall idx :: 0 <= idx < |stack| ==> |stack[idx]| > 0
      decreases |components| - j
    {
      var comp := components[j];
      if comp != "" && comp != "." {
        if comp == ".." {
          if |stack| > 0 && stack[|stack| - 1] != ".." {
            stack := stack[..|stack| - 1];
          } else if !is_absolute {
            stack := stack + [comp];
          }
        } else {
          stack := stack + [comp];
        }
      }
      j := j + 1;
    }

    // Build result iteratively
    if is_absolute {
      r := "/";
      var k := 0;
      while k < |stack|
        invariant 0 <= k <= |stack|
        invariant |r| > 0 && r[0] == '/'
        decreases |stack| - k
      {
        if k > 0 {
          r := r + "/";
        }
        r := r + stack[k];
        k := k + 1;
      }
    } else {
      if |stack| == 0 {
        r := ".";
      } else {
        r := "";
        var k := 0;
        while k < |stack|
          invariant 0 <= k <= |stack|
          invariant k > 0 ==> |r| > 0
          invariant forall idx :: 0 <= idx < |stack| ==> |stack[idx]| > 0
          decreases |stack| - k
        {
          if k > 0 {
            r := r + "/";
          }
          r := r + stack[k];
          k := k + 1;
        }
      }
    }
  }
}
