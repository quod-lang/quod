module Solution {
  predicate IsOpen(c: char) { c == '(' || c == '[' || c == '{' }
  predicate IsClose(c: char) { c == ')' || c == ']' || c == '}' }

  function OpenOf(c: char): char
  {
    if c == ')' then '(' else if c == ']' then '[' else '{'
  }

  // Stack-based scan: returns (no mismatch so far, remaining stack of open brackets)
  function Scan(s: string, st: seq<char>): (bool, seq<char>)
    decreases |s|
  {
    if |s| == 0 then (true, st)
    else if IsOpen(s[0]) then Scan(s[1..], st + [s[0]])
    else if IsClose(s[0]) then
      if |st| > 0 && st[|st| - 1] == OpenOf(s[0]) then Scan(s[1..], st[..|st| - 1])
      else (false, st)
    else Scan(s[1..], st)
  }

  predicate IsBalanced(s: string)
  {
    var r := Scan(s, []);
    r.0 && |r.1| == 0
  }

  method balanced(s: string) returns (b: bool)
    ensures b == IsBalanced(s)
  {
    var st: seq<char> := [];
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant Scan(s, []) == Scan(s[i..], st)
      decreases |s| - i
    {
      var c := s[i];
      assert s[i..][0] == c;
      assert s[i..][1..] == s[i + 1..];
      if IsOpen(c) {
        st := st + [c];
      } else if IsClose(c) {
        if |st| > 0 && st[|st| - 1] == OpenOf(c) {
          st := st[..|st| - 1];
        } else {
          return false;
        }
      }
      i := i + 1;
    }
    assert s[i..] == [];
    b := |st| == 0;
  }
}
