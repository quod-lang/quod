module Solution {
  predicate IsOpen(c: char) { c == '(' || c == '[' || c == '{' }
  predicate IsClose(c: char) { c == ')' || c == ']' || c == '}' }
  function Match(c: char): char requires IsClose(c) {
    if c == ')' then '(' else if c == ']' then '[' else '{'
  }

  // Stack after scanning s, or None once a mismatch has occurred.
  function Scan(s: string): Option<seq<char>> {
    if |s| == 0 then Some([])
    else match Scan(s[..|s| - 1])
      case None => None
      case Some(st) =>
        var c := s[|s| - 1];
        if IsOpen(c) then Some(st + [c])
        else if IsClose(c) then
          (if |st| > 0 && st[|st| - 1] == Match(c) then Some(st[..|st| - 1]) else None)
        else Some(st)
  }

  datatype Option<T> = None | Some(value: T)

  method balanced(s: string) returns (b: bool)
    ensures b <==> Scan(s) == Some([])
  {
    var st: seq<char> := [];
    var k := 0;
    while k < |s|
      invariant 0 <= k <= |s|
      invariant Scan(s[..k]) == Some(st)
    {
      assert s[..k + 1][..k] == s[..k];
      var c := s[k];
      if IsOpen(c) {
        st := st + [c];
      } else if IsClose(c) {
        if |st| == 0 || st[|st| - 1] != Match(c) {
          // Once Scan fails it stays failed, so the whole string is unbalanced.
          ScanFailSticky(s, k + 1);
          return false;
        }
        st := st[..|st| - 1];
      }
      k := k + 1;
    }
    assert s[..k] == s;
    return |st| == 0;
  }

  lemma ScanFailSticky(s: string, k: nat)
    requires k <= |s| && Scan(s[..k]).None?
    ensures Scan(s).None?
    decreases |s| - k
  {
    if k < |s| {
      assert s[..k + 1][..k] == s[..k];
      ScanFailSticky(s, k + 1);
    } else {
      assert s[..k] == s;
    }
  }
}
