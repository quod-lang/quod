module Solution {
  // Does pattern suffix p[i..] match text suffix t[j..]?
  function M(p: string, t: string, i: nat, j: nat): bool
    requires i <= |p| && j <= |t|
    decreases |p| - i + |t| - j
  {
    if i == |p| then j == |t|
    else if p[i] == '*' then M(p, t, i + 1, j) || (j < |t| && M(p, t, i, j + 1))
    else if p[i] == '?' then j < |t| && M(p, t, i + 1, j + 1)
    else if p[i] == '\\' && i + 1 < |p| then j < |t| && t[j] == p[i + 1] && M(p, t, i + 2, j + 1)
    else j < |t| && t[j] == p[i] && M(p, t, i + 1, j + 1)
  }

  method glob_match(pattern: string, text: string) returns (b: bool)
    ensures b == M(pattern, text, 0, 0)
  {
    var n := |pattern|;
    var m := |text|;
    var dp := new bool[n + 1, m + 1];
    var i := n + 1;
    while i > 0
      invariant 0 <= i <= n + 1
      invariant forall i', j' :: i <= i' <= n && 0 <= j' <= m ==> dp[i', j'] == M(pattern, text, i', j')
    {
      i := i - 1;
      var j := m + 1;
      while j > 0
        invariant 0 <= j <= m + 1
        invariant forall i', j' :: i < i' <= n && 0 <= j' <= m ==> dp[i', j'] == M(pattern, text, i', j')
        invariant forall j' :: j <= j' <= m ==> dp[i, j'] == M(pattern, text, i, j')
      {
        j := j - 1;
        var r: bool;
        if i == n {
          r := j == m;
        } else if pattern[i] == '*' {
          r := dp[i + 1, j] || (j < m && dp[i, j + 1]);
        } else if pattern[i] == '?' {
          r := j < m && dp[i + 1, j + 1];
        } else if pattern[i] == '\\' && i + 1 < n {
          r := j < m && text[j] == pattern[i + 1] && dp[i + 2, j + 1];
        } else {
          r := j < m && text[j] == pattern[i] && dp[i + 1, j + 1];
        }
        dp[i, j] := r;
      }
    }
    b := dp[0, 0];
  }
}
