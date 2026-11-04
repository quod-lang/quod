module Solution {

  predicate IsRectangular(m: seq<seq<int>>)
  {
    forall i :: 0 <= i < |m| ==> |m[i]| == |m[0]|
  }

  method transpose(m: seq<seq<int>>) returns (r: seq<seq<int>>)
    requires |m| >= 1
    requires |m[0]| >= 1
    requires IsRectangular(m)
    ensures |r| == |m[0]|
    ensures forall i :: 0 <= i < |r| ==> |r[i]| == |m|
    ensures forall i, j :: 0 <= i < |r| && 0 <= j < |r[i]| ==> r[i][j] == m[j][i]
  {
    var n := |m[0]|;
    var k := |m|;
    r := [];
    var c := 0;
    while c < n
      invariant 0 <= c <= n
      invariant |r| == c
      invariant forall i :: 0 <= i < c ==> |r[i]| == k
      invariant forall i, j :: 0 <= i < c && 0 <= j < k ==> r[i][j] == m[j][i]
      decreases n - c
    {
      var row: seq<int> := [];
      var j := 0;
      while j < k
        invariant 0 <= j <= k
        invariant |row| == j
        invariant forall t :: 0 <= t < j ==> row[t] == m[t][c]
        decreases k - j
      {
        assert |m[j]| == n;
        row := row + [m[j][c]];
        j := j + 1;
      }
      r := r + [row];
      c := c + 1;
    }
  }
}
