module Solution {
  method transpose(m: seq<seq<int>>) returns (r: seq<seq<int>>)
    requires |m| > 0
    requires |m[0]| > 0
    requires forall i :: 0 <= i < |m| ==> |m[i]| == |m[0]|
    ensures |r| == |m[0]|
    ensures forall k :: 0 <= k < |r| ==> |r[k]| == |m|
    ensures forall k, i :: 0 <= k < |r| && 0 <= i < |m| ==> r[k][i] == m[i][k]
  {
    var cols := |m[0]|;
    r := [];
    var j := 0;
    while j < cols
      invariant 0 <= j <= cols
      invariant |r| == j
      invariant forall k :: 0 <= k < j ==> |r[k]| == |m|
      invariant forall k, i :: 0 <= k < j && 0 <= i < |m| ==> r[k][i] == m[i][k]
    {
      var row: seq<int> := [];
      var i := 0;
      while i < |m|
        invariant 0 <= i <= |m|
        invariant |row| == i
        invariant forall t :: 0 <= t < i ==> row[t] == m[t][j]
      {
        row := row + [m[i][j]];
        i := i + 1;
      }
      r := r + [row];
      j := j + 1;
    }
  }
}
