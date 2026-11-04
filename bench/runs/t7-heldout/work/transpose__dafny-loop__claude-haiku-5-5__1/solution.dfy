module Solution {
  method transpose(m: seq<seq<int>>) returns (r: seq<seq<int>>)
    requires |m| > 0
    requires |m[0]| > 0
    requires forall i :: 0 <= i < |m| ==> |m[i]| == |m[0]|
    ensures |r| == |m[0]|
    ensures forall j :: 0 <= j < |r| ==> |r[j]| == |m|
    ensures forall i, j :: 0 <= i < |m| && 0 <= j < |m[0]| ==> r[j][i] == m[i][j]
  {
    var cols := |m[0]|;
    r := [];
    var j := 0;
    while j < cols
      invariant 0 <= j <= cols
      invariant |r| == j
      invariant forall k :: 0 <= k < j ==> |r[k]| == |m|
      invariant forall k, i :: 0 <= k < j && 0 <= i < |m| ==> r[k][i] == m[i][k]
      decreases cols - j
    {
      var col: seq<int> := [];
      var i := 0;
      while i < |m|
        invariant 0 <= i <= |m|
        invariant |col| == i
        invariant forall t :: 0 <= t < i ==> col[t] == m[t][j]
        decreases |m| - i
      {
        col := col + [m[i][j]];
        i := i + 1;
      }
      r := r + [col];
      j := j + 1;
    }
  }
}
