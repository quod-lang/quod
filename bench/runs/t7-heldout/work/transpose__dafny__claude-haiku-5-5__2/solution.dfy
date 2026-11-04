module Solution {
  method transpose(m: seq<seq<int>>) returns (r: seq<seq<int>>)
    requires |m| >= 1
    requires |m[0]| >= 1
    requires forall i :: 0 <= i < |m| ==> |m[i]| == |m[0]|
    ensures |r| == |m[0]|
    ensures forall i :: 0 <= i < |r| ==> |r[i]| == |m|
    ensures forall i, j :: 0 <= i < |r| && 0 <= j < |m| ==> r[i][j] == m[j][i]
  {
    var rows := |m|;
    var cols := |m[0]|;
    r := [];
    var c := 0;
    while c < cols
      invariant 0 <= c <= cols
      invariant |r| == c
      invariant forall i :: 0 <= i < c ==> |r[i]| == rows
      invariant forall i, j :: 0 <= i < c && 0 <= j < rows ==> r[i][j] == m[j][i]
    {
      var col: seq<int> := [];
      var j := 0;
      while j < rows
        invariant 0 <= j <= rows
        invariant |col| == j
        invariant forall k :: 0 <= k < j ==> col[k] == m[k][c]
      {
        col := col + [m[j][c]];
        j := j + 1;
      }
      r := r + [col];
      c := c + 1;
    }
  }
}
