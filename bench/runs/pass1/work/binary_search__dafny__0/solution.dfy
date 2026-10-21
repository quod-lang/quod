module Solution {
  method binary_search(xs: seq<int>, target: int) returns (r: int)
    requires forall i, j :: 0 <= i < j < |xs| ==> xs[i] <= xs[j]
    ensures -1 <= r < |xs|
    ensures r >= 0 ==> xs[r] == target
    ensures r == -1 ==> forall i :: 0 <= i < |xs| ==> xs[i] != target
  {
    var lo := 0;
    var hi := |xs|;
    while lo < hi
      invariant 0 <= lo <= hi <= |xs|
      invariant forall i :: 0 <= i < lo ==> xs[i] != target
      invariant forall i :: hi <= i < |xs| ==> xs[i] != target
      decreases hi - lo
    {
      var mid := lo + (hi - lo) / 2;
      if xs[mid] == target {
        return mid;
      } else if xs[mid] < target {
        lo := mid + 1;
      } else {
        hi := mid;
      }
    }
    return -1;
  }
}
