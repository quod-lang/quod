module Solution {

  predicate sorted(xs: seq<int>) {
    forall i, j :: 0 <= i < j < |xs| ==> xs[i] <= xs[j]
  }

  method binary_search(xs: seq<int>, target: int) returns (r: int)
    requires sorted(xs)
    ensures r == -1 ==> forall k :: 0 <= k < |xs| ==> xs[k] != target
    ensures r != -1 ==> 0 <= r < |xs| && xs[r] == target
  {
    var lo := 0;
    var hi := |xs|;
    while lo < hi
      invariant 0 <= lo <= hi <= |xs|
      invariant forall k :: 0 <= k < lo ==> xs[k] < target
      invariant forall k :: hi <= k < |xs| ==> xs[k] > target
      decreases hi - lo
    {
      var mid := lo + (hi - lo) / 2;
      if xs[mid] < target {
        lo := mid + 1;
      } else if xs[mid] > target {
        hi := mid;
      } else {
        return mid;
      }
    }
    return -1;
  }
}
