module Solution {
  predicate Sorted(xs: seq<int>) {
    forall i, j :: 0 <= i < j < |xs| ==> xs[i] <= xs[j]
  }

  method binary_search(xs: seq<int>, target: int) returns (r: int)
    requires Sorted(xs)
    ensures -1 <= r < |xs|
    ensures r >= 0 ==> xs[r] == target
    ensures r == -1 ==> target !in xs
  {
    var lo, hi := 0, |xs|;
    while lo < hi
      invariant 0 <= lo <= hi <= |xs|
      invariant forall i :: 0 <= i < lo ==> xs[i] < target
      invariant forall i :: hi <= i < |xs| ==> xs[i] > target
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
