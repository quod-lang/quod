module Solution {

  predicate sorted_seq(xs: seq<int>) {
    forall i, j :: 0 <= i < j < |xs| ==> xs[i] <= xs[j]
  }

  method two_sum_sorted(xs: seq<int>, target: int) returns (r: (int, int))
    requires sorted_seq(xs)
    ensures r.0 == -1 ==> r.1 == -1 && forall i, j :: 0 <= i < j < |xs| ==> xs[i] + xs[j] != target
    ensures r.0 != -1 ==> 0 <= r.0 < r.1 < |xs| && xs[r.0] + xs[r.1] == target
  {
    var lo := 0;
    var hi := |xs| - 1;
    while lo < hi
      invariant 0 <= lo && hi < |xs|
      invariant forall i, j :: 0 <= i < j < |xs| && xs[i] + xs[j] == target ==> lo <= i && j <= hi
      decreases hi - lo
    {
      var s := xs[lo] + xs[hi];
      if s == target {
        return (lo, hi);
      } else if s < target {
        assert forall j :: lo < j <= hi ==> xs[lo] + xs[j] <= s;
        lo := lo + 1;
      } else {
        assert forall i :: lo <= i < hi ==> xs[i] + xs[hi] >= s;
        hi := hi - 1;
      }
    }
    r := (-1, -1);
  }
}
