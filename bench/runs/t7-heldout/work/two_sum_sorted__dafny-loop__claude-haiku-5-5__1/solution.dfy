module Solution {

  // xs is sorted in non-decreasing order.
  predicate sorted(xs: seq<int>) {
    forall a, b :: 0 <= a < b < |xs| ==> xs[a] <= xs[b]
  }

  // No pair of indices (a, b) with a < b and both in range sums to target.
  predicate no_pair(xs: seq<int>, target: int) {
    forall a, b :: 0 <= a < b < |xs| ==> xs[a] + xs[b] != target
  }

  method two_sum_sorted(xs: seq<int>, target: int) returns (r: (int, int))
    requires sorted(xs)
    ensures r == (-1, -1) ==> no_pair(xs, target)
    ensures r != (-1, -1) ==> 0 <= r.0 < r.1 < |xs| && xs[r.0] + xs[r.1] == target
  {
    if |xs| == 0 {
      return (-1, -1);
    }
    var i := 0;
    var j := |xs| - 1;
    while i < j
      invariant 0 <= i
      invariant j < |xs|
      invariant forall a, b :: 0 <= a < b < |xs| && (a < i || b > j) ==> xs[a] + xs[b] != target
      decreases j - i
    {
      var s := xs[i] + xs[j];
      if s == target {
        return (i, j);
      } else if s < target {
        // xs[i] + xs[b] <= xs[i] + xs[j] < target for all b <= j, so row i is exhausted.
        i := i + 1;
      } else {
        // xs[a] + xs[j] >= xs[i] + xs[j] > target for all a >= i, so column j is exhausted.
        j := j - 1;
      }
    }
    return (-1, -1);
  }
}
