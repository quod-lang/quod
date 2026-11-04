module Solution {
  method two_sum_sorted(xs: seq<int>, target: int) returns (r: (int, int))
    requires forall p, q :: 0 <= p < q < |xs| ==> xs[p] <= xs[q]
    ensures r == (-1, -1) ==> forall p, q :: 0 <= p < q < |xs| ==> xs[p] + xs[q] != target
    ensures r != (-1, -1) ==> 0 <= r.0 < r.1 < |xs| && xs[r.0] + xs[r.1] == target
  {
    var i := 0;
    var j := |xs| - 1;
    while i < j
      invariant 0 <= i
      invariant j < |xs|
      invariant i <= j + 1
      invariant forall p, q :: 0 <= p < q < |xs| && xs[p] + xs[q] == target ==> i <= p && q <= j
      decreases j - i
    {
      var s := xs[i] + xs[j];
      if s == target {
        return (i, j);
      } else if s < target {
        // Any pair (i, q) with q <= j has sum <= s < target, so i is useless.
        assert forall q :: i < q <= j ==> xs[q] <= xs[j];
        i := i + 1;
      } else {
        // Any pair (p, j) with p >= i has sum >= s > target, so j is useless.
        assert forall p :: i <= p < j ==> xs[i] <= xs[p];
        j := j - 1;
      }
    }
    return (-1, -1);
  }
}
