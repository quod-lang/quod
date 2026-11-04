module Solution {
  predicate sorted(xs: seq<int>) {
    forall a, b :: 0 <= a < b < |xs| ==> xs[a] <= xs[b]
  }

  method two_sum_sorted(xs: seq<int>, target: int) returns (r: (int, int))
    requires sorted(xs)
    ensures r == (-1, -1) ==>
      forall a, b :: 0 <= a < b < |xs| ==> xs[a] + xs[b] != target
    ensures r != (-1, -1) ==>
      0 <= r.0 < r.1 < |xs| && xs[r.0] + xs[r.1] == target
  {
    var n := |xs|;
    var i := 0;
    var j := n - 1;
    while i < j
      invariant 0 <= i
      invariant j < n
      invariant forall a, b :: 0 <= a < b < n && (a < i || b > j) ==> xs[a] + xs[b] != target
      decreases j - i
    {
      var s := xs[i] + xs[j];
      if s == target {
        return (i, j);
      } else if s < target {
        assert forall b :: i < b <= j ==> xs[i] + xs[b] <= xs[i] + xs[j];
        i := i + 1;
      } else {
        assert forall a :: i <= a < j ==> xs[a] + xs[j] >= xs[i] + xs[j];
        j := j - 1;
      }
    }
    return (-1, -1);
  }
}
