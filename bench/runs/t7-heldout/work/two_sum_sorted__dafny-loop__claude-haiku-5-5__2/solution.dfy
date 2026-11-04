module Solution {
  method two_sum_sorted(xs: seq<int>, target: int) returns (r: (int, int))
    requires forall a, b :: 0 <= a < b < |xs| ==> xs[a] <= xs[b]
    ensures r == (-1, -1) ==> forall a, b :: 0 <= a < b < |xs| ==> xs[a] + xs[b] != target
    ensures r != (-1, -1) ==> 0 <= r.0 < r.1 < |xs| && xs[r.0] + xs[r.1] == target
  {
    var i := 0;
    var j := |xs| - 1;
    while i < j
      invariant 0 <= i
      invariant j < |xs|
      invariant i <= j + 1
      invariant forall a, b :: 0 <= a < b < |xs| && xs[a] + xs[b] == target ==> i <= a && b <= j
      decreases j - i
    {
      var s := xs[i] + xs[j];
      if s == target {
        return (i, j);
      } else if s < target {
        // For every b <= j, xs[i] + xs[b] <= s < target, so i cannot pair with anything left of j+1.
        i := i + 1;
      } else {
        // For every a >= i, xs[a] + xs[j] >= s > target, so j cannot pair with anything right of i-1.
        j := j - 1;
      }
    }
    return (-1, -1);
  }
}
