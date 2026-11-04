module Solution {

  method two_sum_sorted(xs: seq<int>, target: int) returns (r: (int, int))
    requires forall a: int, b: int :: 0 <= a < b < |xs| ==> xs[a] <= xs[b]
    ensures r.0 == -1 ==> r.1 == -1 && (forall a: int, b: int :: 0 <= a < b < |xs| ==> xs[a] + xs[b] != target)
    ensures r.0 != -1 ==> 0 <= r.0 < r.1 < |xs| && xs[r.0] + xs[r.1] == target
  {
    var i := 0;
    var j := |xs| - 1;
    while i < j
      invariant 0 <= i && j < |xs|
      invariant forall a: int, b: int :: 0 <= a < b < |xs| && xs[a] + xs[b] == target ==> i <= a && b <= j
      decreases j - i
    {
      var s := xs[i] + xs[j];
      if s == target {
        return (i, j);
      } else if s < target {
        // xs[i] + xs[b] <= xs[i] + xs[j] < target for every b <= j, so i is useless.
        i := i + 1;
      } else {
        // xs[a] + xs[j] >= xs[i] + xs[j] > target for every a >= i, so j is useless.
        j := j - 1;
      }
    }
    return (-1, -1);
  }
}
