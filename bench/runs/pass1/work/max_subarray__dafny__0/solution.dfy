module Solution {
  function Sum(xs: seq<int>, i: int, j: int): int
    requires 0 <= i <= j <= |xs|
    decreases j - i
  {
    if i == j then 0 else Sum(xs, i, j - 1) + xs[j - 1]
  }

  method max_subarray(xs: seq<int>) returns (m: int)
    requires |xs| > 0
    ensures exists a, b :: 0 <= a < b <= |xs| && m == Sum(xs, a, b)
    ensures forall a, b :: 0 <= a < b <= |xs| ==> Sum(xs, a, b) <= m
  {
    var cur := xs[0];
    m := xs[0];
    assert Sum(xs, 0, 1) == xs[0];
    var ca := 0;
    var ma, mb := 0, 1;
    var i := 1;
    while i < |xs|
      invariant 1 <= i <= |xs|
      invariant 0 <= ca < i && cur == Sum(xs, ca, i)
      invariant forall k :: 0 <= k < i ==> Sum(xs, k, i) <= cur
      invariant 0 <= ma < mb <= i && m == Sum(xs, ma, mb)
      invariant forall a, b :: 0 <= a < b <= i ==> Sum(xs, a, b) <= m
      decreases |xs| - i
    {
      assert Sum(xs, i, i + 1) == xs[i];
      assert forall k :: 0 <= k < i ==> Sum(xs, k, i + 1) == Sum(xs, k, i) + xs[i];
      if cur + xs[i] >= xs[i] {
        cur := cur + xs[i];
      } else {
        cur := xs[i];
        ca := i;
      }
      if cur > m {
        m := cur;
        ma, mb := ca, i + 1;
      }
      i := i + 1;
    }
  }
}
