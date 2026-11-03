module Solution {

  // Sum of xs[i..j-1] (the contiguous sublist from index i, inclusive, to j, exclusive).
  function SumRange(xs: seq<int>, i: int, j: int): int
    requires 0 <= i <= j <= |xs|
    decreases j - i
  {
    if i == j then 0 else SumRange(xs, i, j - 1) + xs[j - 1]
  }

  // Maximum sum over all non-empty contiguous sublists, computed in O(n) (Kadane's algorithm).
  method max_subarray(xs: seq<int>) returns (m: int)
    requires |xs| > 0
    ensures exists i, j :: 0 <= i < j <= |xs| && m == SumRange(xs, i, j)
    ensures forall i, j :: 0 <= i < j <= |xs| ==> SumRange(xs, i, j) <= m
  {
    // cur: best sum of a non-empty sublist ending at index k-1
    // m:   best sum of any non-empty sublist within xs[0..k-1]
    var cur := xs[0];
    m := xs[0];
    var k := 1;
    assert SumRange(xs, 0, 1) == xs[0];

    while k < |xs|
      invariant 1 <= k <= |xs|
      invariant exists i :: 0 <= i < k && cur == SumRange(xs, i, k)
      invariant forall i :: 0 <= i < k ==> SumRange(xs, i, k) <= cur
      invariant exists i, j :: 0 <= i < j <= k && m == SumRange(xs, i, j)
      invariant forall i, j :: 0 <= i < j <= k ==> SumRange(xs, i, j) <= m
      decreases |xs| - k
    {
      var x := xs[k];
      assert forall i :: 0 <= i < k ==> SumRange(xs, i, k + 1) == SumRange(xs, i, k) + x;
      assert SumRange(xs, k, k + 1) == x;

      // Extend the best sublist ending at k-1, or start a new one at k.
      if cur + x >= x {
        var i0 :| 0 <= i0 < k && cur == SumRange(xs, i0, k);
        cur := cur + x;
        assert cur == SumRange(xs, i0, k + 1);
      } else {
        cur := x;
        assert cur == SumRange(xs, k, k + 1);
      }

      // Every sublist ending at k is bounded by the new cur.
      assert forall i {:trigger SumRange(xs, i, k + 1)} :: 0 <= i < k + 1 ==> SumRange(xs, i, k + 1) <= cur;

      if cur > m {
        m := cur;
      }

      k := k + 1;
    }
  }
}
