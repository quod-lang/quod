module Solution {

  // Sum of the elements xs[i..j) (half-open range).
  function SumRange(xs: seq<int>, i: int, j: int): int
    requires 0 <= i <= j <= |xs|
    decreases j - i
  {
    if i == j then 0 else SumRange(xs, i, j - 1) + xs[j - 1]
  }

  // Extending a range by one element on the right adds that element.
  lemma SumRangeExtend(xs: seq<int>, i: int, j: int)
    requires 0 <= i <= j < |xs|
    ensures SumRange(xs, i, j + 1) == SumRange(xs, i, j) + xs[j]
  {
  }

  // Kadane's algorithm, O(n).
  method max_subarray(xs: seq<int>) returns (m: int)
    requires |xs| > 0
    ensures exists i, j :: 0 <= i < j <= |xs| && m == SumRange(xs, i, j)
    ensures forall i, j :: 0 <= i < j <= |xs| ==> SumRange(xs, i, j) <= m
  {
    var n := |xs|;
    // cur: best sum of a non-empty suffix of xs[0..k), realised by xs[ci..k)
    var cur := xs[0];
    var ci := 0;
    // best: best sum of a non-empty subarray within xs[0..k), realised by xs[bi..bj)
    var best := xs[0];
    var bi := 0;
    var bj := 1;
    var k := 1;

    while k < n
      invariant 1 <= k <= n
      invariant 0 <= ci < k
      invariant cur == SumRange(xs, ci, k)
      invariant forall i :: 0 <= i < k ==> SumRange(xs, i, k) <= cur
      invariant 0 <= bi < bj <= k
      invariant best == SumRange(xs, bi, bj)
      invariant forall i, j :: 0 <= i < j <= k ==> SumRange(xs, i, j) <= best
      decreases n - k
    {
      forall i | 0 <= i <= k
        ensures SumRange(xs, i, k + 1) == SumRange(xs, i, k) + xs[k]
      {
        SumRangeExtend(xs, i, k);
      }

      if cur < 0 {
        // Restart the suffix at position k.
        cur := xs[k];
        ci := k;
      } else {
        cur := cur + xs[k];
      }

      // Every suffix ending at k+1 is bounded by the new cur.
      assert forall i {:trigger SumRange(xs, i, k + 1)} :: 0 <= i < k + 1 ==> SumRange(xs, i, k + 1) <= cur;

      if cur > best {
        best := cur;
        bi := ci;
        bj := k + 1;
      }

      k := k + 1;
    }

    m := best;
    assert 0 <= bi < bj <= |xs| && m == SumRange(xs, bi, bj);
  }
}
