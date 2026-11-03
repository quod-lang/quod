module Solution {

  // Sum of the half-open range xs[i..j) (empty when i == j).
  function RangeSum(xs: seq<int>, i: int, j: int): int
    requires 0 <= i <= j <= |xs|
    decreases j - i
  {
    if i == j then 0 else RangeSum(xs, i, j - 1) + xs[j - 1]
  }

  // Extending a range by one element adds that element to its sum.
  lemma RangeSumExtend(xs: seq<int>, i: int, j: int)
    requires 0 <= i <= j < |xs|
    ensures RangeSum(xs, i, j + 1) == RangeSum(xs, i, j) + xs[j]
  {
  }

  // Kadane's algorithm, O(n).
  method max_subarray(xs: seq<int>) returns (m: int)
    requires |xs| > 0
    ensures exists i, j :: 0 <= i < j <= |xs| && m == RangeSum(xs, i, j)
    ensures forall i, j :: 0 <= i < j <= |xs| ==> RangeSum(xs, i, j) <= m
  {
    var n := |xs|;
    // cur: best sum of a non-empty range ending at k-1, starting at curStart (ghost).
    var cur := xs[0];
    ghost var curStart := 0;
    // best: best sum of any non-empty range seen so far, realised by [bestI, bestJ) (ghost).
    var best := xs[0];
    ghost var bestI := 0;
    ghost var bestJ := 1;
    var k := 1;
    while k < n
      invariant 1 <= k <= n
      invariant 0 <= curStart < k
      invariant cur == RangeSum(xs, curStart, k)
      invariant forall i :: 0 <= i < k ==> RangeSum(xs, i, k) <= cur
      invariant 0 <= bestI < bestJ <= k
      invariant best == RangeSum(xs, bestI, bestJ)
      invariant forall i, j :: 0 <= i < j <= k ==> RangeSum(xs, i, j) <= best
      decreases n - k
    {
      forall i | 0 <= i <= k {
        RangeSumExtend(xs, i, k);
      }
      if cur < 0 {
        cur := xs[k];
        curStart := k;
      } else {
        cur := cur + xs[k];
      }
      k := k + 1;
      if best < cur {
        best := cur;
        bestI := curStart;
        bestJ := k;
      }
    }
    m := best;
    assert exists i, j :: 0 <= i < j <= |xs| && m == RangeSum(xs, i, j) by {
      assert 0 <= bestI < bestJ <= n && m == RangeSum(xs, bestI, bestJ);
    }
  }
}
