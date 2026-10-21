module Solution {
  method rotate(xs: seq<int>, k: int) returns (r: seq<int>)
    ensures |r| == |xs|
    ensures forall i :: 0 <= i < |xs| ==> r[i] == xs[(i - k) % |xs|]
  {
    var n := |xs|;
    if n == 0 {
      r := [];
      return;
    }
    var s := k % n;
    r := xs[n - s..] + xs[..n - s];
    forall i | 0 <= i < n
      ensures r[i] == xs[(i - k) % n]
    {
      // k == q*n + s, so (i - k) % n == (i - s) % n
      var q := k / n;
      assert k == q * n + s;
      if i < s {
        assert r[i] == xs[n - s + i];
        ModShift(i - s + n, -q - 1, n);
        assert (i - k) == (i - s + n) + (-q - 1) * n;
      } else {
        assert r[i] == xs[i - s];
        ModShift(i - s, -q, n);
        assert (i - k) == (i - s) + (-q) * n;
      }
    }
  }

  lemma ModShift(a: int, m: int, n: int)
    requires n > 0 && 0 <= a < n
    ensures (a + m * n) % n == a
  {
    var b := a + m * n;
    assert b == m * n + a;
    // uniqueness of Euclidean division
    var q2 := b / n;
    var r2 := b % n;
    assert b == q2 * n + r2 && 0 <= r2 < n;
    if q2 > m {
      MulGe(q2 - m, n);
      assert q2 * n - m * n == (q2 - m) * n;
    } else if q2 < m {
      MulGe(m - q2, n);
      assert m * n - q2 * n == (m - q2) * n;
    }
  }

  lemma MulGe(d: int, n: int)
    requires d >= 1 && n > 0
    ensures d * n >= n
  {
    assert d * n == (d - 1) * n + n;
    assert (d - 1) * n >= 0;
  }
}
