module Solution {

  // Strict lexicographic order on sequences of equal length.
  predicate LexLt(a: seq<int>, b: seq<int>)
    requires |a| == |b|
    decreases |a|
  {
    |a| > 0 && (a[0] < b[0] || (a[0] == b[0] && LexLt(a[1..], b[1..])))
  }

  predicate NonInc(s: seq<int>) {
    forall t :: 0 <= t < |s| - 1 ==> s[t] >= s[t+1]
  }

  predicate NonDec(s: seq<int>) {
    forall t :: 0 <= t < |s| - 1 ==> s[t] <= s[t+1]
  }

  lemma LexFromWitness(x: seq<int>, y: seq<int>, k: int)
    requires |x| == |y|
    requires 0 <= k < |x|
    requires forall q :: 0 <= q < k ==> x[q] == y[q]
    requires x[k] < y[k]
    ensures LexLt(x, y)
    decreases k
  {
    if k > 0 {
      assert x[0] == y[0];
      LexFromWitness(x[1..], y[1..], k - 1);
    }
  }

  lemma LexWitness(x: seq<int>, y: seq<int>)
    requires |x| == |y|
    requires LexLt(x, y)
    ensures exists k :: 0 <= k < |x| && (forall q :: 0 <= q < k ==> x[q] == y[q]) && x[k] < y[k]
    decreases |x|
  {
    if x[0] < y[0] {
      assert 0 <= 0 < |x| && (forall q :: 0 <= q < 0 ==> x[q] == y[q]) && x[0] < y[0];
    } else {
      assert x[0] == y[0] && LexLt(x[1..], y[1..]);
      LexWitness(x[1..], y[1..]);
      var k :| 0 <= k < |x[1..]| && (forall q :: 0 <= q < k ==> x[1..][q] == y[1..][q]) && x[1..][k] < y[1..][k];
      assert 0 <= k + 1 < |x| && (forall q :: 0 <= q < k + 1 ==> x[q] == y[q]) && x[k+1] < y[k+1];
    }
  }

  lemma LexPrefix(pre: seq<int>, x: seq<int>, y: seq<int>)
    requires |x| == |y|
    requires LexLt(x, y)
    ensures LexLt(pre + x, pre + y)
  {
    LexWitness(x, y);
    var k :| 0 <= k < |x| && (forall q :: 0 <= q < k ==> x[q] == y[q]) && x[k] < y[k];
    assert forall q :: 0 <= q < |pre| + k ==> (pre + x)[q] == (pre + y)[q];
    LexFromWitness(pre + x, pre + y, |pre| + k);
  }

  // Splitting off the head of a non-empty sequence.
  lemma MS1(s: seq<int>)
    requires |s| > 0
    ensures multiset(s) == multiset{s[0]} + multiset(s[1..])
  {
    assert s == [s[0]] + s[1..];
  }

  // Cancellation of a common multiset summand.
  lemma Cancel(A: multiset<int>, X: multiset<int>, Y: multiset<int>)
    requires A + X == A + Y
    ensures X == Y
  {
    forall v: int ensures X[v] == Y[v] {
      assert (A + X)[v] == (A + Y)[v];
    }
  }

  lemma MemIdx(s: seq<int>, x: int)
    requires x in multiset(s)
    ensures exists q :: 0 <= q < |s| && s[q] == x
    decreases |s|
  {
    if |s| == 0 {
      assert multiset(s) == multiset{};
      assert false;
    } else if s[0] == x {
      assert 0 <= 0 < |s| && s[0] == x;
    } else {
      MS1(s);
      MemIdx(s[1..], x);
      var q :| 0 <= q < |s[1..]| && s[1..][q] == x;
      assert 0 <= q + 1 < |s| && s[q+1] == x;
    }
  }

  // Non-increasing run: s[m] <= s[k] for k <= m.
  lemma DecayFrom(s: seq<int>, k: int, m: int)
    requires 0 <= k <= m < |s|
    requires forall t :: k <= t < |s| - 1 ==> s[t] >= s[t+1]
    ensures s[m] <= s[k]
    decreases m - k
  {
    if k < m {
      DecayFrom(s, k, m - 1);
      assert s[m-1] >= s[m];
    }
  }

  // Non-decreasing run: s[k] <= s[m] for k <= m.
  lemma IncFrom(s: seq<int>, k: int, m: int)
    requires 0 <= k <= m < |s|
    requires forall t :: 0 <= t < |s| - 1 ==> s[t] <= s[t+1]
    ensures s[k] <= s[m]
    decreases m - k
  {
    if k < m {
      IncFrom(s, k, m - 1);
      assert s[m-1] <= s[m];
    }
  }

  // A non-decreasing sequence is lexicographically no larger than any permutation of it.
  lemma SortedMin(t: seq<int>, u: seq<int>)
    requires |t| == |u|
    requires forall q :: 0 <= q < |t| - 1 ==> t[q] <= t[q+1]
    requires multiset(t) == multiset(u)
    ensures t == u || LexLt(t, u)
    decreases |t|
  {
    if |t| == 0 {
      assert t == u;
    } else {
      assert u[0] in multiset(t) by {
        MS1(u);
      }
      assert u[0] in multiset(t);
      MemIdx(t, u[0]);
      var q :| 0 <= q < |t| && t[q] == u[0];
      IncFrom(t, 0, q);
      if u[0] > t[0] {
        assert LexLt(t, u);
      } else {
        assert u[0] == t[0];
        assert t == [t[0]] + t[1..];
        assert u == [t[0]] + u[1..];
        MS1(t);
        MS1(u);
        assert multiset{t[0]} + multiset(t[1..]) == multiset{t[0]} + multiset(u[1..]);
        Cancel(multiset{t[0]}, multiset(t[1..]), multiset(u[1..]));
        assert multiset(t[1..]) == multiset(u[1..]);
        SortedMin(t[1..], u[1..]);
        if t[1..] == u[1..] {
          assert t == u;
        } else {
          assert LexLt(t[1..], u[1..]);
          LexPrefix([t[0]], t[1..], u[1..]);
          assert LexLt(t, u);
        }
      }
    }
  }

  // Equal prefixes and equal multisets give equal remaining multisets.
  lemma PrefixCancel(x: seq<int>, y: seq<int>, k: int)
    requires |x| == |y|
    requires 0 <= k <= |x|
    requires x[..k] == y[..k]
    requires multiset(x) == multiset(y)
    ensures multiset(x[k..]) == multiset(y[k..])
  {
    assert x == x[..k] + x[k..];
    assert y == y[..k] + y[k..];
    assert multiset(x) == multiset(x[..k]) + multiset(x[k..]);
    assert multiset(y) == multiset(y[..k]) + multiset(y[k..]);
    assert multiset(x[..k]) == multiset(y[..k]);
    Cancel(multiset(x[..k]), multiset(x[k..]), multiset(y[k..]));
  }

  lemma UpdMS(s: seq<int>, k: int, v: int)
    requires 0 <= k < |s|
    ensures multiset(s[k := v]) == multiset(s) - multiset{s[k]} + multiset{v}
  {
    assert s == s[..k] + [s[k]] + s[k+1..];
    assert s[k := v] == s[..k] + [v] + s[k+1..];
  }

  // Reverse the segment a[lo..] in place (returning a new sequence).
  method ReverseFrom(a: seq<int>, lo: int) returns (b: seq<int>)
    requires 0 <= lo <= |a|
    ensures |b| == |a|
    ensures b[..lo] == a[..lo]
    ensures forall q :: lo <= q < |a| ==> b[q] == a[lo + |a| - 1 - q]
    ensures multiset(b) == multiset(a)
  {
    var rev: seq<int> := [];
    var t := |a|;
    assert a[lo..t] == a[lo..];
    while t > lo
      invariant lo <= t <= |a|
      invariant |rev| == |a| - t
      invariant forall q :: 0 <= q < |rev| ==> rev[q] == a[|a| - 1 - q]
      invariant multiset(a[lo..]) == multiset(rev) + multiset(a[lo..t])
    {
      assert a[lo..t] == a[lo..t-1] + [a[t-1]];
      rev := rev + [a[t-1]];
      t := t - 1;
    }
    assert a[lo..lo] == [];
    assert a == a[..lo] + a[lo..];
    b := a[..lo] + rev;
  }

  // Key minimality argument for a single permutation p > xs.
  lemma Minimal(xs: seq<int>, r: seq<int>, i: int, j: int, p: seq<int>)
    requires 0 <= i < j < |xs|
    requires i + 1 <= j
    requires forall t :: i + 1 <= t < |xs| - 1 ==> xs[t] >= xs[t+1]
    requires xs[j] > xs[i]
    requires forall t :: j < t < |xs| ==> xs[t] <= xs[i]
    requires |r| == |xs|
    requires multiset(r) == multiset(xs)
    requires forall q :: 0 <= q < i ==> r[q] == xs[q]
    requires r[i] == xs[j]
    requires forall q :: i + 1 <= q < |xs| - 1 ==> r[q] <= r[q+1]
    requires |p| == |xs|
    requires multiset(p) == multiset(xs)
    requires LexLt(xs, p)
    ensures LexLt(r, p) || r == p
  {
    var n := |xs|;
    LexWitness(xs, p);
    var k :| 0 <= k < n && (forall q :: 0 <= q < k ==> xs[q] == p[q]) && xs[k] < p[k];
    if k < i {
      assert forall q :: 0 <= q < k ==> r[q] == p[q];
      assert r[k] == xs[k];
      LexFromWitness(r, p, k);
    } else if k == i {
      assert xs[..i] == p[..i];
      PrefixCancel(xs, p, i);
      assert multiset(p[i..]) == multiset(xs[i..]);
      MS1(p[i..]);
      assert p[i] in multiset(xs[i..]);
      MemIdx(xs[i..], p[i]);
      var q :| 0 <= q < |xs[i..]| && xs[i..][q] == p[i];
      var m := i + q;
      assert xs[m] == p[i];
      assert m >= i + 1;   // because xs[i] < p[i]
      if m > j {
        assert xs[m] <= xs[i];
        assert false;
      }
      assert m <= j;
      DecayFrom(xs, m, j);
      assert xs[j] <= p[i];
      if p[i] > xs[j] {
        assert forall q :: 0 <= q < i ==> r[q] == p[q];
        assert r[i] < p[i];
        LexFromWitness(r, p, i);
      } else {
        assert p[i] == xs[j];
        assert r[..i+1] == p[..i+1];
        PrefixCancel(r, p, i + 1);
        assert forall q {:trigger r[i+1..][q]} :: 0 <= q < |r[i+1..]| - 1 ==> r[i+1..][q] <= r[i+1..][q+1];
        SortedMin(r[i+1..], p[i+1..]);
        if r[i+1..] == p[i+1..] {
          assert r == r[..i+1] + r[i+1..];
          assert p == p[..i+1] + p[i+1..];
          assert r == p;
        } else {
          assert LexLt(r[i+1..], p[i+1..]);
          LexPrefix(r[..i+1], r[i+1..], p[i+1..]);
          assert r[..i+1] + r[i+1..] == r;
          assert r[..i+1] + p[i+1..] == p;
          assert LexLt(r, p);
        }
      }
    } else {
      // k > i: xs[k] is the maximum of xs[k..], so p[k] <= xs[k], contradiction.
      assert xs[..k] == p[..k];
      PrefixCancel(xs, p, k);
      MS1(p[k..]);
      assert p[k] in multiset(xs[k..]);
      MemIdx(xs[k..], p[k]);
      var q :| 0 <= q < |xs[k..]| && xs[k..][q] == p[k];
      DecayFrom(xs, k, k + q);
      assert xs[k + q] == p[k];
      assert xs[k] >= p[k];
      assert false;
    }
  }

  method next_permutation(xs: seq<int>) returns (r: seq<int>)
    ensures |r| == |xs|
    ensures multiset(r) == multiset(xs)
    ensures NonInc(xs) ==> NonDec(r)
    ensures !NonInc(xs) ==> LexLt(xs, r)
    ensures !NonInc(xs) ==>
              forall p: seq<int> | |p| == |xs| && multiset(p) == multiset(xs) && LexLt(xs, p)
                :: LexLt(r, p) || r == p
  {
    var n := |xs|;
    if n <= 1 {
      r := xs;
      return;
    }

    // Pivot: largest i with xs[i] < xs[i+1]; xs[i+1..] is non-increasing.
    var i := n - 2;
    while i >= 0 && xs[i] >= xs[i+1]
      invariant -1 <= i <= n - 2
      invariant forall t :: i < t < n - 1 ==> xs[t] >= xs[t+1]
      decreases i + 1
    {
      i := i - 1;
    }

    if i < 0 {
      assert NonInc(xs);
      r := ReverseFrom(xs, 0);
      assert NonDec(r) by {
        forall t | 0 <= t < |r| - 1 ensures r[t] <= r[t+1] {
          assert r[t] == xs[n - 1 - t];
          assert r[t+1] == xs[n - 2 - t];
          assert xs[n - 2 - t] >= xs[n - 1 - t];
        }
      }
      return;
    }

    assert xs[i] < xs[i+1];
    assert !NonInc(xs) by {
      if NonInc(xs) {
        assert xs[i] >= xs[i+1];
      }
    }

    // Successor index: largest j with xs[j] > xs[i].
    var j := n - 1;
    while xs[j] <= xs[i]
      invariant i + 1 <= j <= n - 1
      invariant forall t :: j < t < n ==> xs[t] <= xs[i]
      decreases j - i
    {
      j := j - 1;
    }
    assert xs[j] > xs[i];

    // Swap positions i and j.
    var s1 := xs[i := xs[j]];
    var s := s1[j := xs[i]];
    UpdMS(xs, i, xs[j]);
    UpdMS(s1, j, xs[i]);
    assert |s| == n;
    assert multiset(s) == multiset(xs);

    // After the swap, the suffix from i+1 is non-increasing.
    assert forall t :: i + 1 <= t < n - 1 ==> s[t] >= s[t+1] by {
      forall t | i + 1 <= t < n - 1 ensures s[t] >= s[t+1] {
        if t + 1 == j {
          DecayFrom(xs, t, j);
        }
        if t == j {
          assert xs[t+1] <= xs[i];
        }
      }
    }

    // Reverse the suffix from i+1 so that it becomes non-decreasing.
    r := ReverseFrom(s, i + 1);
    assert forall q :: i + 1 <= q < n - 1 ==> r[q] <= r[q+1] by {
      forall q | i + 1 <= q < n - 1 ensures r[q] <= r[q+1] {
        var x := i + n - q - 1;
        assert s[x] >= s[x+1];
      }
    }
    assert forall q :: 0 <= q < i ==> r[q] == xs[q];
    assert r[i] == xs[j];

    LexFromWitness(xs, r, i);
    assert LexLt(xs, r);

    forall p: seq<int> | |p| == |xs| && multiset(p) == multiset(xs) && LexLt(xs, p)
      ensures LexLt(r, p) || r == p
    {
      Minimal(xs, r, i, j, p);
    }
  }
}
