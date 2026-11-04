module Solution {

  // s is sorted in non-decreasing order
  predicate Sorted(s: seq<int>) {
    forall a, b :: 0 <= a < b < |s| ==> s[a] <= s[b]
  }

  // a is lexicographically strictly smaller than b
  predicate LexLt(a: seq<int>, b: seq<int>)
    decreases |a|
  {
    |a| > 0 && |b| > 0 &&
    (a[0] < b[0] || (a[0] == b[0] && LexLt(a[1..], b[1..])))
  }

  lemma MsSplit(s: seq<int>, k: int)
    requires 0 <= k <= |s|
    ensures multiset(s) == multiset(s[..k]) + multiset(s[k..])
  {
    assert s == s[..k] + s[k..];
  }

  lemma MsCancel(a: multiset<int>, b: multiset<int>, c: multiset<int>)
    requires a + b == a + c
    ensures b == c
  {
    assert forall z :: b[z] == c[z] by {
      forall z ensures b[z] == c[z] {
        assert (a + b)[z] == (a + c)[z];
      }
    }
  }

  // If p and xs agree on a prefix of length k and are rearrangements, their suffixes are too
  lemma PrefixCancel(p: seq<int>, xs: seq<int>, k: int)
    requires |p| == |xs|
    requires 0 <= k <= |p|
    requires p[..k] == xs[..k]
    requires multiset(p) == multiset(xs)
    ensures multiset(p[k..]) == multiset(xs[k..])
  {
    MsSplit(p, k);
    MsSplit(xs, k);
    MsCancel(multiset(xs[..k]), multiset(p[k..]), multiset(xs[k..]));
  }

  lemma LexFirstDiff(a: seq<int>, b: seq<int>)
    requires |a| == |b|
    requires LexLt(a, b)
    ensures exists k :: 0 <= k < |a| && a[..k] == b[..k] && a[k] < b[k]
    decreases |a|
  {
    if a[0] < b[0] {
      assert 0 <= 0 < |a| && a[..0] == b[..0] && a[0] < b[0];
    } else {
      LexFirstDiff(a[1..], b[1..]);
      var k :| 0 <= k < |a| - 1 && a[1..][..k] == b[1..][..k] && a[1..][k] < b[1..][k];
      assert a[..k + 1] == b[..k + 1];
      assert 0 <= k + 1 < |a| && a[..k + 1] == b[..k + 1] && a[k + 1] < b[k + 1];
    }
  }

  lemma LexWitness(a: seq<int>, b: seq<int>, k: int)
    requires |a| == |b|
    requires 0 <= k < |a|
    requires a[..k] == b[..k]
    requires a[k] < b[k]
    ensures LexLt(a, b)
    decreases k
  {
    if k > 0 {
      assert a[0] == b[0];
      assert a[1..][..k - 1] == b[1..][..k - 1];
      LexWitness(a[1..], b[1..], k - 1);
    }
  }

  lemma LexPrefix(a: seq<int>, b: seq<int>, c: int)
    requires |a| == |b|
    requires 0 <= c <= |a|
    requires a[..c] == b[..c]
    requires LexLt(a[c..], b[c..])
    ensures LexLt(a, b)
    decreases c
  {
    if c > 0 {
      assert a[0] == b[0];
      assert a[1..][c - 1..] == a[c..];
      assert b[1..][c - 1..] == b[c..];
      assert a[1..][..c - 1] == b[1..][..c - 1];
      LexPrefix(a[1..], b[1..], c - 1);
    }
  }

  // A sorted sequence is lexicographically no larger than any rearrangement of it
  lemma SortedLe(s: seq<int>, q: seq<int>)
    requires |s| == |q|
    requires Sorted(s)
    requires multiset(s) == multiset(q)
    ensures s == q || LexLt(s, q)
    decreases |s|
  {
    if |s| > 0 {
      assert q[0] in multiset(q);
      assert q[0] in multiset(s);
      assert q[0] in s;
      var t :| 0 <= t < |s| && s[t] == q[0];
      assert s[0] <= s[t];
      if q[0] > s[0] {
        assert LexLt(s, q);
      } else {
        assert q[0] == s[0];
        assert s == [s[0]] + s[1..];
        assert q == [q[0]] + q[1..];
        assert multiset(s) == multiset{s[0]} + multiset(s[1..]);
        assert multiset(q) == multiset{q[0]} + multiset(q[1..]);
        MsCancel(multiset{s[0]}, multiset(s[1..]), multiset(q[1..]));
        assert Sorted(s[1..]);
        SortedLe(s[1..], q[1..]);
        if s[1..] == q[1..] {
          assert s == q;
        } else {
          assert LexLt(s, q);
        }
      }
    }
  }

  // Minimality of the successor: any rearrangement p greater than xs is >= r
  lemma Minimal(xs: seq<int>, r: seq<int>, p: seq<int>, i: int, j: int)
    requires 0 <= i < j < |xs|
    requires |r| == |xs|
    requires multiset(r) == multiset(xs)
    requires multiset(p) == multiset(xs)
    requires xs[i] < xs[j]
    requires forall a, b :: i < a < b < |xs| ==> xs[a] >= xs[b]
    requires forall m :: j < m < |xs| ==> xs[m] <= xs[i]
    requires forall m :: 0 <= m < i ==> r[m] == xs[m]
    requires r[i] == xs[j]
    requires Sorted(r[i + 1..])
    requires LexLt(xs, p)
    ensures r == p || LexLt(r, p)
  {
    var n := |xs|;
    assert |p| == n;
    LexFirstDiff(xs, p);
    var k :| 0 <= k < n && xs[..k] == p[..k] && xs[k] < p[k];
    if k < i {
      assert r[..k] == p[..k];
      assert r[k] == xs[k];
      LexWitness(r, p, k);
    } else if k > i {
      // p[k] occurs in xs[k..], which is non-increasing, so p[k] <= xs[k]
      PrefixCancel(p, xs, k);
      assert p[k] in p[k..];
      assert p[k] in multiset(p[k..]);
      assert p[k] in multiset(xs[k..]);
      assert p[k] in xs[k..];
      var m :| k <= m < n && xs[m] == p[k];
      assert xs[k] >= xs[m];
      assert false;
    } else {
      // k == i : p[i] > xs[i] occurs at some m > i
      PrefixCancel(p, xs, i);
      assert p[i] in p[i..];
      assert p[i] in multiset(p[i..]);
      assert p[i] in multiset(xs[i..]);
      assert p[i] in xs[i..];
      var m :| i <= m < n && xs[m] == p[i];
      assert m > i;
      assert m <= j;   // otherwise xs[m] <= xs[i] < p[i]
      assert xs[j] <= xs[m];
      assert r[i] <= p[i];
      if xs[j] < p[i] {
        assert r[..i] == p[..i];
        assert r[i] < p[i];
        LexWitness(r, p, i);
      } else {
        assert r[i] == p[i];
        assert r[..i + 1] == p[..i + 1];
        PrefixCancel(r, p, i + 1);
        SortedLe(r[i + 1..], p[i + 1..]);
        if r[i + 1..] == p[i + 1..] {
          assert r == r[..i + 1] + r[i + 1..];
          assert p == p[..i + 1] + p[i + 1..];
          assert r == p;
        } else {
          LexPrefix(r, p, i + 1);
        }
      }
    }
  }

  // Final bookkeeping for the pivot case: r = xs[..i] + [xs[j]] + T, where T is the
  // reverse of y[i+1..] and y is xs with position j replaced by xs[i]
  lemma SwapMs(xs: seq<int>, y: seq<int>, T: seq<int>, r: seq<int>, i: int, j: int)
    requires 0 <= i < j < |xs|
    requires y == xs[j := xs[i]]
    requires multiset(T) == multiset(y[i + 1..|xs|])
    requires r == xs[..i] + [xs[j]] + T
    ensures multiset(r) == multiset(xs)
  {
    var n := |xs|;
    assert y[i + 1..n] == xs[i + 1..j] + [xs[i]] + xs[j + 1..n];
    assert xs[i + 1..n] == xs[i + 1..j] + [xs[j]] + xs[j + 1..n];
    assert xs == xs[..i] + [xs[i]] + xs[i + 1..];
    assert xs[i + 1..] == xs[i + 1..n];
    assert multiset(xs) == multiset(xs[..i]) + multiset{xs[i]} + multiset(xs[i + 1..n]);
    assert multiset(xs[i + 1..n]) == multiset(xs[i + 1..j]) + multiset{xs[j]} + multiset(xs[j + 1..n]);
    assert multiset(y[i + 1..n]) == multiset(xs[i + 1..j]) + multiset{xs[i]} + multiset(xs[j + 1..n]);
    assert r == xs[..i] + [xs[j]] + T;
    assert multiset(r) == multiset(xs[..i]) + multiset{xs[j]} + multiset(y[i + 1..n]);
  }

  lemma MinimalAll(xs: seq<int>, r: seq<int>, T: seq<int>, i: int, j: int)
    requires 0 <= i < j < |xs|
    requires |r| == |xs|
    requires multiset(r) == multiset(xs)
    requires xs[i] < xs[j]
    requires forall a, b :: i < a < b < |xs| ==> xs[a] >= xs[b]
    requires forall m :: j < m < |xs| ==> xs[m] <= xs[i]
    requires Sorted(T)
    requires r == xs[..i] + [xs[j]] + T
    ensures LexLt(xs, r)
    ensures forall p: seq<int> | multiset(p) == multiset(xs) && LexLt(xs, p) :: r == p || LexLt(r, p)
  {
    assert forall m :: 0 <= m < i ==> r[m] == xs[m];
    assert r[i] == xs[j];
    assert r[i + 1..] == T;
    assert xs[..i] == r[..i];
    LexWitness(xs, r, i);
    forall p: seq<int> | multiset(p) == multiset(xs) && LexLt(xs, p)
      ensures r == p || LexLt(r, p)
    {
      Minimal(xs, r, p, i, j);
    }
  }

  lemma Conclude(xs: seq<int>, y: seq<int>, T: seq<int>, r: seq<int>, i: int, j: int)
    requires 0 <= i < j < |xs|
    requires y == xs[j := xs[i]]
    requires xs[i] < xs[j]
    requires forall a, b :: i < a < b < |xs| ==> xs[a] >= xs[b]
    requires forall m :: j < m < |xs| ==> xs[m] <= xs[i]
    requires Sorted(T)
    requires multiset(T) == multiset(y[i + 1..|xs|])
    requires r == xs[..i] + [xs[j]] + T
    requires |T| == |xs| - i - 1
    ensures |r| == |xs|
    ensures multiset(r) == multiset(xs)
    ensures LexLt(xs, r)
    ensures forall p: seq<int> | multiset(p) == multiset(xs) && LexLt(xs, p) :: r == p || LexLt(r, p)
  {
    assert |r| == |xs|;
    SwapMs(xs, y, T, r, i, j);
    MinimalAll(xs, r, T, i, j);
  }

  method next_permutation(xs: seq<int>) returns (r: seq<int>)
    ensures |r| == |xs|
    ensures multiset(r) == multiset(xs)
    ensures (exists a :: 0 <= a < |xs| - 1 && xs[a] < xs[a + 1]) ==>
              LexLt(xs, r) &&
              forall p: seq<int> | multiset(p) == multiset(xs) && LexLt(xs, p) :: r == p || LexLt(r, p)
    ensures (forall a :: 0 <= a < |xs| - 1 ==> xs[a] >= xs[a + 1]) ==> Sorted(r)
  {
    var n := |xs|;
    if n <= 1 {
      return xs;
    }

    // Step 1: i = largest index with xs[i] < xs[i+1]; the suffix after i is non-increasing
    var i := n - 2;
    while i >= 0 && xs[i] >= xs[i + 1]
      invariant -1 <= i <= n - 2
      invariant forall a, b :: i < a < b < n ==> xs[a] >= xs[b]
      decreases i
    {
      i := i - 1;
    }

    if i < 0 {
      // xs is its own greatest rearrangement: answer is its reverse (ascending)
      var T: seq<int> := [];
      var k := 0;
      while k < n
        invariant 0 <= k <= n
        invariant |T| == k
        invariant multiset(T) == multiset(xs[..k])
        invariant Sorted(T)
        invariant |T| > 0 ==> T[0] == xs[k - 1]
        invariant forall a, b :: 0 <= a < b < n ==> xs[a] >= xs[b]
      {
        assert xs[..k + 1] == xs[..k] + [xs[k]];
        T := [xs[k]] + T;
        k := k + 1;
      }
      assert xs[..n] == xs;
      r := T;
      return;
    }

    // i is a pivot
    assert xs[i] < xs[i + 1];

    // Step 2: j = largest index > i with xs[j] > xs[i]
    var j := n - 1;
    while xs[j] <= xs[i]
      invariant i + 1 <= j <= n - 1
      invariant forall m :: j < m < n ==> xs[m] <= xs[i]
      decreases j - i
    {
      j := j - 1;
    }
    assert i < j < n && xs[i] < xs[j];

    // Step 3: swap, then reverse the suffix after i (built directly from y)
    var y := xs[j := xs[i]];
    var lo := i + 1;
    var head := xs[..i] + [xs[j]];

    assert forall a, b :: lo <= a < b < n ==> y[a] >= y[b] by {
      forall a, b | lo <= a < b < n ensures y[a] >= y[b] {
        if b == j {
          assert y[b] == xs[i];
          assert xs[a] >= xs[j];
        } else if a == j {
          assert xs[b] <= xs[i];
        }
      }
    }

    var T: seq<int> := [];
    var k := lo;
    while k < n
      invariant lo <= k <= n
      invariant |T| == k - lo
      invariant multiset(T) == multiset(y[lo..k])
      invariant Sorted(T)
      invariant |T| > 0 ==> T[0] == y[k - 1]
      invariant forall a, b :: lo <= a < b < n ==> y[a] >= y[b]
    {
      assert y[lo..k + 1] == y[lo..k] + [y[k]];
      T := [y[k]] + T;
      k := k + 1;
    }

    r := head + T;
    assert k == n;
    assert |head| == i + 1;
    assert |T| == |xs| - i - 1;
    Conclude(xs, y, T, r, i, j);
  }
}
