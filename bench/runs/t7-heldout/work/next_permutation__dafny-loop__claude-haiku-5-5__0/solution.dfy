module Solution {

  // xs is its own greatest rearrangement (no adjacent strict ascent)
  predicate NonIncr(s: seq<int>) {
    forall i :: 0 <= i < |s| - 1 ==> s[i] >= s[i + 1]
  }

  predicate NonDecr(s: seq<int>) {
    forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
  }

  // k is the last ascent position: xs[k] < xs[k+1] and everything after k is non-increasing.
  // Such a k is unique when it exists.
  predicate IsPivot(xs: seq<int>, k: int) {
    0 <= k < |xs| - 1 && xs[k] < xs[k + 1] &&
    forall j :: k < j < |xs| - 1 ==> xs[j] >= xs[j + 1]
  }

  // r is the next permutation of xs, given that the last ascent of xs is at k:
  // r agrees with xs before k, r[k] is the smallest value after k exceeding xs[k],
  // and the tail after k is ascending. (Multiset equality is stated separately.)
  predicate IsNext(xs: seq<int>, r: seq<int>, k: int) {
    |r| == |xs| && 0 <= k < |xs| &&
    (forall i :: 0 <= i < k ==> r[i] == xs[i]) &&
    r[k] > xs[k] &&
    (forall j :: k < j < |xs| && xs[j] > xs[k] ==> r[k] <= xs[j]) &&
    (forall i :: k + 1 <= i < |r| - 1 ==> r[i] <= r[i + 1])
  }

  // Reversal, used only in specifications.
  ghost function RevSeq(s: seq<int>): seq<int>
    decreases |s|
  {
    if |s| == 0 then [] else RevSeq(s[1..]) + [s[0]]
  }

  lemma RevLen(s: seq<int>)
    ensures |RevSeq(s)| == |s|
    decreases |s|
  {
    if |s| > 0 {
      RevLen(s[1..]);
    }
  }

  lemma RevMs(s: seq<int>)
    ensures multiset(RevSeq(s)) == multiset(s)
    decreases |s|
  {
    if |s| > 0 {
      RevMs(s[1..]);
      assert s == [s[0]] + s[1..];
    }
  }

  lemma RevIdx(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures i < |RevSeq(s)| && RevSeq(s)[i] == s[|s| - 1 - i]
    decreases |s|
  {
    RevLen(s);
    if |s| > 1 {
      RevLen(s[1..]);
      if i < |s| - 1 {
        RevIdx(s[1..], i);
      }
    }
  }

  lemma RevSnoc(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures RevSeq(s[i..]) == RevSeq(s[i + 1..]) + [s[i]]
  {
    assert s[i..] == [s[i]] + s[i + 1..];
    assert RevSeq(s[i..]) == RevSeq(s[i..][1..]) + [s[i..][0]];
    assert s[i..][1..] == s[i + 1..];
  }

  lemma NonIncrChain(s: seq<int>, a: int, b: int)
    requires 0 <= a <= b < |s|
    requires forall i :: a <= i < b ==> s[i] >= s[i + 1]
    ensures s[a] >= s[b]
    decreases b - a
  {
    if a < b {
      NonIncrChain(s, a + 1, b);
    }
  }

  // Reverses the suffix s[p..] of a sequence whose suffix is non-increasing,
  // yielding an ascending suffix.
  method ReverseSuffix(s: seq<int>, p: int) returns (r: seq<int>)
    requires 0 <= p <= |s|
    requires forall i :: p <= i < |s| - 1 ==> s[i] >= s[i + 1]
    ensures |r| == |s|
    ensures multiset(r) == multiset(s)
    ensures forall t :: 0 <= t < p ==> r[t] == s[t]
    ensures forall t :: p <= t < |s| - 1 ==> r[t] <= r[t + 1]
  {
    var n := |s|;
    r := s[..p];
    var i := n;
    while i > p
      invariant p <= i <= n
      invariant r == s[..p] + RevSeq(s[i..])
      decreases i
    {
      RevSnoc(s, i - 1);
      r := r + [s[i - 1]];
      i := i - 1;
    }
    assert s == s[..p] + s[p..];
    assert r == s[..p] + RevSeq(s[p..]);
    RevLen(s[p..]);
    RevMs(s[p..]);
    assert |r| == |s|;
    assert multiset(r) == multiset(s);
    forall t | p <= t < n - 1
      ensures r[t] <= r[t + 1]
    {
      var u := t - p;
      var m := n - p;
      assert |s[p..]| == m;
      RevIdx(s[p..], u);
      RevIdx(s[p..], u + 1);
      assert r[t] == RevSeq(s[p..])[u];
      assert r[t + 1] == RevSeq(s[p..])[u + 1];
      assert s[p..][m - 1 - u] == s[p + m - 1 - u];
      assert s[p..][m - 1 - (u + 1)] == s[p + m - 1 - (u + 1)];
      assert s[p + m - 1 - u] == s[n - 1 - u];
      assert s[p + m - 1 - (u + 1)] == s[n - 2 - u];
      assert s[n - 2 - u] >= s[n - 1 - u];
    }
  }

  method next_permutation(xs: seq<int>) returns (r: seq<int>)
    ensures multiset(r) == multiset(xs)
    ensures NonIncr(xs) ==> NonDecr(r)
    ensures !NonIncr(xs) ==> forall k :: IsPivot(xs, k) ==> IsNext(xs, r, k)
  {
    var n := |xs|;
    if n < 2 {
      return xs;
    }

    // last ascent position
    var k := n - 2;
    while k >= 0 && xs[k] >= xs[k + 1]
      invariant -1 <= k <= n - 2
      invariant forall j :: k < j < n - 1 ==> xs[j] >= xs[j + 1]
      decreases k + 1
    {
      k := k - 1;
    }

    if k < 0 {
      assert NonIncr(xs);
      r := ReverseSuffix(xs, 0);
      return;
    }

    // rightmost position holding a value greater than xs[k]
    var l := n - 1;
    while xs[l] <= xs[k]
      invariant k < l <= n - 1
      invariant forall j :: l < j < n ==> xs[j] <= xs[k]
      decreases l - k
    {
      l := l - 1;
    }

    var t := xs[k];
    var s := xs[k := xs[l]][l := t];
    assert multiset(s) == multiset(xs);

    forall i | k + 1 <= i < n - 1
      ensures s[i] >= s[i + 1]
    {
      if i + 1 < l {
        assert s[i] == xs[i] && s[i + 1] == xs[i + 1];
      } else if i + 1 == l {
        assert s[i] == xs[i] && s[i + 1] == xs[k];
        assert xs[i] >= xs[i + 1];
        assert xs[i + 1] > xs[k];
      } else if i == l {
        assert s[i] == xs[k] && s[i + 1] == xs[i + 1];
        assert xs[i + 1] <= xs[k];
      } else {
        assert s[i] == xs[i] && s[i + 1] == xs[i + 1];
      }
    }

    r := ReverseSuffix(s, k + 1);

    // minimality of r[k] = xs[l]
    forall j | k < j < n && xs[j] > xs[k]
      ensures xs[l] <= xs[j]
    {
      assert j <= l;
      NonIncrChain(xs, j, l);
    }
    assert IsNext(xs, r, k);

    // uniqueness of the pivot
    forall k2 | IsPivot(xs, k2)
      ensures IsNext(xs, r, k2)
    {
      if k2 > k {
        assert xs[k2] >= xs[k2 + 1];
      }
      if k2 < k {
        assert xs[k] >= xs[k + 1];
      }
    }
  }
}
