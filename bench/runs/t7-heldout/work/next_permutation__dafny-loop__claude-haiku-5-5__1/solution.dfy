module Solution {

  // Non-decreasing sequence.
  predicate Sorted(s: seq<int>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  }

  // Non-increasing sequence (no ascent, i.e. greatest arrangement).
  predicate Desc(s: seq<int>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] >= s[j]
  }

  // r is the result obtained from xs by pivoting at index k:
  // same prefix, larger value at k (the smallest such available value),
  // and the remaining suffix of r is ascending while the suffix of xs is descending.
  predicate IsNextAt(xs: seq<int>, r: seq<int>, k: int) {
    0 <= k < |xs| && |r| == |xs| && k < |r|
    && r[..k] == xs[..k]
    && xs[k] < r[k]
    && (forall i :: k < i < |xs| ==> (xs[i] <= xs[k] || r[k] <= xs[i]))
    && Sorted(r[k+1..])
    && Desc(xs[k+1..])
  }

  function Rev(s: seq<int>): seq<int>
    decreases |s|
  {
    if |s| == 0 then [] else Rev(s[1..]) + [s[0]]
  }

  lemma RevLen(s: seq<int>)
    ensures |Rev(s)| == |s|
    decreases |s|
  {
    if |s| > 0 {
      RevLen(s[1..]);
    }
  }

  lemma RevMulti(s: seq<int>)
    ensures multiset(Rev(s)) == multiset(s)
    decreases |s|
  {
    if |s| > 0 {
      RevMulti(s[1..]);
      assert s == [s[0]] + s[1..];
    }
  }

  lemma RevIdx(s: seq<int>, i: int)
    requires 0 <= i < |s|
    requires |Rev(s)| == |s|
    ensures Rev(s)[i] == s[|s| - 1 - i]
    decreases |s|
  {
    if |s| > 1 {
      RevLen(s[1..]);
    }
    if i < |s| - 1 {
      RevIdx(s[1..], i);
    }
  }

  lemma RevSorted(s: seq<int>)
    requires Desc(s)
    ensures Sorted(Rev(s))
  {
    RevLen(s);
    forall i, j | 0 <= i < j < |Rev(s)|
      ensures Rev(s)[i] <= Rev(s)[j]
    {
      RevIdx(s, i);
      RevIdx(s, j);
    }
  }

  method next_permutation(xs: seq<int>) returns (r: seq<int>)
    ensures multiset(r) == multiset(xs)
    ensures Desc(xs) ==> Sorted(r)
    ensures !Desc(xs) ==> exists k :: IsNextAt(xs, r, k)
  {
    var n := |xs|;
    if n <= 1 {
      return xs;
    }

    // Find the pivot: the largest k with xs[k] < xs[k+1].
    var k := n - 2;
    while k >= 0 && xs[k] >= xs[k+1]
      invariant -1 <= k <= n - 2
      invariant forall i, j :: k < i < j < n ==> xs[i] >= xs[j]
      decreases k
    {
      k := k - 1;
    }

    if k < 0 {
      // xs is non-increasing: its smallest arrangement is its reverse.
      assert Desc(xs);
      RevSorted(xs);
      RevMulti(xs);
      r := Rev(xs);
      return;
    }

    assert xs[k] < xs[k+1];

    // Find the rightmost l > k with xs[l] > xs[k].
    var l := n - 1;
    while xs[l] <= xs[k]
      invariant k < l <= n - 1
      invariant xs[k] < xs[k+1]
      invariant forall j :: l < j < n ==> xs[j] <= xs[k]
      decreases l
    {
      l := l - 1;
    }

    // Next permutation: prefix, swap pivot, reverse the (descending) rest.
    var P := xs[..k];
    var S := xs[k+1..l] + [xs[k]] + xs[l+1..];
    assert |S| == n - k - 1;

    // S is non-increasing.
    assert Desc(S);
    RevSorted(S);
    RevMulti(S);
    var T := Rev(S);
    r := P + [xs[l]] + T;

    // Multiset preservation.
    assert xs[k..] == [xs[k]] + xs[k+1..l] + [xs[l]] + xs[l+1..];
    assert xs == P + xs[k..];
    assert multiset(xs) == multiset(P) + multiset{xs[k]} + multiset(xs[k+1..l])
                           + multiset{xs[l]} + multiset(xs[l+1..]);
    assert multiset(S) == multiset(xs[k+1..l]) + multiset{xs[k]} + multiset(xs[l+1..]);
    assert multiset(r) == multiset(P) + multiset{xs[l]} + multiset(T);
    assert multiset(T) == multiset(S);
    assert multiset(r) == multiset(xs);

    // Witness: the pivot is k.
    assert r[..k] == xs[..k] by {
      assert r == P + ([xs[l]] + T);
    }
    assert r[k] == xs[l];
    assert r[k+1..] == T;
    assert |r| == |xs|;
    assert IsNextAt(xs, r, k);

    assert !Desc(xs);
    assert exists kk :: IsNextAt(xs, r, kk) by {
      assert IsNextAt(xs, r, k);
    }
  }
}
