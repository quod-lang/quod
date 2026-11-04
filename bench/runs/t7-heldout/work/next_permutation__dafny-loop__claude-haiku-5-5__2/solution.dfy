module Solution {

  // p is a rearrangement of xs
  predicate IsPerm(p: seq<int>, xs: seq<int>) {
    |p| == |xs| && multiset(p) == multiset(xs)
  }

  // Strict lexicographic order on sequences
  predicate LexLt(a: seq<int>, b: seq<int>)
    decreases |a|
  {
    if |a| == 0 then |b| > 0
    else if |b| == 0 then false
    else if a[0] < b[0] then true
    else if a[0] > b[0] then false
    else LexLt(a[1..], b[1..])
  }

  predicate NonDecreasing(s: seq<int>) {
    forall a, b :: 0 <= a < b < |s| ==> s[a] <= s[b]
  }

  predicate NonIncreasing(s: seq<int>) {
    forall a, b :: 0 <= a < b < |s| ==> s[a] >= s[b]
  }

  function Rev(s: seq<int>): seq<int>
    decreases |s|
  {
    if |s| == 0 then [] else Rev(s[1..]) + [s[0]]
  }

  // Candidate successor: swap pivot i with partner j, then reverse the suffix after i.
  function Build(xs: seq<int>, i: int, j: int): seq<int>
    requires 0 <= i < j < |xs|
  {
    xs[..i] + [xs[j]] + Rev(xs[i+1..j] + [xs[i]] + xs[j+1..])
  }

  // ---------- helper lemmas ----------

  lemma InMS(s: seq<int>, x: int)
    ensures x in multiset(s) <==> x in s
    decreases |s|
  {
    if |s| > 0 {
      InMS(s[1..], x);
      assert s == [s[0]] + s[1..];
    }
  }

  lemma RevProps(s: seq<int>)
    ensures |Rev(s)| == |s|
    ensures multiset(Rev(s)) == multiset(s)
    ensures forall k :: 0 <= k < |s| ==> Rev(s)[k] == s[|s| - 1 - k]
    decreases |s|
  {
    if |s| > 0 {
      var t := s[1..];
      RevProps(t);
      assert s == [s[0]] + t;
      assert Rev(s) == Rev(t) + [s[0]];
      assert multiset(s) == multiset{s[0]} + multiset(t);
      assert multiset(Rev(s)) == multiset(Rev(t)) + multiset{s[0]};
      forall k | 0 <= k < |s| ensures Rev(s)[k] == s[|s| - 1 - k] {
        if k < |t| {
          assert Rev(s)[k] == Rev(t)[k];
          assert Rev(t)[k] == t[|t| - 1 - k];
          assert t[|t| - 1 - k] == s[|s| - 1 - k];
        } else {
          assert Rev(s)[k] == s[0];
          assert s[|s| - 1 - k] == s[0];
        }
      }
    }
  }

  lemma RevSorted(S: seq<int>)
    requires NonIncreasing(S)
    ensures NonDecreasing(Rev(S))
  {
    RevProps(S);
    forall a, b | 0 <= a < b < |Rev(S)| ensures Rev(S)[a] <= Rev(S)[b] {
      assert Rev(S)[a] == S[|S| - 1 - a];
      assert Rev(S)[b] == S[|S| - 1 - b];
      assert S[|S| - 1 - b] >= S[|S| - 1 - a];
    }
  }

  // Suffix (xs[i+1..j] + [xs[i]] + xs[j+1..]) is non-increasing under the pivot hypotheses.
  lemma SuffixNonInc(xs: seq<int>, i: int, j: int)
    requires 0 <= i < j < |xs|
    requires xs[i] < xs[j]
    requires forall a, b :: i < a < b < |xs| ==> xs[a] >= xs[b]
    requires forall a :: j < a < |xs| ==> xs[a] <= xs[i]
    ensures NonIncreasing(xs[i+1..j] + [xs[i]] + xs[j+1..])
  {
    var B := xs[i+1..j];
    var C := xs[j+1..];
    var S := B + [xs[i]] + C;
    var L1 := |B|;
    assert L1 == j - i - 1;
    assert |S| == L1 + 1 + |C|;
    assert forall a :: 0 <= a < L1 ==> S[a] == xs[i + 1 + a];
    assert S[L1] == xs[i];
    assert forall a :: L1 < a < |S| ==> S[a] == xs[a + i + 1];
    forall a, b | 0 <= a < b < |S| ensures S[a] >= S[b] {
      if b < L1 {
        assert S[a] == xs[i + 1 + a];
        assert S[b] == xs[i + 1 + b];
      } else if b == L1 {
        // here a < L1
        assert S[a] == xs[i + 1 + a];
        assert xs[i + 1 + a] >= xs[j];
        assert S[b] == xs[i];
      } else {
        // b > L1: index b + i + 1 is beyond j, so its value is <= xs[i]
        assert S[b] == xs[b + i + 1];
        assert xs[b + i + 1] <= xs[i];
        if a < L1 {
          assert S[a] == xs[i + 1 + a];
          assert xs[i + 1 + a] >= xs[j];
        } else if a == L1 {
          assert S[a] == xs[i];
        } else {
          assert S[a] == xs[a + i + 1];
          assert xs[a + i + 1] >= xs[b + i + 1];
        }
      }
    }
  }

  // If a and b agree up to k and a[k] < b[k], then a < b lexicographically.
  lemma LexPrefix(a: seq<int>, b: seq<int>, k: nat)
    requires k < |a| && k < |b|
    requires forall m :: 0 <= m < k ==> a[m] == b[m]
    requires a[k] < b[k]
    ensures LexLt(a, b)
    decreases k
  {
    if k > 0 {
      LexPrefix(a[1..], b[1..], k - 1);
    }
  }

  // Asymmetry of the lexicographic order.
  lemma Asym(a: seq<int>, b: seq<int>)
    ensures !(LexLt(a, b) && LexLt(b, a))
    decreases |a|
  {
    if |a| > 0 && |b| > 0 && a[0] == b[0] {
      Asym(a[1..], b[1..]);
    }
  }

  // Common prefixes can be cancelled.
  lemma PrefixCancel(a: seq<int>, b: seq<int>, c: seq<int>)
    ensures LexLt(a + b, a + c) == LexLt(b, c)
    decreases |a|
  {
    if |a| > 0 {
      assert (a + b)[0] == a[0];
      assert (a + c)[0] == a[0];
      assert (a + b)[1..] == a[1..] + b;
      assert (a + c)[1..] == a[1..] + c;
      PrefixCancel(a[1..], b, c);
    } else {
      assert a + b == b;
      assert a + c == c;
    }
  }

  // Cancellation for multisets.
  lemma MSCancel(a: multiset<int>, b: multiset<int>, c: multiset<int>)
    requires a + b == a + c
    ensures b == c
  {
    forall x ensures b[x] == c[x] {
      assert (a + b)[x] == (a + c)[x];
    }
  }

  // Lexicographic less-than yields a first point of difference.
  lemma FirstDiff(a: seq<int>, b: seq<int>) returns (k: nat)
    requires |a| == |b|
    requires LexLt(a, b)
    ensures k < |a|
    ensures forall m :: 0 <= m < k ==> a[m] == b[m]
    ensures a[k] < b[k]
    decreases |a|
  {
    assert |a| > 0;
    if a[0] < b[0] {
      k := 0;
    } else {
      assert a[0] == b[0];
      assert LexLt(a[1..], b[1..]);
      var k2 := FirstDiff(a[1..], b[1..]);
      k := k2 + 1;
    }
  }

  // A permutation agreeing with xs on a prefix of length k has the same suffix multiset.
  lemma SliceMS(xs: seq<int>, p: seq<int>, k: nat)
    requires IsPerm(p, xs)
    requires k <= |xs|
    requires forall m :: 0 <= m < k ==> p[m] == xs[m]
    ensures multiset(p[k..]) == multiset(xs[k..])
  {
    assert p[..k] == xs[..k];
    assert p == p[..k] + p[k..];
    assert xs == xs[..k] + xs[k..];
    assert multiset(p) == multiset(p[..k]) + multiset(p[k..]);
    assert multiset(xs) == multiset(xs[..k]) + multiset(xs[k..]);
    assert multiset(p[..k]) == multiset(xs[..k]);
    assert multiset(p[..k]) + multiset(p[k..]) == multiset(p[..k]) + multiset(xs[k..]);
    MSCancel(multiset(p[..k]), multiset(p[k..]), multiset(xs[k..]));
  }

  // If p agrees with xs on [0,k) and the suffix of xs from k is non-increasing,
  // then p[k] <= xs[k] (no permutation can raise the element at k).
  lemma SuffixNoRaise(xs: seq<int>, p: seq<int>, k: nat)
    requires IsPerm(p, xs)
    requires k < |xs|
    requires forall m :: 0 <= m < k ==> p[m] == xs[m]
    requires forall a, b :: k <= a < b < |xs| ==> xs[a] >= xs[b]
    ensures p[k] <= xs[k]
  {
    SliceMS(xs, p, k);
    assert p[k..][0] == p[k];
    assert p[k] in p[k..];
    InMS(p[k..], p[k]);
    assert p[k] in multiset(xs[k..]);
    InMS(xs[k..], p[k]);
    assert p[k] in xs[k..];
    var idx :| 0 <= idx < |xs[k..]| && xs[k..][idx] == p[k];
    assert xs[k + idx] == p[k];
    if idx > 0 {
      assert xs[k] >= xs[k + idx];
    }
  }

  // Sorted (non-decreasing) sequences are lexicographically minimal among their permutations.
  lemma SortedMin(s: seq<int>, t: seq<int>)
    requires NonDecreasing(s)
    requires |t| == |s|
    requires multiset(t) == multiset(s)
    ensures !LexLt(t, s)
    decreases |s|
  {
    if |s| > 0 {
      assert t == [t[0]] + t[1..];
      assert s == [s[0]] + s[1..];
      assert t[0] in multiset(t);
      assert t[0] in multiset(s);
      InMS(s, t[0]);
      assert t[0] in s;
      var idx :| 0 <= idx < |s| && s[idx] == t[0];
      if idx > 0 {
        assert s[0] <= s[idx];
      }
      assert s[0] <= t[0];
      if s[0] < t[0] {
        // LexLt(t, s) is false: first elements, t[0] > s[0]
      } else {
        assert s[0] == t[0];
        assert multiset{t[0]} + multiset(t[1..]) == multiset{s[0]} + multiset(s[1..]);
        MSCancel(multiset{t[0]}, multiset(t[1..]), multiset(s[1..]));
        assert multiset(t[1..]) == multiset(s[1..]);
        assert NonDecreasing(s[1..]);
        SortedMin(s[1..], t[1..]);
      }
    }
  }

  // No permutation of a non-increasing sequence is lexicographically greater.
  lemma NoGreater(xs: seq<int>, p: seq<int>)
    requires IsPerm(p, xs)
    requires NonIncreasing(xs)
    ensures !LexLt(xs, p)
  {
    if LexLt(xs, p) {
      var k := FirstDiff(xs, p);
      assert forall m :: 0 <= m < k ==> p[m] == xs[m];
      SuffixNoRaise(xs, p, k);
      assert false;
    }
  }

  lemma NoGreaterAll(xs: seq<int>)
    requires NonIncreasing(xs)
    ensures forall p :: IsPerm(p, xs) ==> !LexLt(xs, p)
  {
    forall p | IsPerm(p, xs) ensures !LexLt(xs, p) {
      NoGreater(xs, p);
    }
  }

  lemma ExistsGreater(xs: seq<int>, q: seq<int>)
    requires IsPerm(q, xs) && LexLt(xs, q)
    ensures exists p :: IsPerm(p, xs) && LexLt(xs, p)
  {
  }

  // Multiset decomposition of xs around the pivot positions i and j.
  lemma MSDecomp(xs: seq<int>, i: int, j: int)
    requires 0 <= i < j < |xs|
    ensures multiset(xs) == multiset(xs[..i]) + multiset{xs[i]} + multiset(xs[i+1..j]) + multiset{xs[j]} + multiset(xs[j+1..])
  {
    assert xs == xs[..i] + xs[i..];
    assert xs[i..] == [xs[i]] + xs[i+1..];
    assert xs[i+1..] == xs[i+1..j] + xs[j..];
    assert xs[j..] == [xs[j]] + xs[j+1..];
    assert multiset(xs) == multiset(xs[..i]) + multiset(xs[i..]);
    assert multiset(xs[i..]) == multiset{xs[i]} + multiset(xs[i+1..]);
    assert multiset(xs[i+1..]) == multiset(xs[i+1..j]) + multiset(xs[j..]);
    assert multiset(xs[j..]) == multiset{xs[j]} + multiset(xs[j+1..]);
  }

  // The constructed successor is a rearrangement of xs.
  lemma BuildPerm(xs: seq<int>, i: int, j: int)
    requires 0 <= i < j < |xs|
    ensures IsPerm(Build(xs, i, j), xs)
  {
    var S := xs[i+1..j] + [xs[i]] + xs[j+1..];
    RevProps(S);
    MSDecomp(xs, i, j);
    assert |S| == |xs| - i - 1;
    assert Build(xs, i, j) == xs[..i] + [xs[j]] + Rev(S);
  }

  // The constructed successor is strictly greater than xs.
  lemma BuildGreater(xs: seq<int>, i: int, j: int)
    requires 0 <= i < j < |xs|
    requires xs[i] < xs[j]
    ensures LexLt(xs, Build(xs, i, j))
  {
    var r := Build(xs, i, j);
    assert forall m :: 0 <= m < i ==> r[m] == xs[m];
    assert r[i] == xs[j];
    LexPrefix(xs, r, i);
  }

  // Main correctness of the constructed successor (pivot case).
  lemma Minimal(xs: seq<int>, i: int, j: int)
    requires 0 <= i < j < |xs|
    requires xs[i] < xs[j]
    requires forall a, b :: i < a < b < |xs| ==> xs[a] >= xs[b]
    requires forall a :: j < a < |xs| ==> xs[a] <= xs[i]
    ensures IsPerm(Build(xs, i, j), xs)
    ensures LexLt(xs, Build(xs, i, j))
    ensures forall p :: IsPerm(p, xs) && LexLt(xs, p) ==> !LexLt(p, Build(xs, i, j))
  {
    BuildPerm(xs, i, j);
    BuildGreater(xs, i, j);
    forall p | IsPerm(p, xs) && LexLt(xs, p)
      ensures !LexLt(p, Build(xs, i, j))
    {
      MinCase(xs, i, j, p);
    }
  }

  // Case analysis for one permutation p > xs against the constructed successor.
  lemma MinCase(xs: seq<int>, i: int, j: int, p: seq<int>)
    requires 0 <= i < j < |xs|
    requires xs[i] < xs[j]
    requires forall a, b :: i < a < b < |xs| ==> xs[a] >= xs[b]
    requires forall a :: j < a < |xs| ==> xs[a] <= xs[i]
    requires IsPerm(p, xs) && LexLt(xs, p)
    ensures !LexLt(p, Build(xs, i, j))
  {
    var n := |xs|;
    var A := xs[..i];
    var B := xs[i+1..j];
    var C := xs[j+1..];
    var S := B + [xs[i]] + C;
    var r := Build(xs, i, j);
    assert r == A + [xs[j]] + Rev(S);
    RevProps(S);
    SuffixNonInc(xs, i, j);
    RevSorted(S);
    assert |S| == n - i - 1;
    MSDecomp(xs, i, j);
    assert multiset(S) == multiset(B) + multiset{xs[i]} + multiset(C);
    assert multiset(xs) == multiset(A) + multiset{xs[i]} + multiset(B) + multiset{xs[j]} + multiset(C);
    assert forall m :: 0 <= m < i ==> r[m] == xs[m];
    assert r[i] == xs[j];
    var k := FirstDiff(xs, p);
      if k > i {
        // p agrees with xs before k and p[k] > xs[k], but suffix after i is non-increasing
        SuffixNoRaise(xs, p, k);
        assert false;
      } else if k < i {
        assert r[k] == xs[k];
        assert forall m :: 0 <= m < k ==> r[m] == p[m];
        LexPrefix(r, p, k);
        Asym(r, p);
      } else {
        // k == i : p agrees with xs on [0,i) and xs[i] < p[i]
        assert forall m :: 0 <= m < i ==> p[m] == xs[m];
        assert xs[i] < p[i];
        SliceMS(xs, p, i);
        assert p[i..][0] == p[i];
        assert p[i] in p[i..];
        InMS(p[i..], p[i]);
        assert p[i] in multiset(xs[i..]);
        InMS(xs[i..], p[i]);
        assert p[i] in xs[i..];
        var idx :| 0 <= idx < |xs[i..]| && xs[i..][idx] == p[i];
        var m := i + idx;
        assert xs[m] == p[i];
        if m < j {
          if m == i {
            assert false;
          }
          assert xs[m] >= xs[j];
        } else if m > j {
          assert xs[m] <= xs[i];
          assert false;
        }
        assert p[i] >= xs[j];

        if p[i] > xs[j] {
          assert forall q :: 0 <= q < i ==> r[q] == p[q];
          assert r[i] == xs[j];
          LexPrefix(r, p, i);
          Asym(r, p);
        } else {
          // p[i] == xs[j]: compare the tails, which are permutations of each other
          assert p[i] == xs[j];
          assert p[..i] == A;
          assert p[..i + 1] == A + [xs[j]];
          assert p == p[..i] + [p[i]] + p[i+1..];
          assert multiset(p) == multiset(A) + multiset{xs[j]} + multiset(p[i+1..]);
          assert multiset(S) == multiset(B) + multiset{xs[i]} + multiset(C);
          assert multiset(xs) == multiset(A) + multiset{xs[i]} + multiset(B) + multiset{xs[j]} + multiset(C);
          assert multiset(A) + (multiset{xs[j]} + multiset(p[i+1..])) == multiset(p);
          assert multiset(p) == multiset(xs);
          assert multiset(xs) == multiset(A) + (multiset{xs[i]} + multiset(B) + multiset{xs[j]} + multiset(C));
          assert multiset(A) + (multiset{xs[j]} + multiset(p[i+1..])) == multiset(A) + (multiset{xs[i]} + multiset(B) + multiset{xs[j]} + multiset(C));
          MSCancel(multiset(A), multiset{xs[j]} + multiset(p[i+1..]), multiset{xs[i]} + multiset(B) + multiset{xs[j]} + multiset(C));
          assert multiset{xs[j]} + multiset(p[i+1..]) == multiset{xs[j]} + multiset(S);
          MSCancel(multiset{xs[j]}, multiset(p[i+1..]), multiset(S));
          assert multiset(p[i+1..]) == multiset(Rev(S));
          SortedMin(Rev(S), p[i+1..]);
          assert p == p[..i + 1] + p[i+1..];
          assert r == p[..i + 1] + Rev(S);
          PrefixCancel(p[..i + 1], p[i+1..], Rev(S));
        }
      }
  }

  method next_permutation(xs: seq<int>) returns (r: seq<int>)
    ensures IsPerm(r, xs)
    ensures (exists p :: IsPerm(p, xs) && LexLt(xs, p)) ==>
              (LexLt(xs, r) && forall p :: IsPerm(p, xs) && LexLt(xs, p) ==> !LexLt(p, r))
    ensures !(exists p :: IsPerm(p, xs) && LexLt(xs, p)) ==> NonDecreasing(r)
  {
    var n := |xs|;
    if n == 0 {
      NoGreaterAll(xs);
      return xs;
    }

    // Find the pivot: largest i with xs[i] < xs[i+1]
    var i := n - 2;
    while i >= 0 && xs[i] >= xs[i + 1]
      invariant -1 <= i <= n - 2
      invariant forall a, b :: i < a < b < n ==> xs[a] >= xs[b]
      decreases i + 1
    {
      assert forall b :: i + 1 < b < n ==> xs[i + 1] >= xs[b];
      i := i - 1;
    }

    if i < 0 {
      // xs is non-increasing: it is its own greatest arrangement
      assert NonIncreasing(xs);
      NoGreaterAll(xs);
      RevSorted(xs);
      RevProps(xs);
      r := Rev(xs);
      return;
    }

    assert xs[i] < xs[i + 1];

    // Find the rightmost j > i with xs[j] > xs[i]
    var j := n - 1;
    while xs[j] <= xs[i]
      invariant 0 <= i < j <= n - 1
      invariant forall a :: j < a < n ==> xs[a] <= xs[i]
      decreases j - i
    {
      assert j != i + 1;
      j := j - 1;
    }

    r := Build(xs, i, j);
    Minimal(xs, i, j);
    ExistsGreater(xs, r);
  }
}
