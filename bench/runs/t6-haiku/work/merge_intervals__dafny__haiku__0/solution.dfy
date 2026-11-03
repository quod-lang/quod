module Solution {

  // All intervals are well-formed.
  predicate ValidIv(s: seq<(int, int)>) {
    forall k :: 0 <= k < |s| ==> s[k].0 <= s[k].1
  }

  // Intervals are ordered by start.
  predicate SortedByStart(s: seq<(int, int)>) {
    forall k :: 0 <= k < |s| - 1 ==> s[k].0 <= s[k + 1].0
  }

  // Consecutive intervals are strictly separated (no overlap, no touching).
  predicate Disjoint(r: seq<(int, int)>) {
    forall k :: 0 <= k < |r| - 1 ==> r[k].1 < r[k + 1].0
  }

  // Point x lies in some interval of s (index-based).
  predicate Cov(s: seq<(int, int)>, x: int) {
    exists k :: 0 <= k < |s| && s[k].0 <= x <= s[k].1
  }

  lemma CovSnoc(s: seq<(int, int)>, p: (int, int), x: int)
    ensures Cov(s + [p], x) <==> Cov(s, x) || (p.0 <= x <= p.1)
  {
    if Cov(s + [p], x) {
      var k :| 0 <= k < |s + [p]| && (s + [p])[k].0 <= x <= (s + [p])[k].1;
      if k < |s| {
        assert (s + [p])[k] == s[k];
      } else {
        assert (s + [p])[k] == p;
      }
    }
    if Cov(s, x) {
      var k :| 0 <= k < |s| && s[k].0 <= x <= s[k].1;
      assert (s + [p])[k] == s[k];
    }
    if p.0 <= x <= p.1 {
      assert (s + [p])[|s|] == p;
    }
  }

  // Merging the last interval [L0,L1] with [a,b], given L0 <= a <= L1.
  lemma MergeRange(L0: int, L1: int, a: int, b: int, x: int)
    requires L0 <= a <= L1
    requires a <= b
    ensures (L0 <= x <= L1 || a <= x <= b) <==> (L0 <= x <= (if L1 > b then L1 else b))
  {
  }

  lemma CovPrefix(s: seq<(int, int)>, i: int, x: int)
    requires 0 <= i < |s|
    ensures (exists k :: 0 <= k < i + 1 && s[k].0 <= x <= s[k].1)
            <==> ((exists k :: 0 <= k < i && s[k].0 <= x <= s[k].1) || (s[i].0 <= x <= s[i].1))
  {
    if exists k :: 0 <= k < i + 1 && s[k].0 <= x <= s[k].1 {
      var k :| 0 <= k < i + 1 && s[k].0 <= x <= s[k].1;
      if k == i {
        assert s[i].0 <= x <= s[i].1;
      } else {
        assert 0 <= k < i;
      }
    }
  }

  // Sweep over a start-sorted, valid interval list, merging touching/overlapping ones.
  method Sweep(s: seq<(int, int)>) returns (r: seq<(int, int)>)
    requires ValidIv(s)
    requires SortedByStart(s)
    ensures ValidIv(r)
    ensures Disjoint(r)
    ensures forall x :: Cov(r, x) <==> Cov(s, x)
  {
    r := [];
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant ValidIv(r)
      invariant Disjoint(r)
      invariant |r| > 0 ==> i > 0 && r[|r| - 1].0 <= s[i - 1].0
      invariant forall x :: Cov(r, x) <==> (exists k :: 0 <= k < i && s[k].0 <= x <= s[k].1)
      decreases |s| - i
    {
      var a := s[i].0;
      var b := s[i].1;
      if |r| > 0 && r[|r| - 1].1 >= a {
        var n := |r|;
        var L := r[n - 1];
        var M := (L.0, if L.1 > b then L.1 else b);
        var r0 := r[..n - 1];
        assert r == r0 + [L];
        assert r0 + [M] == r[..n - 1] + [M];
        r := r0 + [M];
        assert ValidIv(r);
        assert Disjoint(r);
        forall x : int
          ensures Cov(r, x) <==> (exists k :: 0 <= k < i + 1 && s[k].0 <= x <= s[k].1)
        {
          CovSnoc(r0, M, x);
          CovSnoc(r0, L, x);
          MergeRange(L.0, L.1, a, b, x);
          CovPrefix(s, i, x);
        }
      } else {
        var prev := r;
        r := r + [(a, b)];
        assert ValidIv(r);
        assert Disjoint(r);
        forall x : int
          ensures Cov(r, x) <==> (exists k :: 0 <= k < i + 1 && s[k].0 <= x <= s[k].1)
        {
          CovSnoc(prev, (a, b), x);
          CovPrefix(s, i, x);
        }
      }
      i := i + 1;
    }
    assert forall x :: Cov(r, x) <==> Cov(s, x);
  }

  // Insert p into a start-sorted sequence, keeping it sorted.
  method InsertSorted(s: seq<(int, int)>, p: (int, int)) returns (t: seq<(int, int)>)
    requires SortedByStart(s)
    requires ValidIv(s)
    requires p.0 <= p.1
    ensures SortedByStart(t)
    ensures ValidIv(t)
    ensures multiset(t) == multiset(s) + multiset{p}
  {
    var i := 0;
    while i < |s| && s[i].0 <= p.0
      invariant 0 <= i <= |s|
      invariant forall k :: 0 <= k < i ==> s[k].0 <= p.0
      decreases |s| - i
    {
      i := i + 1;
    }
    t := s[..i] + [p] + s[i..];
    assert s == s[..i] + s[i..];
    assert multiset(t) == multiset(s) + multiset{p};
    forall k | 0 <= k < |t| - 1
      ensures t[k].0 <= t[k + 1].0
    {
      if k + 1 < i {
        assert t[k] == s[k] && t[k + 1] == s[k + 1];
      } else if k + 1 == i {
        assert t[k] == s[k] && t[k + 1] == p;
      } else if k == i {
        assert t[k] == p;
        assert t[k + 1] == s[i];
      } else {
        assert t[k] == s[k - 1] && t[k + 1] == s[k];
      }
    }
    forall k | 0 <= k < |t|
      ensures t[k].0 <= t[k].1
    {
      if k < i {
        assert t[k] == s[k];
      } else if k == i {
        assert t[k] == p;
      } else {
        assert t[k] == s[k - 1];
      }
    }
  }

  // Membership-based coverage, used in the top-level contract.
  predicate Covers(s: seq<(int, int)>, x: int) {
    exists p :: p in s && p.0 <= x <= p.1
  }

  lemma CovEq(s: seq<(int, int)>, x: int)
    ensures Cov(s, x) <==> Covers(s, x)
  {
    if Cov(s, x) {
      var k :| 0 <= k < |s| && s[k].0 <= x <= s[k].1;
      assert s[k] in s;
    }
    if Covers(s, x) {
      var p :| p in s && p.0 <= x <= p.1;
      var k :| 0 <= k < |s| && s[k] == p;
      assert s[k].0 <= x <= s[k].1;
    }
  }

  // Sort intervals by start (insertion sort), preserving the multiset.
  method SortIv(iv: seq<(int, int)>) returns (s: seq<(int, int)>)
    requires ValidIv(iv)
    ensures SortedByStart(s)
    ensures ValidIv(s)
    ensures multiset(s) == multiset(iv)
  {
    s := [];
    var i := 0;
    while i < |iv|
      invariant 0 <= i <= |iv|
      invariant SortedByStart(s)
      invariant ValidIv(s)
      invariant multiset(s) == multiset(iv[..i])
      decreases |iv| - i
    {
      assert iv[i] in iv;
      s := InsertSorted(s, iv[i]);
      assert iv[..i + 1] == iv[..i] + [iv[i]];
      i := i + 1;
    }
    assert iv[..i] == iv;
  }

  method merge_intervals(iv: seq<(int, int)>) returns (r: seq<(int, int)>)
    requires ValidIv(iv)
    ensures SortedByStart(r)
    ensures Disjoint(r)
    ensures ValidIv(r)
    ensures forall x {:trigger Covers(r, x)} :: Covers(iv, x) <==> Covers(r, x)
  {
    var s := SortIv(iv);
    r := Sweep(s);
    assert multiset(s) == multiset(iv);
    forall p | p in s ensures p in iv {
      assert multiset(s)[p] > 0;
      assert multiset(iv)[p] > 0;
    }
    forall p | p in iv ensures p in s {
      assert multiset(iv)[p] > 0;
      assert multiset(s)[p] > 0;
    }
    forall x : int ensures Covers(iv, x) <==> Covers(r, x)
    {
      CovEq(s, x);
      CovEq(r, x);
    }
  }
}
