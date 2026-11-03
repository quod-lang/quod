module Solution {

  // The closed interval [c, d] contains the real point x.
  ghost predicate In(c: int, d: int, x: real) {
    c as real <= x <= d as real
  }

  // The real point x lies in the union of the intervals of s.
  ghost predicate Covers(s: seq<(int, int)>, x: real) {
    exists k :: 0 <= k < |s| && In(s[k].0, s[k].1, x)
  }

  ghost predicate SortedByStart(s: seq<(int, int)>) {
    forall p, q :: 0 <= p < q < |s| ==> s[p].0 <= s[q].0
  }

  ghost predicate WellFormed(s: seq<(int, int)>) {
    forall k :: 0 <= k < |s| ==> s[k].0 <= s[k].1
  }

  // Strictly separated: every earlier interval ends before every later one starts
  // (so intervals that merely touch are not allowed).
  ghost predicate Separated(s: seq<(int, int)>) {
    forall p, q :: 0 <= p < q < |s| ==> s[p].1 < s[q].0
  }

  lemma CoversSnoc(t: seq<(int, int)>, e: (int, int), x: real)
    ensures Covers(t + [e], x) <==> Covers(t, x) || In(e.0, e.1, x)
  {
    if Covers(t + [e], x) {
      var k :| 0 <= k < |t + [e]| && In((t + [e])[k].0, (t + [e])[k].1, x);
      if k < |t| {
        assert (t + [e])[k] == t[k];
        assert Covers(t, x);
      } else {
        assert (t + [e])[k] == e;
        assert In(e.0, e.1, x);
      }
    }
    if Covers(t, x) {
      var k :| 0 <= k < |t| && In(t[k].0, t[k].1, x);
      assert (t + [e])[k] == t[k];
      assert Covers(t + [e], x);
    }
    if In(e.0, e.1, x) {
      assert (t + [e])[|t|] == e;
      assert Covers(t + [e], x);
    }
  }

  lemma MergeCover(c: int, d: int, a: int, b: int, x: real)
    requires c <= a <= d
    ensures In(c, d, x) || In(a, b, x) <==> In(c, if b > d then b else d, x)
  {
  }

  lemma CoversPerm(s: seq<(int, int)>, t: seq<(int, int)>, x: real)
    requires multiset(s) == multiset(t)
    ensures Covers(s, x) <==> Covers(t, x)
  {
    if Covers(s, x) {
      var k :| 0 <= k < |s| && In(s[k].0, s[k].1, x);
      assert s[k] in multiset(s);
      assert s[k] in multiset(t);
      assert s[k] in t;
      var j :| 0 <= j < |t| && t[j] == s[k];
      assert In(t[j].0, t[j].1, x);
      assert Covers(t, x);
    }
    if Covers(t, x) {
      var k :| 0 <= k < |t| && In(t[k].0, t[k].1, x);
      assert t[k] in multiset(t);
      assert t[k] in multiset(s);
      assert t[k] in s;
      var j :| 0 <= j < |s| && s[j] == t[k];
      assert In(s[j].0, s[j].1, x);
      assert Covers(s, x);
    }
  }

  lemma WFPerm(s: seq<(int, int)>, t: seq<(int, int)>)
    requires multiset(s) == multiset(t)
    requires WellFormed(s)
    ensures WellFormed(t)
  {
    forall k | 0 <= k < |t| ensures t[k].0 <= t[k].1 {
      assert t[k] in multiset(t);
      assert t[k] in multiset(s);
      assert t[k] in s;
      var j :| 0 <= j < |s| && s[j] == t[k];
    }
  }

  // Sorts the intervals by start (insertion sort), preserving the multiset.
  method SortByStart(s: seq<(int, int)>) returns (r: seq<(int, int)>)
    requires WellFormed(s)
    ensures multiset(r) == multiset(s)
    ensures SortedByStart(r)
    ensures WellFormed(r)
  {
    var a := new (int, int)[|s|];
    var m := 0;
    while m < a.Length
      invariant 0 <= m <= a.Length
      invariant forall k :: 0 <= k < m ==> a[k] == s[k]
      decreases a.Length - m
    {
      a[m] := s[m];
      m := m + 1;
    }
    assert a[..] == s;

    var i := 0;
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant multiset(a[..]) == multiset(s)
      invariant forall p, q :: 0 <= p < q < i ==> a[p].0 <= a[q].0
      decreases a.Length - i
    {
      var j := i;
      while j > 0 && a[j - 1].0 > a[j].0
        invariant 0 <= j <= i < a.Length
        invariant multiset(a[..]) == multiset(s)
        invariant forall p, q :: 0 <= p < q <= i && q != j ==> a[p].0 <= a[q].0
        decreases j
      {
        a[j - 1], a[j] := a[j], a[j - 1];
        j := j - 1;
      }
      i := i + 1;
    }
    r := a[..];
    assert multiset(r) == multiset(s);
    assert SortedByStart(r);
    WFPerm(s, r);
  }

  method merge_intervals(iv: seq<(int, int)>) returns (r: seq<(int, int)>)
    requires forall k :: 0 <= k < |iv| ==> iv[k].0 <= iv[k].1
    ensures WellFormed(r)
    ensures Separated(r)
    ensures forall x: real {:trigger Covers(r, x)} :: Covers(r, x) <==> Covers(iv, x)
  {
    var s := SortByStart(iv);
    assert multiset(s) == multiset(iv);
    r := [];
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant WellFormed(r)
      invariant Separated(r)
      invariant SortedByStart(s)
      invariant WellFormed(s)
      invariant forall k :: 0 <= k < |r| ==> 0 < i && r[k].0 <= s[i - 1].0
      invariant forall x: real {:trigger Covers(r, x)} :: Covers(r, x) <==> Covers(s[..i], x)
      decreases |s| - i
    {
      var a := s[i].0;
      var b := s[i].1;
      assert s[..i + 1] == s[..i] + [s[i]];
      forall x: real ensures Covers(s[..i + 1], x) <==> Covers(s[..i], x) || In(a, b, x) {
        CoversSnoc(s[..i], s[i], x);
      }

      if |r| > 0 && a <= r[|r| - 1].1 {
        var last := r[|r| - 1];
        var t := r[..|r| - 1];
        assert r == t + [last];
        var nb := if b > last.1 then b else last.1;
        assert last.0 <= a;
        r := t + [(last.0, nb)];
        forall x: real ensures Covers(r, x) <==> Covers(s[..i + 1], x) {
          CoversSnoc(t, last, x);
          CoversSnoc(t, (last.0, nb), x);
          MergeCover(last.0, last.1, a, b, x);
        }
      } else {
        var prev := r;
        r := r + [(a, b)];
        forall x: real ensures Covers(r, x) <==> Covers(s[..i + 1], x) {
          CoversSnoc(prev, (a, b), x);
        }
      }
      i := i + 1;
    }
    assert s[..|s|] == s;
    forall x: real ensures Covers(r, x) <==> Covers(iv, x) {
      CoversPerm(s, iv, x);
    }
  }
}
