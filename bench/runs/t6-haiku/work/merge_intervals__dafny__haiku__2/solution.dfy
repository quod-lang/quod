module Solution {

  // x lies in some closed interval of s. Real-valued so that integer intervals
  // which merely touch in a gap (e.g. [1,2] and [3,4]) are not identified.
  predicate covers(s: seq<(int, int)>, x: real)
  {
    exists j :: 0 <= j < |s| && (s[j].0 as real) <= x <= (s[j].1 as real)
  }

  predicate sortedByStart(s: seq<(int, int)>)
  {
    forall i, j :: 0 <= i < j < |s| ==> s[i].0 <= s[j].0
  }

  // Every interval is valid, and consecutive intervals are strictly separated
  // (r[k].1 < r[k+1].0): they neither overlap nor share an endpoint.
  predicate normalized(r: seq<(int, int)>)
  {
    (forall k :: 0 <= k < |r| ==> r[k].0 <= r[k].1) &&
    (forall k :: 0 <= k < |r| - 1 ==> r[k].1 < r[k + 1].0)
  }

  lemma CoversConcat(a: seq<(int, int)>, b: seq<(int, int)>, x: real)
    ensures covers(a + b, x) <==> covers(a, x) || covers(b, x)
  {
    if covers(a + b, x) {
      var j :| 0 <= j < |a + b| && ((a + b)[j].0 as real) <= x <= ((a + b)[j].1 as real);
      if j < |a| {
        assert (a + b)[j] == a[j];
        assert covers(a, x);
      } else {
        assert (a + b)[j] == b[j - |a|];
        assert covers(b, x);
      }
    }
    if covers(a, x) {
      var j :| 0 <= j < |a| && (a[j].0 as real) <= x <= (a[j].1 as real);
      assert (a + b)[j] == a[j];
      assert covers(a + b, x);
    }
    if covers(b, x) {
      var j :| 0 <= j < |b| && (b[j].0 as real) <= x <= (b[j].1 as real);
      assert (a + b)[|a| + j] == b[j];
      assert covers(a + b, x);
    }
  }

  lemma CoversSingleton(p: (int, int), x: real)
    ensures covers([p], x) <==> (p.0 as real) <= x <= (p.1 as real)
  {
    if covers([p], x) {
      var j :| 0 <= j < 1 && ((p.0 as real) <= x <= (p.1 as real));
    }
    if (p.0 as real) <= x <= (p.1 as real) {
      assert [p][0] == p;
      assert 0 <= 0 < |[p]| && (([p][0].0 as real) <= x <= ([p][0].1 as real));
    }
  }

  lemma CoversPerm(s: seq<(int, int)>, t: seq<(int, int)>, x: real)
    requires multiset(s) == multiset(t)
    ensures covers(s, x) <==> covers(t, x)
  {
    if covers(s, x) {
      var j :| 0 <= j < |s| && (s[j].0 as real) <= x <= (s[j].1 as real);
      assert s[j] in multiset(t);
      assert s[j] in t;
      var k :| 0 <= k < |t| && t[k] == s[j];
      assert covers(t, x);
    }
    if covers(t, x) {
      var j :| 0 <= j < |t| && (t[j].0 as real) <= x <= (t[j].1 as real);
      assert t[j] in multiset(s);
      assert t[j] in s;
      var k :| 0 <= k < |s| && s[k] == t[j];
      assert covers(s, x);
    }
  }

  // Insert x into a sorted sequence, keeping it sorted.
  function insertSorted(x: (int, int), s: seq<(int, int)>): seq<(int, int)>
    requires sortedByStart(s)
    ensures sortedByStart(insertSorted(x, s))
    ensures multiset(insertSorted(x, s)) == multiset(s) + multiset{x}
    decreases |s|
  {
    if |s| == 0 then [x]
    else if x.0 <= s[0].0 then [x] + s
    else
      var rest := insertSorted(x, s[1..]);
      assert s == [s[0]] + s[1..];
      assert multiset(s) == multiset{s[0]} + multiset(s[1..]);
      assert multiset(rest) == multiset(s[1..]) + multiset{x};
      assert forall j :: 0 <= j < |rest| ==> s[0].0 <= rest[j].0 by {
        forall j | 0 <= j < |rest| ensures s[0].0 <= rest[j].0 {
          var e := rest[j];
          assert multiset(rest)[e] > 0;
          if e != x {
            assert multiset(s[1..])[e] > 0;
            var k :| 0 <= k < |s[1..]| && s[1..][k] == e;
            assert s[k + 1] == e;
            assert s[0].0 <= s[k + 1].0;
          }
        }
      }
      [s[0]] + rest
  }

  // Insertion sort by start.
  function sortByStart(s: seq<(int, int)>): seq<(int, int)>
    ensures sortedByStart(sortByStart(s))
    ensures multiset(sortByStart(s)) == multiset(s)
    decreases |s|
  {
    if |s| == 0 then []
    else
      assert s == [s[0]] + s[1..];
      insertSorted(s[0], sortByStart(s[1..]))
  }

  method merge_intervals(iv: seq<(int, int)>) returns (r: seq<(int, int)>)
    requires forall k :: 0 <= k < |iv| ==> iv[k].0 <= iv[k].1
    ensures normalized(r)
    ensures forall x: real :: covers(r, x) <==> covers(iv, x)
  {
    var s := sortByStart(iv);
    forall x: real ensures covers(s, x) <==> covers(iv, x) {
      CoversPerm(iv, s, x);
    }
    forall k | 0 <= k < |s| ensures s[k].0 <= s[k].1 {
      assert s[k] in multiset(iv);
      assert s[k] in iv;
      var m :| 0 <= m < |iv| && iv[m] == s[k];
    }

    r := [];
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant normalized(r)
      invariant forall x: real :: covers(r, x) <==> covers(s[..i], x)
      invariant i < |s| && |r| > 0 ==> r[|r| - 1].0 <= s[i].0
      invariant forall k :: 0 <= k < |s| ==> s[k].0 <= s[k].1
      decreases |s| - i
    {
      var a := s[i].0;
      var b := s[i].1;
      assert s[i] == (a, b);
      assert s[..i + 1] == s[..i] + [s[i]];
      if |r| > 0 && a <= r[|r| - 1].1 {
        // Overlap or shared endpoint: extend the last output interval.
        var n := |r| - 1;
        var L := r[n].0;
        var e0 := r[n].1;
        var e := if b > e0 then b else e0;
        assert L <= a <= e0;
        var prev := r;
        assert prev[n] == (L, e0);
        var prefix := prev[..n];
        assert normalized(prefix + [(L, e)]) by {
          assert forall k :: 0 <= k < |prefix| ==> prefix[k] == prev[k];
          assert forall k :: 0 <= k < |prefix| - 1 ==> prefix[k].1 < prefix[k + 1].0;
          assert |prefix| == n;
          if n > 0 {
            assert prefix[n - 1] == prev[n - 1];
            assert prev[n - 1].1 < prev[n].0;
          }
        }
        assert prev == prefix + [prev[n]];
        r := prefix + [(L, e)];
        forall x: real ensures covers(r, x) <==> covers(s[..i + 1], x) {
          assert covers(prev, x) <==> covers(s[..i], x);
          CoversConcat(prefix, [prev[n]], x);
          CoversConcat(prefix, [(L, e)], x);
          CoversConcat(s[..i], [s[i]], x);
          CoversSingleton(prev[n], x);
          CoversSingleton((L, e), x);
          assert covers([prev[n]], x) <==> (L as real) <= x <= (e0 as real);
          assert covers(prev, x) <==> covers(prefix, x) || ((L as real) <= x <= (e0 as real));
          assert covers(s[..i + 1], x) <==> covers(s[..i], x) || (a as real) <= x <= (b as real);
          CoversConcat(prefix, [prev[n]], x);
          CoversConcat(s[..i], [s[i]], x);
        }
      } else {
        // Disjoint from the last output interval: append.
        var prev := r;
        if |r| > 0 {
          assert r[|r| - 1].1 < a;
        }
        assert normalized(prev + [(a, b)]) by {
          if |prev| > 0 {
            assert (prev + [(a, b)])[|prev|] == (a, b);
            assert prev[|prev| - 1].1 < a;
          }
        }
        r := prev + [(a, b)];
        forall x: real ensures covers(r, x) <==> covers(s[..i + 1], x) {
          CoversConcat(prev, [s[i]], x);
          CoversConcat(s[..i], [s[i]], x);
        }
      }
      i := i + 1;
    }
    assert s[..|s|] == s;
  }
}
