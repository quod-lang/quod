module Solution {

  predicate Valid(s: seq<(int, int)>)
  {
    forall i :: 0 <= i < |s| ==> s[i].0 <= s[i].1
  }

  // Sorted by start, pairwise disjoint and non-touching (a gap between consecutive intervals).
  predicate Canonical(s: seq<(int, int)>)
  {
    Valid(s) && forall i, j :: 0 <= i < j < |s| ==> s[i].1 < s[j].0
  }

  // Point p (in doubled coordinates, so half-integers are represented) lies in interval x.
  // Using doubled coordinates makes (1,2),(3,4) distinct from (1,4) (the point 2.5 is uncovered).
  predicate In(x: (int, int), p: int)
  {
    2 * x.0 <= p <= 2 * x.1
  }

  predicate Covered(s: seq<(int, int)>, p: int)
  {
    exists i :: 0 <= i < |s| && In(s[i], p)
  }

  function Insert(r: seq<(int, int)>, x: (int, int)): seq<(int, int)>
    decreases |r|
  {
    if |r| == 0 then [x]
    else if r[0].1 < x.0 then [r[0]] + Insert(r[1..], x)
    else if x.1 < r[0].0 then [x] + r
    else Insert(r[1..], (if x.0 < r[0].0 then x.0 else r[0].0, if x.1 > r[0].1 then x.1 else r[0].1))
  } by method {
    var pre: seq<(int, int)> := [];
    var j := 0;
    var y := x;
    while j < |r|
      invariant 0 <= j <= |r|
      invariant pre + Insert(r[j..], y) == Insert(r, x)
      decreases |r| - j
    {
      assert r[j..][0] == r[j];
      assert r[j..][1..] == r[j + 1..];
      if r[j].1 < y.0 {
        assert Insert(r[j..], y) == [r[j]] + Insert(r[j + 1..], y);
        pre := pre + [r[j]];
        j := j + 1;
      } else if y.1 < r[j].0 {
        assert Insert(r[j..], y) == [y] + r[j..];
        return pre + [y] + r[j..];
      } else {
        y := (if y.0 < r[j].0 then y.0 else r[j].0, if y.1 > r[j].1 then y.1 else r[j].1);
        j := j + 1;
      }
    }
    assert r[j..] == [];
    return pre + [y];
  }

  lemma InsertProps(r: seq<(int, int)>, x: (int, int))
    requires Canonical(r) && x.0 <= x.1
    ensures Canonical(Insert(r, x))
    ensures forall p :: Covered(Insert(r, x), p) <==> (Covered(r, p) || In(x, p))
    ensures forall k :: 0 <= k < |Insert(r, x)| ==>
              Insert(r, x)[k].0 == x.0 || (exists i :: 0 <= i < |r| && Insert(r, x)[k].0 == r[i].0)
    decreases |r|
  {
    var res := Insert(r, x);
    if |r| == 0 {
      assert res == [x];
      forall p ensures Covered(res, p) <==> (Covered(r, p) || In(x, p)) {
        if In(x, p) { assert In(res[0], p); }
      }
    } else if r[0].1 < x.0 {
      var rest := Insert(r[1..], x);
      InsertProps(r[1..], x);
      assert res == [r[0]] + rest;
      forall k | 0 <= k < |rest| ensures r[0].1 < rest[k].0 {
        if rest[k].0 == x.0 {
        } else {
          var i :| 0 <= i < |r[1..]| && rest[k].0 == r[1..][i].0;
          assert r[1..][i] == r[i + 1];
        }
      }
      forall p ensures Covered(res, p) <==> (Covered(r, p) || In(x, p)) {
        if Covered(res, p) {
          var i :| 0 <= i < |res| && In(res[i], p);
          if i == 0 { assert In(r[0], p); }
          else {
            assert In(rest[i - 1], p);
            assert Covered(rest, p);
            if Covered(r[1..], p) {
              var j :| 0 <= j < |r[1..]| && In(r[1..][j], p);
              assert In(r[j + 1], p);
            }
          }
        }
        if Covered(r, p) {
          var i :| 0 <= i < |r| && In(r[i], p);
          if i == 0 { assert In(res[0], p); }
          else {
            assert In(r[1..][i - 1], p);
            assert Covered(r[1..], p);
            var j :| 0 <= j < |rest| && In(rest[j], p);
            assert In(res[j + 1], p);
          }
        }
        if In(x, p) {
          assert Covered(rest, p);
          var j :| 0 <= j < |rest| && In(rest[j], p);
          assert In(res[j + 1], p);
        }
      }
      forall k | 0 <= k < |res|
        ensures res[k].0 == x.0 || (exists i :: 0 <= i < |r| && res[k].0 == r[i].0)
      {
        if k == 0 { assert res[k].0 == r[0].0; }
        else {
          assert res[k] == rest[k - 1];
          if rest[k - 1].0 != x.0 {
            var i :| 0 <= i < |r[1..]| && rest[k - 1].0 == r[1..][i].0;
            assert r[1..][i] == r[i + 1];
          }
        }
      }
    } else if x.1 < r[0].0 {
      assert res == [x] + r;
      forall p ensures Covered(res, p) <==> (Covered(r, p) || In(x, p)) {
        if Covered(res, p) {
          var i :| 0 <= i < |res| && In(res[i], p);
          if i > 0 { assert In(r[i - 1], p); }
        }
        if Covered(r, p) {
          var i :| 0 <= i < |r| && In(r[i], p);
          assert In(res[i + 1], p);
        }
        if In(x, p) { assert In(res[0], p); }
      }
      forall k | 0 <= k < |res|
        ensures res[k].0 == x.0 || (exists i :: 0 <= i < |r| && res[k].0 == r[i].0)
      {
        if k > 0 { assert res[k] == r[k - 1]; }
      }
    } else {
      var y := (if x.0 < r[0].0 then x.0 else r[0].0, if x.1 > r[0].1 then x.1 else r[0].1);
      InsertProps(r[1..], y);
      assert res == Insert(r[1..], y);
      forall p ensures Covered(res, p) <==> (Covered(r, p) || In(x, p)) {
        assert In(y, p) <==> (In(x, p) || In(r[0], p));
        if Covered(r[1..], p) {
          var j :| 0 <= j < |r[1..]| && In(r[1..][j], p);
          assert In(r[j + 1], p);
        }
        if Covered(r, p) {
          var i :| 0 <= i < |r| && In(r[i], p);
          if i > 0 { assert In(r[1..][i - 1], p); }
        }
      }
      forall k | 0 <= k < |res|
        ensures res[k].0 == x.0 || (exists i :: 0 <= i < |r| && res[k].0 == r[i].0)
      {
        if res[k].0 != x.0 {
          if res[k].0 == y.0 {
            assert y.0 == r[0].0;
          } else {
            var i :| 0 <= i < |r[1..]| && res[k].0 == r[1..][i].0;
            assert r[1..][i] == r[i + 1];
          }
        }
      }
    }
  }

  method merge_intervals(iv: seq<(int, int)>) returns (r: seq<(int, int)>)
    requires Valid(iv)
    ensures Canonical(r)
    ensures forall p :: Covered(r, p) <==> Covered(iv, p)
  {
    r := [];
    var i := 0;
    while i < |iv|
      invariant 0 <= i <= |iv|
      invariant Canonical(r)
      invariant forall p :: Covered(r, p) <==> Covered(iv[..i], p)
    {
      InsertProps(r, iv[i]);
      forall p ensures Covered(iv[..i + 1], p) <==> (Covered(iv[..i], p) || In(iv[i], p)) {
        if Covered(iv[..i + 1], p) {
          var j :| 0 <= j < i + 1 && In(iv[..i + 1][j], p);
          if j < i { assert In(iv[..i][j], p); }
        }
        if Covered(iv[..i], p) {
          var j :| 0 <= j < i && In(iv[..i][j], p);
          assert In(iv[..i + 1][j], p);
        }
        if In(iv[i], p) { assert In(iv[..i + 1][i], p); }
      }
      r := Insert(r, iv[i]);
      i := i + 1;
    }
    assert iv[..i] == iv;
  }
}
