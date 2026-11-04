module Solution {

  // ---------------------------------------------------------------------
  // Specification helpers
  // ---------------------------------------------------------------------

  // A fold starts at a page classified 1, or at a continuation page (0)
  // that is the first page of the batch or directly follows a separator (2).
  predicate IsStart(pages: seq<int>, i: int)
  {
    0 <= i < |pages| && (pages[i] == 1 || (pages[i] == 0 && (i == 0 || pages[i - 1] == 2)))
  }

  // [s, e) is a fold: it starts at a start page, every page strictly inside it
  // is a continuation page (0), and it ends at the end of the batch or just
  // before a page classified 1 or 2.
  predicate FoldAt(pages: seq<int>, s: int, e: int)
  {
    0 <= s < e <= |pages| && IsStart(pages, s) &&
    (forall m :: s < m < e ==> pages[m] == 0) &&
    (e == |pages| || pages[e] != 0)
  }

  // First index >= m whose page is not a continuation page (0), or |pages|.
  function FoldEnd(pages: seq<int>, m: int): int
    requires 0 <= m <= |pages|
    ensures m <= FoldEnd(pages, m) <= |pages|
    decreases |pages| - m
  {
    if m == |pages| || pages[m] != 0 then m
    else FoldEnd(pages, m + 1)
  }

  lemma FoldEndProps(pages: seq<int>, m: int)
    requires 0 <= m <= |pages|
    ensures FoldEnd(pages, m) == |pages| || pages[FoldEnd(pages, m)] != 0
    ensures forall q :: m <= q < FoldEnd(pages, m) ==> pages[q] == 0
    decreases |pages| - m
  {
    if m < |pages| && pages[m] == 0 {
      FoldEndProps(pages, m + 1);
      assert FoldEnd(pages, m) == FoldEnd(pages, m + 1);
    }
  }

  // Ghost specification: the folds of pages[i..], computed greedily.
  function Split(pages: seq<int>, i: int): seq<(int, int)>
    requires 0 <= i <= |pages|
    decreases |pages| - i
  {
    if i == |pages| then []
    else if pages[i] == 2 then Split(pages, i + 1)
    else [(i, FoldEnd(pages, i + 1))] + Split(pages, FoldEnd(pages, i + 1))
  }

  // Positions the greedy scan can stop at: batch start, after a separator,
  // or at a page that is not a continuation page.
  predicate Reach(pages: seq<int>, i: int)
    requires 0 <= i <= |pages|
  {
    i == 0 || i == |pages| || pages[i - 1] == 2 || pages[i] != 0
  }

  // s is exactly the folds of pages[i..].
  predicate GoodFrom(pages: seq<int>, i: int, s: seq<(int, int)>)
    requires 0 <= i
  {
    (forall k :: 0 <= k < |s| ==> i <= s[k].0 && FoldAt(pages, s[k].0, s[k].1)) &&
    (forall k :: 0 <= k < |s| - 1 ==> s[k].1 <= s[k + 1].0) &&
    (forall x :: i <= x < |pages| && IsStart(pages, x) ==> exists k :: 0 <= k < |s| && s[k].0 == x) &&
    (forall x :: i <= x < |pages| ==> (pages[x] != 2 <==> exists k :: 0 <= k < |s| && s[k].0 <= x < s[k].1))
  }

  // Prepending a separator page does not change the folds.
  lemma SepStep(pages: seq<int>, i: int, s: seq<(int, int)>)
    requires 0 <= i < |pages| && pages[i] == 2
    requires GoodFrom(pages, i + 1, s)
    ensures GoodFrom(pages, i, s)
  {
    forall x | i <= x < |pages| ensures (pages[x] != 2 <==> exists k :: 0 <= k < |s| && s[k].0 <= x < s[k].1) {
      if x == i {
        assert pages[x] == 2;
        forall k | 0 <= k < |s| ensures !(s[k].0 <= x < s[k].1) {
          assert s[k].0 >= i + 1;
        }
      }
    }
  }

  // Facts about s = [(i, j)] + t, phrased without concatenation so the
  // lemmas below stay small for the solver.
  predicate IsCons(i: int, j: int, t: seq<(int, int)>, s: seq<(int, int)>)
  {
    |s| == |t| + 1 && s[0] == (i, j) && (forall k :: 0 <= k < |t| ==> s[k + 1] == t[k])
  }

  // Clauses 1 and 2 of GoodFrom for a prepended fold.
  lemma FoldStepC12(pages: seq<int>, i: int, j: int, t: seq<(int, int)>, s: seq<(int, int)>)
    requires 0 <= i < j <= |pages|
    requires FoldAt(pages, i, j)
    requires GoodFrom(pages, j, t)
    requires IsCons(i, j, t, s)
    ensures forall k :: 0 <= k < |s| ==> i <= s[k].0 && FoldAt(pages, s[k].0, s[k].1)
    ensures forall k :: 0 <= k < |s| - 1 ==> s[k].1 <= s[k + 1].0
  {
    forall k | 0 <= k < |s| ensures i <= s[k].0 && FoldAt(pages, s[k].0, s[k].1) {
      if k == 0 {
      } else {
        assert s[k] == t[k - 1];
      }
    }
    forall k | 0 <= k < |s| - 1 ensures s[k].1 <= s[k + 1].0 {
      if k == 0 {
        assert s[1] == t[0];
        assert t[0].0 >= j;
      } else {
        assert s[k] == t[k - 1];
        assert s[k + 1] == t[k];
      }
    }
  }

  // Clause 3 of GoodFrom for a prepended fold.
  lemma FoldStepC3(pages: seq<int>, i: int, j: int, t: seq<(int, int)>, s: seq<(int, int)>)
    requires 0 <= i < j <= |pages|
    requires FoldAt(pages, i, j)
    requires GoodFrom(pages, j, t)
    requires IsCons(i, j, t, s)
    ensures forall x :: i <= x < |pages| && IsStart(pages, x) ==> exists k :: 0 <= k < |s| && s[k].0 == x
  {
    forall x | i <= x < |pages| && IsStart(pages, x) ensures exists k :: 0 <= k < |s| && s[k].0 == x {
      if x == i {
        assert s[0].0 == x;
      } else if x < j {
        assert pages[x] == 0;
        assert pages[x - 1] != 2;
        assert !IsStart(pages, x);
      } else {
        var k' :| 0 <= k' < |t| && t[k'].0 == x;
        assert s[k' + 1] == t[k'];
      }
    }
  }

  // Clause 4 of GoodFrom for a prepended fold.
  lemma FoldStepC4(pages: seq<int>, i: int, j: int, t: seq<(int, int)>, s: seq<(int, int)>)
    requires 0 <= i < j <= |pages|
    requires FoldAt(pages, i, j)
    requires GoodFrom(pages, j, t)
    requires IsCons(i, j, t, s)
    ensures forall x :: i <= x < |pages| ==> (pages[x] != 2 <==> exists k :: 0 <= k < |s| && s[k].0 <= x < s[k].1)
  {
    forall x | i <= x < |pages| ensures (pages[x] != 2 <==> exists k :: 0 <= k < |s| && s[k].0 <= x < s[k].1) {
      if x < j {
        assert pages[x] != 2;
        assert s[0].0 <= x < s[0].1;
      } else {
        if exists k :: 0 <= k < |t| && t[k].0 <= x < t[k].1 {
          var k' :| 0 <= k' < |t| && t[k'].0 <= x < t[k'].1;
          assert s[k' + 1] == t[k'];
        }
        if exists k :: 0 <= k < |s| && s[k].0 <= x < s[k].1 {
          var k2 :| 0 <= k2 < |s| && s[k2].0 <= x < s[k2].1;
          if k2 == 0 {
            assert s[0].1 == j;
            assert false;
          } else {
            assert s[k2] == t[k2 - 1];
          }
        }
      }
    }
  }

  // Prepending a fold [i, j) to the folds t of pages[j..].
  lemma FoldStep(pages: seq<int>, i: int, j: int, t: seq<(int, int)>)
    requires 0 <= i < j <= |pages|
    requires FoldAt(pages, i, j)
    requires GoodFrom(pages, j, t)
    ensures GoodFrom(pages, i, [(i, j)] + t)
  {
    var s := [(i, j)] + t;
    assert IsCons(i, j, t, s);
    FoldStepC12(pages, i, j, t, s);
    FoldStepC3(pages, i, j, t, s);
    FoldStepC4(pages, i, j, t, s);
  }

  // Induction: Split(pages, i) is GoodFrom(pages, i, ...) whenever i is reachable.
  lemma SplitGood(pages: seq<int>, i: int)
    requires forall q :: 0 <= q < |pages| ==> pages[q] == 0 || pages[q] == 1 || pages[q] == 2
    requires 0 <= i <= |pages|
    requires Reach(pages, i)
    ensures GoodFrom(pages, i, Split(pages, i))
    decreases |pages| - i
  {
    if i == |pages| {
      assert Split(pages, i) == [];
    } else if pages[i] == 2 {
      SplitGood(pages, i + 1);
      assert Split(pages, i) == Split(pages, i + 1);
      SepStep(pages, i, Split(pages, i + 1));
    } else {
      var j := FoldEnd(pages, i + 1);
      FoldEndProps(pages, i + 1);
      assert i + 1 <= j <= |pages|;
      assert Reach(pages, j);
      SplitGood(pages, j);
      assert IsStart(pages, i) by {
        if pages[i] == 0 {
          assert i == 0 || pages[i - 1] == 2;
        }
      }
      assert FoldAt(pages, i, j);
      assert Split(pages, i) == [(i, j)] + Split(pages, j);
      FoldStep(pages, i, j, Split(pages, j));
    }
  }

  // ---------------------------------------------------------------------
  // Method
  // ---------------------------------------------------------------------

  method split_folds(pages: seq<int>) returns (r: seq<(int, int)>)
    requires forall i :: 0 <= i < |pages| ==> pages[i] == 0 || pages[i] == 1 || pages[i] == 2
    ensures forall k :: 0 <= k < |r| ==> FoldAt(pages, r[k].0, r[k].1)
    ensures forall k :: 0 <= k < |r| - 1 ==> r[k].1 <= r[k + 1].0
    ensures forall x :: 0 <= x < |pages| && IsStart(pages, x) ==> exists k :: 0 <= k < |r| && r[k].0 == x
    ensures forall x :: 0 <= x < |pages| ==> (pages[x] != 2 <==> exists k :: 0 <= k < |r| && r[k].0 <= x < r[k].1)
  {
    var n := |pages|;
    var i := 0;
    r := [];
    while i < n
      invariant 0 <= i <= n
      invariant Reach(pages, i)
      invariant r + Split(pages, i) == Split(pages, 0)
      decreases n - i
    {
      if pages[i] == 2 {
        assert Split(pages, i) == Split(pages, i + 1);
        i := i + 1;
      } else {
        var j := i + 1;
        while j < n && pages[j] == 0
          invariant i + 1 <= j <= n
          invariant FoldEnd(pages, j) == FoldEnd(pages, i + 1)
          invariant forall q :: i < q < j ==> pages[q] == 0
          decreases n - j
        {
          assert FoldEnd(pages, j) == FoldEnd(pages, j + 1);
          j := j + 1;
        }
        assert FoldEnd(pages, j) == j;
        assert Split(pages, i) == [(i, j)] + Split(pages, j);
        assert r + Split(pages, i) == (r + [(i, j)]) + Split(pages, j);
        r := r + [(i, j)];
        assert Reach(pages, j);
        i := j;
      }
    }
    assert Split(pages, n) == [];
    assert r == Split(pages, 0);
    SplitGood(pages, 0);
    assert GoodFrom(pages, 0, r);
  }
}
