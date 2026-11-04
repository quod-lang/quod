module Solution {

  // Page s can start a fold: it is a fold-start page (classified 1), or it is
  // a non-separator at the start of the batch or right after a separator.
  ghost predicate StartOk(pages: seq<int>, s: int)
  {
    0 <= s < |pages| &&
    (pages[s] == 1 || (pages[s] == 0 && (s == 0 || pages[s - 1] == 2)))
  }

  // f = (start, end) is a well-formed fold of pages.
  ghost predicate FoldOk(pages: seq<int>, f: (int, int))
  {
    var s := f.0;
    var e := f.1;
    0 <= s < e <= |pages| &&
    StartOk(pages, s) &&
    (forall j :: s <= j < e ==> pages[j] != 2) &&
    (forall j :: s < j < e ==> pages[j] != 1) &&
    (e == |pages| || pages[e] == 1 || pages[e] == 2)
  }

  // r is exactly the list of folds of pages, in order.
  ghost predicate ValidFolds(pages: seq<int>, r: seq<(int, int)>)
  {
    (forall k :: 0 <= k < |r| ==> FoldOk(pages, r[k])) &&
    (forall k :: 0 <= k < |r| - 1 ==> r[k].1 <= r[k + 1].0) &&
    (forall j :: 0 <= j < |pages| && pages[j] != 2 ==>
        exists k :: 0 <= k < |r| && r[k].0 <= j < r[k].1)
  }

  // Appending the fold (s, e) keeps every non-separator page below e covered.
  lemma CoverAppend(pages: seq<int>, r: seq<(int, int)>, s: int, e: int)
    requires 0 <= s <= e <= |pages|
    requires forall j :: 0 <= j < s && pages[j] != 2 ==>
        exists k :: 0 <= k < |r| && r[k].0 <= j < r[k].1
    ensures forall j :: 0 <= j < e && pages[j] != 2 ==>
        exists k :: 0 <= k < |r + [(s, e)]| && (r + [(s, e)])[k].0 <= j < (r + [(s, e)])[k].1
  {
    forall j | 0 <= j < e && pages[j] != 2
      ensures exists k :: 0 <= k < |r + [(s, e)]| && (r + [(s, e)])[k].0 <= j < (r + [(s, e)])[k].1
    {
      if j < s {
        var k :| 0 <= k < |r| && r[k].0 <= j < r[k].1;
        assert (r + [(s, e)])[k] == r[k];
      } else {
        assert (r + [(s, e)])[|r|] == (s, e);
      }
    }
  }

  method split_folds(pages: seq<int>) returns (r: seq<(int, int)>)
    requires forall j :: 0 <= j < |pages| ==> pages[j] == 0 || pages[j] == 1 || pages[j] == 2
    ensures ValidFolds(pages, r)
  {
    var n := |pages|;
    var i := 0;
    // cur: start of the currently open fold, or -1 if none is open.
    var cur := -1;
    r := [];

    while i < n
      invariant 0 <= i <= n
      invariant forall k :: 0 <= k < |r| ==> FoldOk(pages, r[k])
      invariant forall k :: 0 <= k < |r| - 1 ==> r[k].1 <= r[k + 1].0
      invariant forall k :: 0 <= k < |r| ==> r[k].1 <= (if cur >= 0 then cur else i)
      invariant cur < 0 ==> (i == 0 || pages[i - 1] == 2)
      invariant cur >= 0 ==>
        cur < i && StartOk(pages, cur) &&
        (forall j :: cur <= j < i ==> pages[j] != 2) &&
        (forall j :: cur < j < i ==> pages[j] != 1)
      invariant forall j :: 0 <= j < (if cur >= 0 then cur else i) && pages[j] != 2 ==>
        exists k :: 0 <= k < |r| && r[k].0 <= j < r[k].1
      decreases n - i
    {
      if pages[i] == 2 {
        if cur >= 0 {
          CoverAppend(pages, r, cur, i);
          r := r + [(cur, i)];
          cur := -1;
        }
      } else if pages[i] == 1 {
        if cur >= 0 {
          CoverAppend(pages, r, cur, i);
          r := r + [(cur, i)];
        }
        cur := i;
      } else {
        if cur < 0 {
          cur := i;
        }
      }
      i := i + 1;
    }

    if cur >= 0 {
      CoverAppend(pages, r, cur, n);
      r := r + [(cur, n)];
    }
  }
}
