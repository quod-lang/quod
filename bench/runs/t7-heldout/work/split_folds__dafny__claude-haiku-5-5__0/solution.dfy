module Solution {
  // Specification-level fold computation.
  // Walks the batch from index i, where cur is the start of the currently open
  // fold (or -1 if no fold is open). Each emitted pair (start, end) is a fold
  // covering pages start .. end-1.
  //  - a separator (2) closes the open fold, if any, and opens nothing;
  //  - a first page (1) closes the open fold, if any, and opens a new one at i;
  //  - a continuation page (0) opens a fold at i if none is open, else extends it.
  // At the end of the batch the open fold, if any, is closed at |pages|.
  ghost function Go(pages: seq<int>, i: int, cur: int): seq<(int, int)>
    requires 0 <= i <= |pages|
    requires cur == -1 || (0 <= cur < i)
    requires forall k :: 0 <= k < |pages| ==> pages[k] == 0 || pages[k] == 1 || pages[k] == 2
    decreases |pages| - i
  {
    if i == |pages| then
      (if cur >= 0 then [(cur, i)] else [])
    else if pages[i] == 2 then
      (if cur >= 0 then [(cur, i)] else []) + Go(pages, i + 1, -1)
    else if pages[i] == 1 then
      (if cur >= 0 then [(cur, i)] else []) + Go(pages, i + 1, i)
    else
      Go(pages, i + 1, if cur >= 0 then cur else i)
  }

  method split_folds(pages: seq<int>) returns (r: seq<(int, int)>)
    requires forall i :: 0 <= i < |pages| ==> pages[i] == 0 || pages[i] == 1 || pages[i] == 2
    ensures r == Go(pages, 0, -1)
    ensures forall k :: 0 <= k < |r| ==> r[k].0 < r[k].1
  {
    r := [];
    var i := 0;
    var cur := -1;
    while i < |pages|
      invariant 0 <= i <= |pages|
      invariant cur == -1 || (0 <= cur < i)
      invariant Go(pages, 0, -1) == r + Go(pages, i, cur)
      invariant forall k :: 0 <= k < |r| ==> r[k].0 < r[k].1
      decreases |pages| - i
    {
      var p := pages[i];
      if p == 2 {
        if cur >= 0 {
          r := r + [(cur, i)];
        }
        cur := -1;
      } else if p == 1 {
        if cur >= 0 {
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
      r := r + [(cur, |pages|)];
    }
  }
}
