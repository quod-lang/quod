module Solution {

  // Folds of pages[i..] given that `cur` is the start of the currently open
  // fold (or -1 if no fold is open). Each fold is (start, end) with end exclusive.
  function Go(pages: seq<int>, i: int, cur: int): seq<(int, int)>
    requires 0 <= i <= |pages|
    requires -1 <= cur < i
    decreases |pages| - i
  {
    if i == |pages| then
      if cur >= 0 then [(cur, i)] else []
    else if pages[i] == 1 then
      (if cur >= 0 then [(cur, i)] else []) + Go(pages, i + 1, i)
    else if pages[i] == 0 then
      if cur >= 0 then Go(pages, i + 1, cur) else Go(pages, i + 1, i)
    else
      (if cur >= 0 then [(cur, i)] else []) + Go(pages, i + 1, -1)
  }

  method split_folds(pages: seq<int>) returns (r: seq<(int, int)>)
    requires forall k :: 0 <= k < |pages| ==> pages[k] == 0 || pages[k] == 1 || pages[k] == 2
    ensures r == Go(pages, 0, -1)
  {
    var i := 0;
    var cur := -1;
    r := [];
    while i < |pages|
      invariant 0 <= i <= |pages|
      invariant -1 <= cur < i
      invariant r + Go(pages, i, cur) == Go(pages, 0, -1)
      decreases |pages| - i
    {
      var p := pages[i];
      if p == 1 {
        if cur >= 0 {
          r := r + [(cur, i)];
        }
        cur := i;
      } else if p == 0 {
        if cur < 0 {
          cur := i;
        }
      } else {
        if cur >= 0 {
          r := r + [(cur, i)];
        }
        cur := -1;
      }
      i := i + 1;
    }
    assert Go(pages, i, cur) == (if cur >= 0 then [(cur, |pages|)] else []);
    r := r + (if cur >= 0 then [(cur, |pages|)] else []);
  }
}
