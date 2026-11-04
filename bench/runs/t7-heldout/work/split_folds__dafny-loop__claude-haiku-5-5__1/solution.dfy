module Solution {

  // Every page is classified as 0 (continuation), 1 (first page), or 2 (separator).
  predicate ValidPages(pages: seq<int>) {
    forall i :: 0 <= i < |pages| ==> pages[i] == 0 || pages[i] == 1 || pages[i] == 2
  }

  // Index of the first page at or after j that is not a continuation page (0),
  // or |pages| if there is none. A fold starting at j ends here.
  function FoldEnd(pages: seq<int>, j: int): int
    requires 0 <= j <= |pages|
    ensures j <= FoldEnd(pages, j) <= |pages|
    decreases |pages| - j
  {
    if j >= |pages| then |pages|
    else if pages[j] != 0 then j
    else FoldEnd(pages, j + 1)
  }

  // Folds of the suffix of pages starting at index i.
  // A non-separator page reached here always starts a fold: either it is
  // classified 1, or it is at the start of the batch or right after a separator
  // (the only positions where the scan resumes, since a fold ends just before a 1 or a 2).
  function Folds(pages: seq<int>, i: int): seq<(int, int)>
    requires 0 <= i <= |pages|
    decreases |pages| - i
  {
    if i >= |pages| then []
    else if pages[i] == 2 then Folds(pages, i + 1)
    else
      var e := FoldEnd(pages, i + 1);
      [(i, e)] + Folds(pages, e)
  }

  method split_folds(pages: seq<int>) returns (r: seq<(int, int)>)
    requires ValidPages(pages)
    ensures r == Folds(pages, 0)
  {
    r := [];
    var i := 0;
    while i < |pages|
      invariant 0 <= i <= |pages|
      invariant r + Folds(pages, i) == Folds(pages, 0)
      decreases |pages| - i
    {
      if pages[i] == 2 {
        assert Folds(pages, i) == Folds(pages, i + 1);
        i := i + 1;
      } else {
        var k := i + 1;
        while k < |pages| && pages[k] == 0
          invariant i + 1 <= k <= |pages|
          invariant FoldEnd(pages, k) == FoldEnd(pages, i + 1)
          decreases |pages| - k
        {
          assert FoldEnd(pages, k) == FoldEnd(pages, k + 1);
          k := k + 1;
        }
        // Here k == |pages| or pages[k] != 0, so FoldEnd(pages, k) == k.
        assert FoldEnd(pages, k) == k;
        assert FoldEnd(pages, i + 1) == k;
        assert Folds(pages, i) == [(i, k)] + Folds(pages, k);
        r := r + [(i, k)];
        i := k;
      }
    }
  }
}
