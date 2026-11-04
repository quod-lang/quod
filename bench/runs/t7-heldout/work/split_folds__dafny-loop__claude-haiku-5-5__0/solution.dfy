module Solution {

  // Page i is the first page of a fold: it is classified 1, or it is not a
  // separator and is at the start of the batch or directly after a separator.
  predicate IsStart(pages: seq<int>, i: int)
  {
    0 <= i < |pages| &&
    (pages[i] == 1 || (pages[i] != 2 && (i == 0 || pages[i - 1] == 2)))
  }

  // The first page after s that is classified 1 or 2 (a new fold or a
  // separator), or the length of the batch if there is none.
  function Boundary(pages: seq<int>, s: int): int
    requires 0 <= s < |pages|
    decreases |pages| - s
  {
    if s + 1 == |pages| then |pages|
    else if pages[s + 1] == 1 || pages[s + 1] == 2 then s + 1
    else Boundary(pages, s + 1)
  }

  method split_folds(pages: seq<int>) returns (r: seq<(int, int)>)
    requires forall i :: 0 <= i < |pages| ==> pages[i] == 0 || pages[i] == 1 || pages[i] == 2
    ensures forall k :: 0 <= k < |r| ==>
              (0 <= r[k].0 < |pages| && IsStart(pages, r[k].0) && r[k].1 == Boundary(pages, r[k].0))
    ensures forall s :: 0 <= s < |pages| && IsStart(pages, s) ==>
              exists k :: 0 <= k < |r| && r[k].0 == s
    ensures forall k, l :: 0 <= k < l < |r| ==> r[k].0 < r[l].0
  {
    var n := |pages|;
    r := [];
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant forall k :: 0 <= k < |r| ==>
                  (0 <= r[k].0 < i && IsStart(pages, r[k].0) && r[k].1 == Boundary(pages, r[k].0))
      invariant forall s :: 0 <= s < i && IsStart(pages, s) ==>
                  exists k :: 0 <= k < |r| && r[k].0 == s
      invariant forall k, l :: 0 <= k < l < |r| ==> r[k].0 < r[l].0
    {
      if IsStart(pages, i) {
        var prev := r;
        r := r + [(i, Boundary(pages, i))];
        assert |r| == |prev| + 1;
        assert r[|prev|].0 == i;
        assert forall k :: 0 <= k < |prev| ==> r[k] == prev[k];
      }
      i := i + 1;
    }
  }
}
