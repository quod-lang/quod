module Solution {

  // A run of `c` copies of `v` (empty when c <= 0).
  function Run(v: int, c: int): seq<int>
  {
    seq(if c > 0 then c else 0, _ => v)
  }

  // Expansion of a run-length encoding back into a flat sequence.
  function Expand(r: seq<(int, int)>): seq<int>
    decreases |r|
  {
    if |r| == 0 then []
    else Expand(r[..|r|-1]) + Run(r[|r|-1].0, r[|r|-1].1)
  }

  lemma RunSucc(v: int, c: int)
    requires c >= 0
    ensures Run(v, c + 1) == Run(v, c) + [v]
  {
    var a := Run(v, c + 1);
    var b := Run(v, c) + [v];
    assert |a| == c + 1 && |b| == c + 1;
    forall k | 0 <= k < c + 1
      ensures a[k] == b[k]
    {
      if k < c {
        assert b[k] == Run(v, c)[k];
      } else {
        assert b[k] == v;
      }
    }
    assert a == b;
  }

  lemma ExpandAppend(r: seq<(int, int)>, p: (int, int))
    ensures Expand(r + [p]) == Expand(r) + Run(p.0, p.1)
  {
    var s := r + [p];
    assert |s| == |r| + 1;
    assert s[..|s|-1] == r;
    assert s[|s|-1] == p;
  }

  lemma ExpandUnfold(r: seq<(int, int)>)
    requires |r| > 0
    ensures Expand(r) == Expand(r[..|r|-1]) + Run(r[|r|-1].0, r[|r|-1].1)
  {
  }

  method rle_encode(xs: seq<int>) returns (r: seq<(int, int)>)
    ensures Expand(r) == xs
    ensures forall k :: 0 <= k < |r| ==> r[k].1 >= 1
    ensures forall k :: 0 <= k < |r| - 1 ==> r[k].0 != r[k + 1].0
  {
    r := [];
    var i := 0;
    while i < |xs|
      invariant 0 <= i <= |xs|
      invariant Expand(r) == xs[..i]
      invariant forall k :: 0 <= k < |r| ==> r[k].1 >= 1
      invariant forall k :: 0 <= k < |r| - 1 ==> r[k].0 != r[k + 1].0
      decreases |xs| - i
    {
      var v := xs[i];
      if |r| > 0 && r[|r| - 1].0 == v {
        var n := |r| - 1;
        var c := r[n].1;
        var prefix := r[..n];
        ExpandUnfold(r);
        RunSucc(v, c);
        ExpandAppend(prefix, (v, c + 1));
        r := prefix + [(v, c + 1)];
      } else {
        ExpandAppend(r, (v, 1));
        r := r + [(v, 1)];
      }
      SnocSlice(xs, i);
      i := i + 1;
    }
  }

  lemma SnocSlice(xs: seq<int>, i: int)
    requires 0 <= i < |xs|
    ensures xs[..i] + [xs[i]] == xs[..i + 1]
  {
  }
}
