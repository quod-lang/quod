module Solution {

  // Expansion of a run-length encoding back into a flat sequence.
  function Expand(r: seq<(int, int)>): seq<int>
    decreases |r|
  {
    if |r| == 0 then []
    else seq(if r[0].1 < 0 then 0 else r[0].1, _ => r[0].0) + Expand(r[1..])
  }

  lemma Expand_Concat(a: seq<(int, int)>, b: seq<(int, int)>)
    ensures Expand(a + b) == Expand(a) + Expand(b)
    decreases |a|
  {
    if |a| == 0 {
      assert a + b == b;
      assert Expand([]) == [];
    } else {
      assert (a + b)[0] == a[0];
      assert (a + b)[1..] == a[1..] + b;
      Expand_Concat(a[1..], b);
      assert Expand(a + b) == seq(if a[0].1 < 0 then 0 else a[0].1, _ => a[0].0) + Expand(a[1..] + b);
      assert Expand(a[1..] + b) == Expand(a[1..]) + Expand(b);
      assert Expand(a) == seq(if a[0].1 < 0 then 0 else a[0].1, _ => a[0].0) + Expand(a[1..]);
    }
  }

  lemma Expand_Single(p: (int, int))
    requires p.1 >= 0
    ensures Expand([p]) == seq(p.1, _ => p.0)
  {
    assert [p][1..] == [];
    assert Expand([]) == [];
  }

  method rle_encode(xs: seq<int>) returns (r: seq<(int, int)>)
    ensures forall k :: 0 <= k < |r| ==> r[k].1 >= 1
    ensures forall k :: 0 <= k < |r| - 1 ==> r[k].0 != r[k + 1].0
    ensures Expand(r) == xs
  {
    r := [];
    var i := 0;
    while i < |xs|
      invariant 0 <= i <= |xs|
      invariant forall k :: 0 <= k < |r| ==> r[k].1 >= 1
      invariant forall k :: 0 <= k < |r| - 1 ==> r[k].0 != r[k + 1].0
      invariant Expand(r) == xs[..i]
      decreases |xs| - i
    {
      var x := xs[i];
      if |r| > 0 && r[|r| - 1].0 == x {
        var last := r[|r| - 1];
        var prefix := r[..|r| - 1];
        assert r == prefix + [last];
        assert last.1 >= 1;
        r := prefix + [(x, last.1 + 1)];
        assert forall k :: 0 <= k < |r| ==> r[k].1 >= 1;
        assert forall k :: 0 <= k < |r| - 1 ==> r[k].0 != r[k + 1].0;
        Expand_Concat(prefix, [last]);
        Expand_Single(last);
        Expand_Concat(prefix, [(x, last.1 + 1)]);
        Expand_Single((x, last.1 + 1));
        assert seq(last.1 + 1, _ => x) == seq(last.1, _ => x) + [x];
        assert xs[..i + 1] == xs[..i] + [x];
      } else {
        Expand_Concat(r, [(x, 1)]);
        Expand_Single((x, 1));
        r := r + [(x, 1)];
        assert xs[..i + 1] == xs[..i] + [x];
      }
      i := i + 1;
    }
    assert xs[..i] == xs;
  }
}
