module Solution {
  function Rep(v: int, c: int): seq<int>
  {
    if c <= 0 then [] else seq(c, _ => v)
  }

  function Decode(r: seq<(int, int)>): seq<int>
  {
    if |r| == 0 then [] else Decode(r[..|r|-1]) + Rep(r[|r|-1].0, r[|r|-1].1)
  }

  method rle_encode(xs: seq<int>) returns (r: seq<(int, int)>)
    ensures forall i :: 0 <= i < |r| ==> r[i].1 >= 1
    ensures forall i :: 0 <= i < |r| - 1 ==> r[i].0 != r[i+1].0
    ensures Decode(r) == xs
  {
    r := [];
    var i := 0;
    while i < |xs|
      invariant 0 <= i <= |xs|
      invariant forall k :: 0 <= k < |r| ==> r[k].1 >= 1
      invariant forall k :: 0 <= k < |r| - 1 ==> r[k].0 != r[k+1].0
      invariant Decode(r) == xs[..i]
      invariant i > 0 ==> |r| > 0 && r[|r|-1].0 == xs[i-1]
      invariant i == 0 ==> r == []
    {
      if |r| > 0 && r[|r|-1].0 == xs[i] {
        var n := |r|;
        var p := r[n-1];
        var r0 := r[..n-1];
        assert r == r0 + [p];
        assert Decode(r) == Decode(r0) + Rep(p.0, p.1);
        assert Rep(p.0, p.1 + 1) == Rep(p.0, p.1) + [p.0];
        var r' := r0 + [(p.0, p.1 + 1)];
        assert r'[..n-1] == r0;
        assert Decode(r') == Decode(r0) + Rep(p.0, p.1 + 1);
        r := r';
      } else {
        var r' := r + [(xs[i], 1)];
        assert r'[..|r|] == r;
        assert Rep(xs[i], 1) == [xs[i]];
        r := r';
      }
      assert xs[..i+1] == xs[..i] + [xs[i]];
      i := i + 1;
    }
    assert xs[..i] == xs;
  }
}
