module Solution {
  function Decode(r: seq<(int, int)>): seq<int>
    requires forall i :: 0 <= i < |r| ==> r[i].1 >= 1
  {
    if |r| == 0 then [] else Decode(r[..|r| - 1]) + seq(r[|r| - 1].1, _ => r[|r| - 1].0)
  }

  method rle_encode(xs: seq<int>) returns (r: seq<(int, int)>)
    ensures forall i :: 0 <= i < |r| ==> r[i].1 >= 1
    ensures forall i :: 0 <= i < |r| - 1 ==> r[i].0 != r[i + 1].0
    ensures Decode(r) == xs
  {
    r := [];
    var k := 0;
    while k < |xs|
      invariant 0 <= k <= |xs|
      invariant forall i :: 0 <= i < |r| ==> r[i].1 >= 1
      invariant forall i :: 0 <= i < |r| - 1 ==> r[i].0 != r[i + 1].0
      invariant Decode(r) == xs[..k]
      invariant k > 0 <==> |r| > 0
      invariant k > 0 ==> r[|r| - 1].0 == xs[k - 1]
    {
      if |r| > 0 && r[|r| - 1].0 == xs[k] {
        var last := r[|r| - 1];
        var prefix := r[..|r| - 1];
        var r' := prefix + [(last.0, last.1 + 1)];
        assert r'[..|r'| - 1] == prefix;
        assert r[..|r| - 1] == prefix;
        assert seq(last.1 + 1, _ => last.0) == seq(last.1, _ => last.0) + [xs[k]];
        r := r';
      } else {
        var r' := r + [(xs[k], 1)];
        assert r'[..|r'| - 1] == r;
        r := r';
      }
      assert xs[..k + 1] == xs[..k] + [xs[k]];
      k := k + 1;
    }
    assert xs[..k] == xs;
  }
}
