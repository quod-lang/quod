module Solution {
  // Expands a run-length encoding back into the flat sequence it describes.
  // Non-positive counts contribute nothing (valid encodings always have counts >= 1).
  function Expand(r: seq<(int, int)>): seq<int>
    decreases |r|
  {
    if |r| == 0 then []
    else
      var c := if r[0].1 > 0 then r[0].1 else 0;
      seq(c, _ => r[0].0) + Expand(r[1..])
  }

  // Expanding r + [p] appends the expansion of p.
  lemma ExpandAppend(r: seq<(int, int)>, p: (int, int))
    requires p.1 >= 1
    requires forall k :: 0 <= k < |r| ==> r[k].1 >= 1
    ensures Expand(r + [p]) == Expand(r) + seq(p.1, _ => p.0)
    decreases |r|
  {
    if |r| == 0 {
      assert r + [p] == [p];
      assert Expand([p]) == seq(p.1, _ => p.0) + Expand([]);
      assert seq(p.1, _ => p.0) + [] == seq(p.1, _ => p.0);
    } else {
      assert (r + [p])[1..] == r[1..] + [p];
      assert forall k :: 0 <= k < |r[1..]| ==> r[1..][k].1 >= 1;
      ExpandAppend(r[1..], p);
      assert Expand(r + [p]) == seq(r[0].1, _ => r[0].0) + Expand(r[1..] + [p]);
      assert Expand(r) == seq(r[0].1, _ => r[0].0) + Expand(r[1..]);
      calc {
        Expand(r + [p]);
        seq(r[0].1, _ => r[0].0) + Expand(r[1..] + [p]);
        seq(r[0].1, _ => r[0].0) + (Expand(r[1..]) + seq(p.1, _ => p.0));
        (seq(r[0].1, _ => r[0].0) + Expand(r[1..])) + seq(p.1, _ => p.0);
        Expand(r) + seq(p.1, _ => p.0);
      }
    }
  }

  lemma SeqSnoc(n: nat, v: int)
    ensures seq(n + 1, _ => v) == seq(n, _ => v) + [v]
  {
  }

  method rle_encode(xs: seq<int>) returns (r: seq<(int, int)>)
    ensures Expand(r) == xs
    ensures forall k :: 0 <= k < |r| ==> r[k].1 >= 1
    ensures forall k :: 0 <= k < |r| - 1 ==> r[k].0 != r[k + 1].0
  {
    if |xs| == 0 {
      return [];
    }

    // Completed runs are in r; the current (open) run is (cv, cc).
    r := [];
    var cv := xs[0];
    var cc := 0;
    var i := 0;

    while i < |xs|
      invariant 0 <= i <= |xs|
      invariant i == 0 ==> r == [] && cc == 0
      invariant i > 0 ==> cc >= 1 && cv == xs[i - 1]
      invariant i > 0 ==> Expand(r) + seq(cc, _ => cv) == xs[..i]
      invariant forall k :: 0 <= k < |r| ==> r[k].1 >= 1
      invariant forall k :: 0 <= k < |r| - 1 ==> r[k].0 != r[k + 1].0
      invariant |r| > 0 ==> r[|r| - 1].0 != cv
      decreases |xs| - i
    {
      if i == 0 {
        cv := xs[0];
        cc := 1;
      } else if xs[i] == cv {
        SeqSnoc(cc, cv);
        assert xs[..i + 1] == xs[..i] + [xs[i]];
        cc := cc + 1;
      } else {
        ExpandAppend(r, (cv, cc));
        assert xs[..i + 1] == xs[..i] + [xs[i]];
        r := r + [(cv, cc)];
        cv := xs[i];
        cc := 1;
      }
      i := i + 1;
    }

    r := r + [(cv, cc)];
    assert xs[..|xs|] == xs;
    ExpandAppend(r[..|r| - 1], (cv, cc));
    assert r[..|r| - 1] + [(cv, cc)] == r;
    assert Expand(r) == xs;
  }
}
