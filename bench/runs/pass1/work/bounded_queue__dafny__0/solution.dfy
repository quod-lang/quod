module Solution {
  function QueueAfter(capacity: int, ops: seq<int>): seq<int>
    decreases |ops|
  {
    if |ops| == 0 then []
    else
      var q := QueueAfter(capacity, ops[..|ops|-1]);
      var x := ops[|ops|-1];
      if x > 0 then
        (if |q| >= capacity && |q| > 0 then q[1..] + [x] else q + [x])
      else if |q| > 0 then q[1..]
      else q
  }

  function OutAfter(capacity: int, ops: seq<int>): seq<int>
    decreases |ops|
  {
    if |ops| == 0 then []
    else
      var q := QueueAfter(capacity, ops[..|ops|-1]);
      var o := OutAfter(capacity, ops[..|ops|-1]);
      var x := ops[|ops|-1];
      if x > 0 then o
      else if |q| > 0 then o + [q[0]]
      else o + [-1]
  }

  method bounded_queue(capacity: int, ops: seq<int>) returns (out: seq<int>)
    requires capacity >= 1
    requires forall i :: 0 <= i < |ops| ==> ops[i] >= 0
    ensures out == OutAfter(capacity, ops)
  {
    var q: seq<int> := [];
    out := [];
    var i := 0;
    while i < |ops|
      invariant 0 <= i <= |ops|
      invariant q == QueueAfter(capacity, ops[..i])
      invariant out == OutAfter(capacity, ops[..i])
      decreases |ops| - i
    {
      assert ops[..i+1][..i] == ops[..i];
      var x := ops[i];
      if x > 0 {
        if |q| >= capacity && |q| > 0 {
          q := q[1..] + [x];
        } else {
          q := q + [x];
        }
      } else {
        if |q| > 0 {
          out := out + [q[0]];
          q := q[1..];
        } else {
          out := out + [-1];
        }
      }
      i := i + 1;
    }
    assert ops[..|ops|] == ops;
  }
}
