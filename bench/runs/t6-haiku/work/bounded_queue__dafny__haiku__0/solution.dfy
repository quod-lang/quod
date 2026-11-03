module Solution {

  // Pure specification of the simulation.
  // q is the current queue content (oldest first), capacity is the bound.
  // Returns the outputs produced by the remaining operations.
  function Run(capacity: int, ops: seq<int>, q: seq<int>): seq<int>
    requires capacity >= 1
    requires |q| <= capacity
    decreases |ops|
  {
    if |ops| == 0 then []
    else if ops[0] == 0 then
      if |q| == 0 then [-1] + Run(capacity, ops[1..], q)
      else [q[0]] + Run(capacity, ops[1..], q[1..])
    else
      var q2 := if |q| == capacity then q[1..] else q;
      Run(capacity, ops[1..], q2 + [ops[0]])
  }

  method bounded_queue(capacity: int, ops: seq<int>) returns (out: seq<int>)
    requires capacity >= 1
    requires forall i :: 0 <= i < |ops| ==> ops[i] >= 0
    ensures out == Run(capacity, ops, [])
  {
    var q: seq<int> := [];
    out := [];
    var i := 0;
    while i < |ops|
      invariant 0 <= i <= |ops|
      invariant |q| <= capacity
      invariant out + Run(capacity, ops[i..], q) == Run(capacity, ops, [])
      decreases |ops| - i
    {
      var x := ops[i];
      assert ops[i..][0] == x;
      assert ops[i..][1..] == ops[i+1..];
      if x == 0 {
        if |q| == 0 {
          out := out + [-1];
        } else {
          out := out + [q[0]];
          q := q[1..];
        }
      } else {
        if |q| == capacity {
          q := q[1..];
        }
        q := q + [x];
      }
      i := i + 1;
    }
    assert ops[i..] == [];
  }
}
