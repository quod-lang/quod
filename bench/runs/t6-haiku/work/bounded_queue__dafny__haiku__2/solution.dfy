module Solution {

  // Enqueue x into queue q of capacity cap. If the queue is full,
  // the oldest element is dropped first.
  function Push(cap: int, q: seq<int>, x: int): seq<int>
    requires cap >= 1
  {
    if |q| >= cap then q[1..] + [x] else q + [x]
  }

  // Output produced when processing ops[i..] starting from queue q.
  function Outputs(cap: int, q: seq<int>, ops: seq<int>, i: int): seq<int>
    requires cap >= 1
    requires 0 <= i <= |ops|
    decreases |ops| - i
  {
    if i == |ops| then []
    else if ops[i] > 0 then
      Outputs(cap, Push(cap, q, ops[i]), ops, i + 1)
    else if |q| == 0 then
      [-1] + Outputs(cap, q, ops, i + 1)
    else
      [q[0]] + Outputs(cap, q[1..], ops, i + 1)
  }

  method bounded_queue(capacity: int, ops: seq<int>) returns (out: seq<int>)
    requires capacity >= 1
    requires forall j :: 0 <= j < |ops| ==> ops[j] >= 0
    ensures out == Outputs(capacity, [], ops, 0)
  {
    var q: seq<int> := [];
    out := [];
    var i := 0;
    while i < |ops|
      invariant 0 <= i <= |ops|
      invariant |q| <= capacity
      invariant out + Outputs(capacity, q, ops, i) == Outputs(capacity, [], ops, 0)
      decreases |ops| - i
    {
      if ops[i] > 0 {
        q := Push(capacity, q, ops[i]);
      } else if |q| == 0 {
        out := out + [-1];
      } else {
        out := out + [q[0]];
        q := q[1..];
      }
      i := i + 1;
    }
  }
}
