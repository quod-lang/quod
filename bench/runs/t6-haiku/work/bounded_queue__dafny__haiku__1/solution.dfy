module Solution {
  // Specification function: outputs produced by running the operations `ops`
  // against a queue whose current contents are `q` (front at index 0),
  // with capacity `cap`.
  //  - push x (x > 0): if full, drop the oldest element first, then append x.
  //  - pop (0): output the oldest element, or -1 if the queue is empty.
  function Run(cap: int, q: seq<int>, ops: seq<int>): seq<int>
    requires cap >= 1
    decreases |ops|
  {
    if ops == [] then []
    else
      var x := ops[0];
      if x > 0 then
        if |q| == cap then
          Run(cap, q[1..] + [x], ops[1..])
        else
          Run(cap, q + [x], ops[1..])
      else
        if |q| == 0 then
          [-1] + Run(cap, q, ops[1..])
        else
          [q[0]] + Run(cap, q[1..], ops[1..])
  }

  method bounded_queue(capacity: int, ops: seq<int>) returns (out: seq<int>)
    requires capacity >= 1
    requires forall i :: 0 <= i < |ops| ==> ops[i] >= 0
    ensures out == Run(capacity, [], ops)
  {
    out := [];
    var q: seq<int> := [];
    var i := 0;
    while i < |ops|
      invariant 0 <= i <= |ops|
      invariant out + Run(capacity, q, ops[i..]) == Run(capacity, [], ops)
      decreases |ops| - i
    {
      var x := ops[i];
      assert ops[i..] == [x] + ops[i+1..];
      if x > 0 {
        if |q| == capacity {
          q := q[1..] + [x];
        } else {
          q := q + [x];
        }
      } else {
        if |q| == 0 {
          out := out + [-1];
        } else {
          out := out + [q[0]];
          q := q[1..];
        }
      }
      i := i + 1;
    }
  }
}
