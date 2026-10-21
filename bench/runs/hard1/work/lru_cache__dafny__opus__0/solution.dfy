module Solution {
  // Cache is ordered from least recently used (front) to most recently used (back).
  function Contains(c: seq<(int, int)>, k: int): bool
  {
    if |c| == 0 then false else c[0].0 == k || Contains(c[1..], k)
  }

  function Lookup(c: seq<(int, int)>, k: int): int
  {
    if |c| == 0 then -1 else if c[0].0 == k then c[0].1 else Lookup(c[1..], k)
  }

  function Remove(c: seq<(int, int)>, k: int): seq<(int, int)>
  {
    if |c| == 0 then [] else if c[0].0 == k then Remove(c[1..], k) else [c[0]] + Remove(c[1..], k)
  }

  function Step(capacity: int, c: seq<(int, int)>, op: (int, int, int)): (seq<(int, int)>, seq<int>)
    requires capacity >= 1
  {
    var (kind, key, value) := op;
    if kind == 0 then
      if Contains(c, key) then (Remove(c, key) + [(key, Lookup(c, key))], [Lookup(c, key)])
      else (c, [-1])
    else if kind == 1 then
      if Contains(c, key) then (Remove(c, key) + [(key, value)], [])
      else if |c| >= capacity then (c[1..] + [(key, value)], [])
      else (c + [(key, value)], [])
    else (c, [])
  }

  function Run(capacity: int, ops: seq<(int, int, int)>): (seq<(int, int)>, seq<int>)
    requires capacity >= 1
  {
    if |ops| == 0 then ([], [])
    else
      var prev := Run(capacity, ops[..|ops| - 1]);
      var nxt := Step(capacity, prev.0, ops[|ops| - 1]);
      (nxt.0, prev.1 + nxt.1)
  }

  method lru_cache(capacity: int, ops: seq<(int, int, int)>) returns (out: seq<int>)
    requires capacity >= 1
    requires forall i :: 0 <= i < |ops| ==> (ops[i].0 == 0 || ops[i].0 == 1)
    requires forall i :: 0 <= i < |ops| && ops[i].0 == 1 ==> ops[i].2 >= 0
    ensures out == Run(capacity, ops).1
  {
    var cache: seq<(int, int)> := [];
    out := [];
    var i := 0;
    while i < |ops|
      invariant 0 <= i <= |ops|
      invariant (cache, out) == Run(capacity, ops[..i])
    {
      assert ops[..i + 1][..i] == ops[..i];
      var s := Step(capacity, cache, ops[i]);
      cache := s.0;
      out := out + s.1;
      i := i + 1;
    }
    assert ops[..|ops|] == ops;
  }
}
