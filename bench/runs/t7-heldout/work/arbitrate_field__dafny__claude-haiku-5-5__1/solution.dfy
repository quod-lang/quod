module Solution {

  // Key ordering: a candidate with confidence c1 and engine rank k1 strictly
  // beats one with confidence c2 and engine rank k2 when its confidence is
  // higher, or the confidences are equal and its engine is more trusted.
  predicate Beats(c1: int, k1: int, c2: int, k2: int) {
    c1 > c2 || (c1 == c2 && k1 < k2)
  }

  method arbitrate_field(candidates: seq<(int, int, int)>, rank: seq<int>, threshold: int) returns (r: int)
    requires forall i :: 0 <= i < |candidates| ==> 0 <= candidates[i].0 < |rank|
    requires forall i :: 0 <= i < |candidates| ==> 0 <= candidates[i].1 <= 100
    requires 0 <= threshold <= 100
    ensures -1 <= r < |candidates|
    ensures r == -1 ==> forall i :: 0 <= i < |candidates| ==> candidates[i].1 < threshold
    ensures r != -1 ==>
      candidates[r].1 >= threshold &&
      forall i :: 0 <= i < |candidates| && candidates[i].1 >= threshold ==>
        (Beats(candidates[r].1, rank[candidates[r].0], candidates[i].1, rank[candidates[i].0])
         || (!Beats(candidates[i].1, rank[candidates[i].0], candidates[r].1, rank[candidates[r].0])
             && i >= r))
  {
    r := -1;
    var i := 0;
    while i < |candidates|
      invariant 0 <= i <= |candidates|
      invariant -1 <= r < i
      invariant r == -1 ==> forall j :: 0 <= j < i ==> candidates[j].1 < threshold
      invariant r != -1 ==>
        candidates[r].1 >= threshold &&
        forall j :: 0 <= j < i && candidates[j].1 >= threshold ==>
          (Beats(candidates[r].1, rank[candidates[r].0], candidates[j].1, rank[candidates[j].0])
           || (!Beats(candidates[j].1, rank[candidates[j].0], candidates[r].1, rank[candidates[r].0])
               && j >= r))
      decreases |candidates| - i
    {
      if candidates[i].1 >= threshold {
        if r == -1 || Beats(candidates[i].1, rank[candidates[i].0], candidates[r].1, rank[candidates[r].0]) {
          r := i;
        }
      }
      i := i + 1;
    }
  }
}
