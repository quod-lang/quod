module Solution {

  // Candidate i is ranked strictly above candidate j in the selection order:
  // higher confidence first, then smaller engine rank. Equal on both: the earlier index wins.
  predicate Above(candidates: seq<(int, int, int)>, rank: seq<int>, i: int, j: int)
    requires 0 <= i < |candidates| && 0 <= j < |candidates|
    requires 0 <= candidates[i].0 < |rank| && 0 <= candidates[j].0 < |rank|
  {
    candidates[i].1 > candidates[j].1 ||
    (candidates[i].1 == candidates[j].1 && rank[candidates[i].0] < rank[candidates[j].0])
  }

  method arbitrate_field(candidates: seq<(int, int, int)>, rank: seq<int>, threshold: int) returns (r: int)
    requires 0 <= threshold <= 100
    requires forall i :: 0 <= i < |candidates| ==> 0 <= candidates[i].0 < |rank|
    requires forall i :: 0 <= i < |candidates| ==> 0 <= candidates[i].1 <= 100
    ensures r == -1 || 0 <= r < |candidates|
    // No candidate reaches the threshold: manual validation.
    ensures r == -1 ==> forall i :: 0 <= i < |candidates| ==> candidates[i].1 < threshold
    // Otherwise the result is eligible and beats every other eligible candidate
    // (highest confidence, then smallest engine rank, then first index).
    ensures r != -1 ==> candidates[r].1 >= threshold
    ensures r != -1 ==> forall i :: 0 <= i < |candidates| && candidates[i].1 >= threshold ==>
      candidates[i].1 < candidates[r].1 ||
      (candidates[i].1 == candidates[r].1 && rank[candidates[i].0] > rank[candidates[r].0]) ||
      (candidates[i].1 == candidates[r].1 && rank[candidates[i].0] == rank[candidates[r].0] && i >= r)
  {
    r := -1;
    var i := 0;
    while i < |candidates|
      invariant 0 <= i <= |candidates|
      invariant r == -1 || (0 <= r < i && candidates[r].1 >= threshold)
      invariant r == -1 ==> forall j :: 0 <= j < i ==> candidates[j].1 < threshold
      invariant r != -1 ==> forall j :: 0 <= j < i && candidates[j].1 >= threshold ==>
        candidates[j].1 < candidates[r].1 ||
        (candidates[j].1 == candidates[r].1 && rank[candidates[j].0] > rank[candidates[r].0]) ||
        (candidates[j].1 == candidates[r].1 && rank[candidates[j].0] == rank[candidates[r].0] && j >= r)
      decreases |candidates| - i
    {
      if candidates[i].1 >= threshold && (r == -1 || Above(candidates, rank, i, r)) {
        r := i;
      }
      i := i + 1;
    }
  }
}
