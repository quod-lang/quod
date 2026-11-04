module Solution {

  // a is at least as good as b: higher confidence wins; on equal confidence,
  // smaller engine rank wins; on equal confidence and rank, smaller index wins.
  predicate AtLeastAsGood(candidates: seq<(int, int, int)>, rank: seq<int>, a: int, b: int)
    requires 0 <= a < |candidates| && 0 <= b < |candidates|
    requires forall k :: 0 <= k < |candidates| ==> 0 <= candidates[k].0 < |rank|
  {
    candidates[a].1 > candidates[b].1 ||
    (candidates[a].1 == candidates[b].1 && rank[candidates[a].0] < rank[candidates[b].0]) ||
    (candidates[a].1 == candidates[b].1 && rank[candidates[a].0] == rank[candidates[b].0] && a <= b)
  }

  method arbitrate_field(candidates: seq<(int, int, int)>, rank: seq<int>, threshold: int) returns (r: int)
    requires forall i :: 0 <= i < |candidates| ==> 0 <= candidates[i].0 < |rank| && 0 <= candidates[i].1 <= 100
    requires 0 <= threshold <= 100
    ensures r == -1 || 0 <= r < |candidates|
    ensures r != -1 ==> candidates[r].1 >= threshold
    ensures forall j :: 0 <= j < |candidates| && candidates[j].1 >= threshold ==>
              r != -1 && AtLeastAsGood(candidates, rank, r, j)
  {
    r := -1;
    var i := 0;
    while i < |candidates|
      invariant 0 <= i <= |candidates|
      invariant r == -1 || (0 <= r < i && candidates[r].1 >= threshold)
      invariant r == -1 ==> forall j :: 0 <= j < i ==> candidates[j].1 < threshold
      invariant forall j :: 0 <= j < i && candidates[j].1 >= threshold ==>
                  r != -1 && AtLeastAsGood(candidates, rank, r, j)
    {
      if candidates[i].1 >= threshold {
        if r == -1 {
          r := i;
        } else if candidates[i].1 > candidates[r].1 ||
                  (candidates[i].1 == candidates[r].1 && rank[candidates[i].0] < rank[candidates[r].0]) {
          r := i;
        }
      }
      i := i + 1;
    }
  }
}
