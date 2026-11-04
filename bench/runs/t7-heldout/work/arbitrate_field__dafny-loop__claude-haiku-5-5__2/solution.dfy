module Solution {

  // Candidate c (at index i) is preferred over candidate d (at index j):
  // higher confidence wins; on equal confidence, smaller engine rank wins;
  // on equal confidence and rank, the earlier index wins.
  predicate Beats(c: (int, int, int), d: (int, int, int), rank: seq<int>, i: int, j: int)
    requires 0 <= c.0 < |rank| && 0 <= d.0 < |rank|
  {
    c.1 > d.1
    || (c.1 == d.1 && rank[c.0] < rank[d.0])
    || (c.1 == d.1 && rank[c.0] == rank[d.0] && i < j)
  }

  method arbitrate_field(candidates: seq<(int, int, int)>, rank: seq<int>, threshold: int) returns (r: int)
    requires forall i :: 0 <= i < |candidates| ==>
               0 <= candidates[i].0 < |rank| && 0 <= candidates[i].1 <= 100
    requires 0 <= threshold <= 100
    ensures r == -1 || 0 <= r < |candidates|
    ensures r == -1 ==> forall j :: 0 <= j < |candidates| ==> candidates[j].1 < threshold
    ensures r != -1 ==> candidates[r].1 >= threshold
    ensures r != -1 ==> forall j :: 0 <= j < |candidates| && candidates[j].1 >= threshold && j != r ==>
              Beats(candidates[r], candidates[j], rank, r, j)
  {
    r := -1;
    var i := 0;
    while i < |candidates|
      invariant 0 <= i <= |candidates|
      invariant r == -1 || 0 <= r < i
      invariant r == -1 ==> forall j :: 0 <= j < i ==> candidates[j].1 < threshold
      invariant r != -1 ==> candidates[r].1 >= threshold
      invariant r != -1 ==> forall j :: 0 <= j < i && candidates[j].1 >= threshold && j != r ==>
                  Beats(candidates[r], candidates[j], rank, r, j)
      decreases |candidates| - i
    {
      if candidates[i].1 >= threshold {
        if r == -1 || Beats(candidates[i], candidates[r], rank, i, r) {
          r := i;
        }
      }
      i := i + 1;
    }
  }
}
