module Solution {

  // candidate i is eligible when its confidence reaches the threshold
  predicate Eligible(candidates: seq<(int, int, int)>, threshold: int, i: int)
    requires 0 <= i < |candidates|
  {
    candidates[i].1 >= threshold
  }

  // candidate a is at least as good as candidate b:
  // higher confidence, or equal confidence and smaller engine rank,
  // or equal confidence and equal rank and a is not after b.
  predicate AtLeastAsGood(candidates: seq<(int, int, int)>, rank: seq<int>, a: int, b: int)
    requires 0 <= a < |candidates| && 0 <= b < |candidates|
    requires 0 <= candidates[a].0 < |rank| && 0 <= candidates[b].0 < |rank|
  {
    candidates[a].1 > candidates[b].1 ||
    (candidates[a].1 == candidates[b].1 && rank[candidates[a].0] < rank[candidates[b].0]) ||
    (candidates[a].1 == candidates[b].1 && rank[candidates[a].0] == rank[candidates[b].0] && a <= b)
  }

  // transitivity of AtLeastAsGood (lexicographic order on (-confidence, rank, index))
  lemma AtLeastAsGoodTrans(candidates: seq<(int, int, int)>, rank: seq<int>, a: int, b: int, c: int)
    requires 0 <= a < |candidates| && 0 <= b < |candidates| && 0 <= c < |candidates|
    requires forall x :: 0 <= x < |candidates| ==> 0 <= candidates[x].0 < |rank|
    requires AtLeastAsGood(candidates, rank, a, b)
    requires AtLeastAsGood(candidates, rank, b, c)
    ensures AtLeastAsGood(candidates, rank, a, c)
  {
  }

  method arbitrate_field(candidates: seq<(int, int, int)>, rank: seq<int>, threshold: int) returns (r: int)
    requires 0 <= threshold <= 100
    requires forall i :: 0 <= i < |candidates| ==> 0 <= candidates[i].1 <= 100
    requires forall i :: 0 <= i < |candidates| ==> 0 <= candidates[i].0 < |rank|
    ensures -1 <= r < |candidates|
    ensures r == -1 ==> forall k :: 0 <= k < |candidates| ==> candidates[k].1 < threshold
    ensures r >= 0 ==> Eligible(candidates, threshold, r)
    ensures r >= 0 ==> forall k :: 0 <= k < |candidates| && Eligible(candidates, threshold, k) ==>
              AtLeastAsGood(candidates, rank, r, k)
  {
    var best := -1;
    var i := 0;
    while i < |candidates|
      invariant 0 <= i <= |candidates|
      invariant -1 <= best < i
      invariant best >= 0 ==> Eligible(candidates, threshold, best)
      invariant best >= 0 ==> forall k :: 0 <= k < i && Eligible(candidates, threshold, k) ==>
                  AtLeastAsGood(candidates, rank, best, k)
      invariant best == -1 ==> forall k :: 0 <= k < i ==> candidates[k].1 < threshold
      decreases |candidates| - i
    {
      if candidates[i].1 >= threshold && (best == -1 || AtLeastAsGood(candidates, rank, i, best)) {
        forall k | 0 <= k < i && Eligible(candidates, threshold, k) && best >= 0
          ensures AtLeastAsGood(candidates, rank, i, k)
        {
          AtLeastAsGoodTrans(candidates, rank, i, best, k);
        }
        best := i;
      }
      i := i + 1;
    }
    r := best;
  }
}
