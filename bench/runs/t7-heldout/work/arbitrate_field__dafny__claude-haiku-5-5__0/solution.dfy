module Solution {

  // Candidate a (by index) is strictly preferred to candidate b (by index):
  // higher confidence wins; on equal confidence, smaller engine rank wins;
  // on equal confidence and rank, the earlier index wins.
  predicate Beats(cs: seq<(int, int, int)>, rank: seq<int>, a: int, b: int)
    requires 0 <= a < |cs| && 0 <= b < |cs|
    requires forall k :: 0 <= k < |cs| ==> 0 <= cs[k].0 < |rank|
  {
    cs[a].1 > cs[b].1 ||
    (cs[a].1 == cs[b].1 &&
      (rank[cs[a].0] < rank[cs[b].0] ||
       (rank[cs[a].0] == rank[cs[b].0] && a < b)))
  }

  lemma BeatsTrans(cs: seq<(int, int, int)>, rank: seq<int>, a: int, b: int, c: int)
    requires 0 <= a < |cs| && 0 <= b < |cs| && 0 <= c < |cs|
    requires forall k :: 0 <= k < |cs| ==> 0 <= cs[k].0 < |rank|
    requires Beats(cs, rank, a, b) && Beats(cs, rank, b, c)
    ensures Beats(cs, rank, a, c)
  {
  }

  method arbitrate_field(candidates: seq<(int, int, int)>, rank: seq<int>, threshold: int) returns (r: int)
    requires forall i :: 0 <= i < |candidates| ==> 0 <= candidates[i].0 < |rank|
    requires forall i :: 0 <= i < |candidates| ==> 0 <= candidates[i].1 <= 100
    requires 0 <= threshold <= 100
    ensures r == -1 || 0 <= r < |candidates|
    ensures r == -1 ==> forall i :: 0 <= i < |candidates| ==> candidates[i].1 < threshold
    ensures r != -1 ==> candidates[r].1 >= threshold
    ensures r != -1 ==> forall i :: 0 <= i < |candidates| && candidates[i].1 >= threshold && i != r ==> Beats(candidates, rank, r, i)
  {
    r := -1;
    var i := 0;
    while i < |candidates|
      invariant 0 <= i <= |candidates|
      invariant r == -1 ==> forall k :: 0 <= k < i ==> candidates[k].1 < threshold
      invariant r != -1 ==> 0 <= r < i && candidates[r].1 >= threshold
      invariant r != -1 ==> forall k :: 0 <= k < i && candidates[k].1 >= threshold && k != r ==> Beats(candidates, rank, r, k)
      decreases |candidates| - i
    {
      if candidates[i].1 >= threshold {
        if r == -1 {
          r := i;
        } else if Beats(candidates, rank, i, r) {
          // i beats old r, and old r beats every earlier eligible candidate,
          // so i beats them all by transitivity.
          forall k | 0 <= k < i && candidates[k].1 >= threshold
            ensures Beats(candidates, rank, i, k)
          {
            if k != r {
              BeatsTrans(candidates, rank, i, r, k);
            }
          }
          r := i;
        }
      }
      i := i + 1;
    }
  }
}
