predicate ValidIv(s: seq<(int, int)>) { forall k :: 0 <= k < |s| ==> s[k].0 <= s[k].1 }
predicate SortedByStart(s: seq<(int, int)>) { forall k :: 0 <= k < |s| - 1 ==> s[k].0 <= s[k + 1].0 }
predicate Disjoint(r: seq<(int, int)>) { forall k :: 0 <= k < |r| - 1 ==> r[k].1 < r[k + 1].0 }
predicate Cov(s: seq<(int, int)>, x: int) { exists k :: 0 <= k < |s| && s[k].0 <= x <= s[k].1 }
lemma Both(x: int)
  ensures Cov([(1,2),(3,4)], x) <==> Cov([(1,4)], x)
{
  if 1 <= x <= 4 {
    if x <= 2 { assert (1,2) == [(1,2),(3,4)][0]; } else { assert (3,4) == [(1,2),(3,4)][1]; }
    assert [(1,4)][0].0 <= x <= [(1,4)][0].1;
  }
}
lemma Witness()
  ensures SortedByStart([(1,2),(3,4)]) && Disjoint([(1,2),(3,4)]) && ValidIv([(1,2),(3,4)])
  ensures SortedByStart([(1,4)]) && Disjoint([(1,4)]) && ValidIv([(1,4)])
  ensures forall x :: Cov([(1,2),(3,4)], x) <==> Cov([(1,4)], x)
{ forall x ensures Cov([(1,2),(3,4)], x) <==> Cov([(1,4)], x) { Both(x); } }
