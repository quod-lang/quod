module Solution {
  predicate InRange(n: int, o: seq<int>)
  {
    forall i :: 0 <= i < |o| ==> 0 <= o[i] < n
  }

  predicate Distinct(o: seq<int>)
  {
    forall i, j :: 0 <= i < j < |o| ==> o[i] != o[j]
  }

  // every edge (u, v) has u strictly before v (self-loops are never respected)
  predicate Respects(edges: seq<(int, int)>, o: seq<int>)
  {
    forall i, j :: 0 <= i <= j < |o| ==> (o[j], o[i]) !in edges
  }

  // o is an ordering of all n nodes that respects every edge
  predicate Valid(n: int, edges: seq<(int, int)>, o: seq<int>)
  {
    |o| == n && InRange(n, o) && Distinct(o) && Respects(edges, o)
  }

  predicate LexLeq(a: seq<int>, b: seq<int>)
  {
    a == b || exists k :: 0 <= k < |a| && k < |b| && a[..k] == b[..k] && a[k] < b[k]
  }

  predicate Pre(a: seq<int>, o: seq<int>)
  {
    (|a| <= |o| && a == o[..|a|]) ||
    exists k :: 0 <= k < |a| && k < |o| && a[..k] == o[..k] && a[k] < o[k]
  }

  predicate Avail(n: int, edges: seq<(int, int)>, order: seq<int>, x: int)
  {
    0 <= x < n && x !in order && forall e :: e in edges && e.1 == x ==> e.0 in order
  }

  lemma SubsetCard(A: set<int>, B: set<int>)
    requires A <= B
    ensures |A| <= |B|
    decreases |A|
  {
    if A != {} {
      var x :| x in A;
      SubsetCard(A - {x}, B - {x});
    }
  }

  lemma DistinctCard(s: seq<int>)
    requires Distinct(s)
    ensures |set x | x in s| == |s|
  {
    if |s| > 0 {
      var t := s[..|s| - 1];
      DistinctCard(t);
      assert (set x | x in s) == (set x | x in t) + {s[|s| - 1]};
      assert s[|s| - 1] !in t;
    }
  }

  lemma RangeCard(n: int)
    requires n >= 0
    ensures |set x | 0 <= x < n| == n
  {
    if n > 0 {
      RangeCard(n - 1);
      assert (set x | 0 <= x < n) == (set x | 0 <= x < n - 1) + {n - 1};
    }
  }

  lemma Surj(n: int, o: seq<int>)
    requires n >= 0 && |o| == n && InRange(n, o) && Distinct(o)
    ensures forall x :: 0 <= x < n ==> x in o
  {
    var S := set x | x in o;
    var R := set x | 0 <= x < n;
    DistinctCard(o);
    RangeCard(n);
    assert S <= R;
    forall x | 0 <= x < n
      ensures x in o
    {
      if x !in o {
        SubsetCard(S, R - {x});
        assert false;
      }
    }
  }

  lemma NoValid(n: int, edges: seq<(int, int)>, order: seq<int>, o: seq<int>)
    requires n >= 1
    requires forall e :: e in edges ==> 0 <= e.0 < n && 0 <= e.1 < n
    requires |order| < n && InRange(n, order) && Distinct(order)
    requires forall x :: 0 <= x < n ==> !Avail(n, edges, order, x)
    ensures !Valid(n, edges, o)
  {
    if Valid(n, edges, o) {
      Surj(n, o);
      var So := set x | x in o;
      var Sr := set x | x in order;
      DistinctCard(o);
      DistinctCard(order);
      if forall j :: 0 <= j < n ==> o[j] in order {
        assert So <= Sr;
        SubsetCard(So, Sr);
        assert false;
      }
      var m := 0;
      while o[m] in order
        invariant 0 <= m < n
        invariant exists j :: m <= j < n && o[j] !in order
        invariant forall j :: 0 <= j < m ==> o[j] in order
        decreases n - m
      {
        m := m + 1;
      }
      var y := o[m];
      forall e | e in edges && e.1 == y
        ensures e.0 in order
      {
        var u := e.0;
        assert u in o;
        var p :| 0 <= p < n && o[p] == u;
        if p >= m {
          assert (o[p], o[m]) in edges;
          assert false;
        }
      }
      assert Avail(n, edges, order, y);
      assert false;
    }
  }

  lemma Step(n: int, edges: seq<(int, int)>, order: seq<int>, c: int, o: seq<int>)
    requires n >= 1
    requires forall e :: e in edges ==> 0 <= e.0 < n && 0 <= e.1 < n
    requires |order| < n && InRange(n, order) && Distinct(order)
    requires Avail(n, edges, order, c)
    requires forall x :: 0 <= x < c ==> !Avail(n, edges, order, x)
    requires Valid(n, edges, o) && Pre(order, o)
    ensures Pre(order + [c], o)
  {
    var a := order + [c];
    if exists k :: 0 <= k < |order| && k < |o| && order[..k] == o[..k] && order[k] < o[k] {
      var k :| 0 <= k < |order| && k < |o| && order[..k] == o[..k] && order[k] < o[k];
      assert a[..k] == order[..k];
      assert a[k] == order[k];
    } else {
      var m := |order|;
      assert order == o[..m];
      Surj(n, o);
      var y := o[m];
      assert y !in order by {
        if y in order {
          var q :| 0 <= q < m && order[q] == y;
          assert o[q] == o[m];
        }
      }
      forall e | e in edges && e.1 == y
        ensures e.0 in order
      {
        var u := e.0;
        assert u in o;
        var p :| 0 <= p < n && o[p] == u;
        if p >= m {
          assert (o[p], o[m]) in edges;
          assert false;
        }
        assert o[p] in o[..m];
      }
      assert Avail(n, edges, order, y);
      assert c <= y;
      if c < y {
        assert a[..m] == o[..m];
      } else {
        assert a == o[..m + 1];
      }
    }
  }

  method ComputeBlocked(n: int, edges: seq<(int, int)>, order: seq<int>, placed: seq<bool>)
    returns (blocked: seq<bool>)
    requires forall e :: e in edges ==> 0 <= e.0 < n && 0 <= e.1 < n
    requires |placed| == n
    requires forall x :: 0 <= x < n ==> (placed[x] <==> x in order)
    ensures |blocked| == n
    ensures forall x :: 0 <= x < n ==> (Avail(n, edges, order, x) <==> !placed[x] && !blocked[x])
  {
    blocked := seq(n, _ => false);
    var i := 0;
    while i < |edges|
      invariant 0 <= i <= |edges|
      invariant |blocked| == n
      invariant forall v :: 0 <= v < n ==>
        (blocked[v] <==> exists j :: 0 <= j < i && edges[j].1 == v && !placed[edges[j].0])
    {
      assert edges[i] in edges;
      var (u, v) := edges[i];
      if !placed[u] {
        blocked := blocked[v := true];
      }
      i := i + 1;
    }
    forall x | 0 <= x < n
      ensures Avail(n, edges, order, x) <==> !placed[x] && !blocked[x]
    {
      if blocked[x] {
        var j :| 0 <= j < |edges| && edges[j].1 == x && !placed[edges[j].0];
        assert edges[j] in edges;
      }
      if !Avail(n, edges, order, x) && !placed[x] {
        var e :| e in edges && e.1 == x && e.0 !in order;
        var j :| 0 <= j < |edges| && edges[j] == e;
      }
    }
  }

  predicate Closed(edges: seq<(int, int)>, order: seq<int>)
  {
    forall i :: 0 <= i < |order| ==>
      forall e :: e in edges && e.1 == order[i] ==> e.0 in order[..i]
  }

  lemma ClosedStep(n: int, edges: seq<(int, int)>, order: seq<int>, c: int)
    requires Closed(edges, order) && Avail(n, edges, order, c)
    ensures Closed(edges, order + [c])
  {
    var a := order + [c];
    forall i | 0 <= i < |a|
      ensures forall e :: e in edges && e.1 == a[i] ==> e.0 in a[..i]
    {
      if i < |order| {
        assert a[..i] == order[..i];
      } else {
        assert a[..i] == order;
      }
    }
  }

  lemma Final(n: int, edges: seq<(int, int)>, order: seq<int>)
    requires |order| == n && InRange(n, order) && Distinct(order) && Closed(edges, order)
    requires forall o :: Valid(n, edges, o) ==> Pre(order, o)
    ensures Valid(n, edges, order)
    ensures forall o :: Valid(n, edges, o) ==> LexLeq(order, o)
  {
    forall i, j | 0 <= i <= j < |order|
      ensures (order[j], order[i]) !in edges
    {
      if (order[j], order[i]) in edges {
        assert order[j] in order[..i];
        var q :| 0 <= q < i && order[q] == order[j];
      }
    }
    forall o | Valid(n, edges, o)
      ensures LexLeq(order, o)
    {
      assert Pre(order, o);
      assert o[..|o|] == o;
    }
  }

  method topo_sort(n: int, edges: seq<(int, int)>) returns (order: seq<int>)
    requires n >= 1
    requires forall e :: e in edges ==> 0 <= e.0 < n && 0 <= e.1 < n
    ensures order == [] ==> forall o :: !Valid(n, edges, o)
    ensures order != [] ==> Valid(n, edges, order)
    ensures order != [] ==> forall o :: Valid(n, edges, o) ==> LexLeq(order, o)
  {
    order := [];
    var placed := seq(n, _ => false);
    while |order| < n
      invariant |order| <= n && InRange(n, order) && Distinct(order)
      invariant |placed| == n
      invariant forall x :: 0 <= x < n ==> (placed[x] <==> x in order)
      invariant Closed(edges, order)
      invariant forall o :: Valid(n, edges, o) ==> Pre(order, o)
      decreases n - |order|
    {
      var blocked := ComputeBlocked(n, edges, order, placed);
      var c := 0;
      while c < n && (placed[c] || blocked[c])
        invariant 0 <= c <= n
        invariant forall x :: 0 <= x < c ==> !Avail(n, edges, order, x)
      {
        c := c + 1;
      }
      if c == n {
        forall o
          ensures !Valid(n, edges, o)
        {
          NoValid(n, edges, order, o);
        }
        return [];
      }
      forall o | Valid(n, edges, o)
        ensures Pre(order + [c], o)
      {
        Step(n, edges, order, c, o);
      }
      ClosedStep(n, edges, order, c);
      order := order + [c];
      placed := placed[c := true];
    }
    Final(n, edges, order);
  }
}
