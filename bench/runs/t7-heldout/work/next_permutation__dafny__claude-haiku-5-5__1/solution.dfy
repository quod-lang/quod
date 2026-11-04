module Solution {

  // ---------------------------------------------------------------
  // Specification helpers
  // ---------------------------------------------------------------

  // Lexicographic "strictly less than" on integer sequences.
  // A proper prefix is smaller than the longer sequence.
  ghost function LexLt(a: seq<int>, b: seq<int>): bool
    decreases |a|
  {
    if |a| == 0 then |b| > 0
    else if |b| == 0 then false
    else if a[0] < b[0] then true
    else if a[0] > b[0] then false
    else LexLt(a[1..], b[1..])
  }

  ghost predicate NonDecr(s: seq<int>)
  {
    forall a, b :: 0 <= a < b < |s| ==> s[a] <= s[b]
  }

  ghost predicate NonIncr(s: seq<int>)
  {
    forall a, b :: 0 <= a < b < |s| ==> s[a] >= s[b]
  }

  function RevSeq(s: seq<int>): seq<int>
    decreases |s|
  {
    if |s| == 0 then [] else RevSeq(s[1..]) + [s[0]]
  }

  // The successor arrangement, given the pivot i and the rightmost j with xs[j] > xs[i].
  ghost function Res(xs: seq<int>, i: int, j: int): seq<int>
    requires 0 <= i < j < |xs|
  {
    xs[..i] + [xs[j]] + RevSeq(xs[i+1..j] + [xs[i]] + xs[j+1..])
  }

  // ---------------------------------------------------------------
  // Multiset helpers
  // ---------------------------------------------------------------

  lemma MSCard(s: seq<int>)
    ensures |multiset(s)| == |s|
    decreases |s|
  {
    if |s| > 0 {
      MSCard(s[1..]);
      assert s == [s[0]] + s[1..];
    }
  }

  lemma MSAppend(a: seq<int>, b: seq<int>)
    ensures multiset(a + b) == multiset(a) + multiset(b)
    decreases |a|
  {
    if |a| > 0 {
      MSAppend(a[1..], b);
      assert a + b == [a[0]] + (a[1..] + b);
      assert a == [a[0]] + a[1..];
    }
  }

  lemma MSComm(A: multiset<int>, B: multiset<int>)
    ensures A + B == B + A
  {
  }

  lemma MSHead(s: seq<int>)
    requires |s| > 0
    ensures multiset(s) == multiset([s[0]]) + multiset(s[1..])
  {
    assert s == [s[0]] + s[1..];
    MSAppend([s[0]], s[1..]);
  }

  // Cancel a common multiset summand.
  lemma MSCancel(A: seq<int>, P: seq<int>, X: seq<int>)
    requires multiset(A) + multiset(P) == multiset(A) + multiset(X)
    ensures multiset(P) == multiset(X)
  {
    assert multiset(P) == (multiset(A) + multiset(P)) - multiset(A);
    assert multiset(X) == (multiset(A) + multiset(X)) - multiset(A);
  }

  // Cancel a common head element.
  lemma MSCancelHead(a: seq<int>, b: seq<int>)
    requires |a| > 0 && |b| > 0
    requires a[0] == b[0]
    requires multiset(a) == multiset(b)
    ensures multiset(a[1..]) == multiset(b[1..])
  {
    MSHead(a);
    MSHead(b);
    MSCancel([a[0]], a[1..], b[1..]);
  }

  // Moving the head x0 of [x0] + M + [y] + T to the front of [y] + (M + [x0] + T).
  lemma MSRot(x0: int, M: seq<int>, y: int, T: seq<int>)
    ensures multiset([x0] + M + [y] + T) == multiset([y]) + multiset(M + [x0] + T)
  {
    MSAppend([x0] + M + [y], T);
    MSAppend([x0] + M, [y]);
    MSAppend([x0], M);
    MSAppend(M + [x0], T);
    MSAppend(M, [x0]);
    MSComm(multiset([x0]), multiset(M));
  }

  // ---------------------------------------------------------------
  // Lexicographic order lemmas
  // ---------------------------------------------------------------

  lemma LexAsym(a: seq<int>, b: seq<int>)
    requires LexLt(a, b)
    ensures !LexLt(b, a)
    decreases |a|
  {
    if |a| > 0 && |b| > 0 && a[0] == b[0] {
      LexAsym(a[1..], b[1..]);
    }
  }

  // A witness of a first difference gives the order.
  lemma LexIntro(a: seq<int>, b: seq<int>, k: int)
    requires |a| == |b|
    requires 0 <= k < |a|
    requires a[..k] == b[..k]
    requires a[k] < b[k]
    ensures LexLt(a, b)
    decreases k
  {
    if k > 0 {
      assert a[0] == b[0];
      assert a[1..][..k-1] == b[1..][..k-1];
      LexIntro(a[1..], b[1..], k-1);
    }
  }

  // Every strict order comes from a first difference.
  lemma LexDecomp(a: seq<int>, b: seq<int>) returns (k: int)
    requires |a| == |b|
    requires LexLt(a, b)
    ensures 0 <= k < |a|
    ensures a[..k] == b[..k]
    ensures a[k] < b[k]
    decreases |a|
  {
    assert |a| > 0;
    if a[0] < b[0] {
      k := 0;
    } else {
      assert a[0] == b[0];
      var k2 := LexDecomp(a[1..], b[1..]);
      k := k2 + 1;
      assert a[..k] == b[..k];
    }
  }

  // Common prefix can be removed.
  lemma LexPrefix(A: seq<int>, u: seq<int>, v: seq<int>)
    ensures LexLt(A + u, A + v) == LexLt(u, v)
    decreases |A|
  {
    if |A| > 0 {
      assert (A + u)[0] == A[0] && (A + v)[0] == A[0];
      assert (A + u)[1..] == A[1..] + u;
      assert (A + v)[1..] == A[1..] + v;
      LexPrefix(A[1..], u, v);
    } else {
      assert A + u == u && A + v == v;
    }
  }

  // ---------------------------------------------------------------
  // Monotone sequence lemmas
  // ---------------------------------------------------------------

  lemma TailNonIncr(s: seq<int>)
    requires |s| > 0
    requires NonIncr(s)
    ensures NonIncr(s[1..])
  {
    forall a, b | 0 <= a < b < |s[1..]|
      ensures s[1..][a] >= s[1..][b]
    {
      assert s[1..][a] == s[a+1];
      assert s[1..][b] == s[b+1];
    }
  }

  lemma SliceNonIncr(s: seq<int>, lo: int)
    requires 0 <= lo <= |s|
    requires forall a, b :: lo <= a < b < |s| ==> s[a] >= s[b]
    ensures NonIncr(s[lo..])
  {
    forall a, b | 0 <= a < b < |s[lo..]|
      ensures s[lo..][a] >= s[lo..][b]
    {
      assert s[lo..][a] == s[lo + a];
      assert s[lo..][b] == s[lo + b];
    }
  }

  // Splitting a non-increasing concatenation.
  lemma SplitNonIncr(A: seq<int>, B: seq<int>)
    requires NonIncr(A + B)
    ensures NonIncr(A) && NonIncr(B)
    ensures forall ia, ib :: 0 <= ia < |A| && 0 <= ib < |B| ==> A[ia] >= B[ib]
  {
    forall a, b | 0 <= a < b < |A|
      ensures A[a] >= A[b]
    {
      assert (A + B)[a] == A[a];
      assert (A + B)[b] == A[b];
    }
    forall a, b | 0 <= a < b < |B|
      ensures B[a] >= B[b]
    {
      assert (A + B)[|A| + a] == B[a];
      assert (A + B)[|A| + b] == B[b];
    }
    forall ia, ib | 0 <= ia < |A| && 0 <= ib < |B|
      ensures A[ia] >= B[ib]
    {
      assert (A + B)[ia] == A[ia];
      assert (A + B)[|A| + ib] == B[ib];
    }
  }

  lemma JoinNonIncr(A: seq<int>, B: seq<int>)
    requires NonIncr(A) && NonIncr(B)
    requires forall ia, ib :: 0 <= ia < |A| && 0 <= ib < |B| ==> A[ia] >= B[ib]
    ensures NonIncr(A + B)
  {
    forall x, y | 0 <= x < y < |A| + |B|
      ensures (A + B)[x] >= (A + B)[y]
    {
      if y < |A| {
        assert (A + B)[x] == A[x] && (A + B)[y] == A[y];
      } else if x >= |A| {
        assert (A + B)[x] == B[x - |A|] && (A + B)[y] == B[y - |A|];
      } else {
        assert (A + B)[x] == A[x];
        assert (A + B)[y] == B[y - |A|];
      }
    }
  }

  lemma RevProps(s: seq<int>)
    ensures |RevSeq(s)| == |s|
    ensures multiset(RevSeq(s)) == multiset(s)
    ensures forall k :: 0 <= k < |s| ==> RevSeq(s)[k] == s[|s| - 1 - k]
    decreases |s|
  {
    if |s| > 0 {
      RevProps(s[1..]);
      assert RevSeq(s) == RevSeq(s[1..]) + [s[0]];
      MSHead(s);
      MSAppend(RevSeq(s[1..]), [s[0]]);
      forall k | 0 <= k < |s|
        ensures RevSeq(s)[k] == s[|s| - 1 - k]
      {
        if k < |s| - 1 {
          assert RevSeq(s)[k] == RevSeq(s[1..])[k];
        }
      }
    }
  }

  // Reversing a non-increasing sequence gives a non-decreasing one.
  lemma RevNonDecr(s: seq<int>)
    requires NonIncr(s)
    ensures NonDecr(RevSeq(s))
  {
    RevProps(s);
    forall a, b | 0 <= a < b < |s|
      ensures RevSeq(s)[a] <= RevSeq(s)[b]
    {
      assert RevSeq(s)[a] == s[|s| - 1 - a];
      assert RevSeq(s)[b] == s[|s| - 1 - b];
    }
  }

  // A non-decreasing sequence is lexicographically minimal among its rearrangements.
  lemma NonDecrMin(s: seq<int>, q: seq<int>)
    requires NonDecr(s)
    requires multiset(q) == multiset(s)
    ensures !LexLt(q, s)
    decreases |s|
  {
    if |s| > 0 {
      MSCard(q);
      MSCard(s);
      assert q[0] in multiset(q);
      assert q[0] in multiset(s);
      var k :| 0 <= k < |s| && s[k] == q[0];
      assert s[0] <= s[k];
      if s[0] < q[0] {
        // LexLt(q, s) is false since q[0] > s[0]
      } else {
        assert s[0] == q[0];
        MSCancelHead(q, s);
        assert NonDecr(s[1..]);
        NonDecrMin(s[1..], q[1..]);
      }
    }
  }

  // A non-increasing sequence is lexicographically maximal among its rearrangements.
  lemma NonIncrMax(s: seq<int>, q: seq<int>)
    requires NonIncr(s)
    requires multiset(q) == multiset(s)
    ensures !LexLt(s, q)
    decreases |s|
  {
    if |s| > 0 {
      MSCard(q);
      MSCard(s);
      assert q[0] in multiset(q);
      assert q[0] in multiset(s);
      var k :| 0 <= k < |s| && s[k] == q[0];
      assert s[0] >= s[k];
      if s[0] > q[0] {
        // LexLt(s, q) is false since s[0] > q[0]
      } else {
        assert s[0] == q[0];
        MSCancelHead(q, s);
        TailNonIncr(s);
        NonIncrMax(s[1..], q[1..]);
      }
    }
  }

  // ---------------------------------------------------------------
  // Key lemma: the suffix case.
  // Pivot x0 at the front, then M, then the rightmost larger element y, then T (all <= x0).
  // ---------------------------------------------------------------

  lemma Top(x0: int, M: seq<int>, y: int, T: seq<int>, P: seq<int>)
    requires x0 < y
    requires NonIncr(M + [y] + T)
    requires forall q :: 0 <= q < |T| ==> T[q] <= x0
    requires multiset(P) == multiset([x0] + M + [y] + T)
    requires LexLt([x0] + M + [y] + T, P)
    ensures !LexLt(P, [y] + RevSeq(M + [x0] + T))
  {
    var Y := M + [y] + T;
    var X := [x0] + Y;
    var Z := M + [x0] + T;
    assert X == [x0] + M + [y] + T;
    assert Y == M + ([y] + T);
    assert Z == M + ([x0] + T);
    assert X[1..] == Y;
    assert |P| > 0;

    // Non-increasing structure of Y = M + ([y] + T)
    SplitNonIncr(M, [y] + T);
    SplitNonIncr([y], T);
    JoinNonIncr([x0], T);
    // every element of M is >= y
    forall ia | 0 <= ia < |M|
      ensures M[ia] >= y
    {
      assert ([y] + T)[0] == y;
    }
    // M is >= everything in [x0] + T
    forall ia, ib | 0 <= ia < |M| && 0 <= ib < |[x0] + T|
      ensures M[ia] >= ([x0] + T)[ib]
    {
      if ib == 0 {
        assert ([x0] + T)[0] == x0;
      } else {
        assert ([x0] + T)[ib] == T[ib - 1];
      }
    }
    JoinNonIncr(M, [x0] + T);
    assert Z == M + ([x0] + T);
    assert NonIncr(Z);

    RevProps(Z);
    RevNonDecr(Z);

    if P[0] < x0 {
      // LexLt(X, P) would be false since X[0] = x0 > P[0]
    } else if P[0] == x0 {
      // LexLt(X, P) reduces to LexLt(Y, P[1..]), but Y is non-increasing.
      MSCancelHead(X, P);
      assert multiset(P[1..]) == multiset(X[1..]);
      assert multiset(P[1..]) == multiset(Y);
      NonIncrMax(Y, P[1..]);
    } else {
      // P[0] > x0 and P[0] occurs in X, not at index 0, so it occurs in Y.
      assert P[0] in multiset(P);
      assert P[0] in X;
      var q :| 0 <= q < |X| && X[q] == P[0];
      assert q > 0;
      assert Y[q - 1] == P[0];
      if q - 1 < |M| {
        assert M[q - 1] == P[0];
        assert P[0] >= y;
      } else if q - 1 == |M| {
        assert P[0] == y;
      } else {
        assert T[q - 1 - |M| - 1] == P[0];
        assert P[0] <= x0;
      }
      // Hence P[0] >= y
      assert P[0] >= y;
      if P[0] > y {
        // P[0] > y = R[0], so LexLt(P, R) is false
      } else {
        assert P[0] == y;
        MSHead(P);
        MSRot(x0, M, y, T);
        assert multiset([y]) + multiset(P[1..]) == multiset([y]) + multiset(Z);
        MSCancel([y], P[1..], Z);
        assert multiset(P[1..]) == multiset(RevSeq(Z));
        NonDecrMin(RevSeq(Z), P[1..]);
        assert ([y] + RevSeq(Z))[1..] == RevSeq(Z);
      }
    }
  }

  // ---------------------------------------------------------------
  // Slicing facts
  // ---------------------------------------------------------------

  lemma Decomp(xs: seq<int>, i: int, j: int)
    requires 0 <= i < j < |xs|
    ensures xs == xs[..i] + [xs[i]] + xs[i+1..j] + [xs[j]] + xs[j+1..]
    ensures xs[i..] == [xs[i]] + xs[i+1..j] + [xs[j]] + xs[j+1..]
    ensures xs[i+1..] == xs[i+1..j] + [xs[j]] + xs[j+1..]
  {
    assert xs[j..] == [xs[j]] + xs[j+1..];
    assert xs[i+1..] == xs[i+1..j] + xs[j..];
    assert xs[i..] == [xs[i]] + xs[i+1..];
    assert xs == xs[..i] + xs[i..];
  }

  // ---------------------------------------------------------------
  // Minimality of the successor
  // ---------------------------------------------------------------

  lemma Minimal(xs: seq<int>, p: seq<int>, i: int, j: int)
    requires 0 <= i < j < |xs|
    requires xs[i] < xs[j]
    requires NonIncr(xs[i+1..])
    requires forall k :: j < k < |xs| ==> xs[k] <= xs[i]
    requires multiset(p) == multiset(xs)
    requires LexLt(xs, p)
    ensures !LexLt(p, Res(xs, i, j))
  {
    Decomp(xs, i, j);
    var A := xs[..i];
    var x0 := xs[i];
    var M := xs[i+1..j];
    var y := xs[j];
    var T := xs[j+1..];
    var X := [x0] + M + [y] + T;
    var Z := M + [x0] + T;
    var r := Res(xs, i, j);

    assert xs == A + X;
    assert xs[i+1..] == M + [y] + T;
    assert r == A + ([y] + RevSeq(Z));
    RevProps(Z);
    MSCard(xs);
    MSCard(p);
    assert |p| == |xs|;
    assert |r| == |xs|;

    forall q | 0 <= q < |T|
      ensures T[q] <= x0
    {
      assert T[q] == xs[j + 1 + q];
    }

    if p[..i] == A {
      var P := p[i..];
      assert p == A + P;
      MSAppend(A, P);
      MSAppend(A, X);
      MSCancel(A, P, X);
      assert multiset(P) == multiset(X);
      LexPrefix(A, X, P);
      assert LexLt(X, P);
      Top(x0, M, y, T, P);
      LexPrefix(A, P, [y] + RevSeq(Z));
    } else {
      var k := LexDecomp(xs, p);
      if k >= i {
        assert p[..i] == xs[..i];
        assert p[..i] == A;
      } else {
        assert r[..k] == A[..k] == xs[..k] == p[..k];
        assert r[k] == A[k] == xs[k];
        LexIntro(r, p, k);
        LexAsym(r, p);
      }
    }
  }

  // ---------------------------------------------------------------
  // The two cases of the method, as lemmas.
  // ---------------------------------------------------------------

  // xs is non-increasing: its greatest arrangement; reversing it gives the least one.
  lemma FinishDesc(xs: seq<int>)
    requires NonIncr(xs)
    ensures multiset(RevSeq(xs)) == multiset(xs)
    ensures NonDecr(RevSeq(xs))
    ensures forall p: seq<int> :: multiset(p) == multiset(xs) ==> !LexLt(xs, p)
  {
    RevProps(xs);
    RevNonDecr(xs);
    forall p: seq<int> | multiset(p) == multiset(xs)
      ensures !LexLt(xs, p)
    {
      NonIncrMax(xs, p);
    }
  }

  // The successor Res(xs, i, j) is a permutation of xs, agreeing with xs before i,
  // with r[i] = xs[j] > xs[i].
  lemma ResPerm(xs: seq<int>, i: int, j: int)
    requires 0 <= i < j < |xs|
    ensures multiset(Res(xs, i, j)) == multiset(xs)
    ensures |Res(xs, i, j)| == |xs|
    ensures Res(xs, i, j)[..i] == xs[..i]
    ensures Res(xs, i, j)[i] == xs[j]
  {
    Decomp(xs, i, j);
    var A := xs[..i];
    var x0 := xs[i];
    var M := xs[i+1..j];
    var y := xs[j];
    var T := xs[j+1..];
    var X := [x0] + M + [y] + T;
    var Z := M + [x0] + T;
    var r := Res(xs, i, j);

    assert xs == A + X;
    assert r == A + ([y] + RevSeq(Z));
    RevProps(Z);
    MSRot(x0, M, y, T);
    MSAppend(A, [y] + RevSeq(Z));
    MSAppend([y], RevSeq(Z));
    MSAppend(A, X);
    assert multiset(r) == multiset(xs);
    MSCard(r);
    MSCard(xs);
    assert |r| == |xs|;
    assert r[..i] == xs[..i];
    assert r[i] == xs[j];
  }

  lemma FinishMin(xs: seq<int>, i: int, j: int)
    requires 0 <= i < j < |xs|
    requires xs[i] < xs[j]
    requires NonIncr(xs[i+1..])
    requires forall k :: j < k < |xs| ==> xs[k] <= xs[i]
    ensures forall p: seq<int> :: multiset(p) == multiset(xs) && LexLt(xs, p) ==> !LexLt(p, Res(xs, i, j))
  {
    forall p: seq<int> | multiset(p) == multiset(xs) && LexLt(xs, p)
      ensures !LexLt(p, Res(xs, i, j))
    {
      Minimal(xs, p, i, j);
    }
  }

  lemma Finish(xs: seq<int>, i: int, j: int)
    requires 0 <= i < j < |xs|
    requires xs[i] < xs[j]
    requires NonIncr(xs[i+1..])
    requires forall k :: j < k < |xs| ==> xs[k] <= xs[i]
    ensures multiset(Res(xs, i, j)) == multiset(xs)
    ensures LexLt(xs, Res(xs, i, j))
    ensures forall p: seq<int> :: multiset(p) == multiset(xs) && LexLt(xs, p) ==> !LexLt(p, Res(xs, i, j))
  {
    ResPerm(xs, i, j);
    LexIntro(xs, Res(xs, i, j), i);
    FinishMin(xs, i, j);
  }

  // ---------------------------------------------------------------
  // Method
  // ---------------------------------------------------------------

  // Pivot: the rightmost i with xs[i] < xs[i+1], or -1 if there is none.
  method FindPivot(xs: seq<int>) returns (i: int)
    requires |xs| >= 1
    ensures -1 <= i <= |xs| - 2
    ensures i >= 0 ==> xs[i] < xs[i+1]
    ensures NonIncr(xs[i+1..])
  {
    var n := |xs|;
    i := n - 2;
    while i >= 0 && xs[i] >= xs[i+1]
      invariant -1 <= i <= n - 2
      invariant forall a, b :: i + 1 <= a < b < n ==> xs[a] >= xs[b]
      decreases i
    {
      i := i - 1;
    }
    SliceNonIncr(xs, i + 1);
  }

  // Rightmost j > i with xs[j] > xs[i], given that xs[i] < xs[i+1].
  method FindRight(xs: seq<int>, i: int) returns (j: int)
    requires 0 <= i < |xs| - 1
    requires xs[i] < xs[i+1]
    ensures i + 1 <= j < |xs|
    ensures xs[i] < xs[j]
    ensures forall k :: j < k < |xs| ==> xs[k] <= xs[i]
  {
    j := |xs| - 1;
    while xs[j] <= xs[i]
      invariant i + 1 <= j < |xs|
      invariant forall k :: j < k < |xs| ==> xs[k] <= xs[i]
      decreases j
    {
      j := j - 1;
    }
  }

  method next_permutation(xs: seq<int>) returns (r: seq<int>)
    ensures multiset(r) == multiset(xs)
    ensures (exists p: seq<int> :: multiset(p) == multiset(xs) && LexLt(xs, p)) ==>
              (LexLt(xs, r) &&
               forall p: seq<int> :: multiset(p) == multiset(xs) && LexLt(xs, p) ==> !LexLt(p, r))
    ensures (forall p: seq<int> :: multiset(p) == multiset(xs) ==> !LexLt(xs, p)) ==> NonDecr(r)
  {
    var n := |xs|;
    if n == 0 {
      forall p: seq<int> | multiset(p) == multiset(xs)
        ensures !LexLt(xs, p)
      {
        MSCard(p);
      }
      r := xs;
      return;
    }

    var i := FindPivot(xs);
    if i < 0 {
      // xs is non-increasing: it is its own greatest arrangement; reverse it.
      FinishDesc(xs);
      r := RevSeq(xs);
      return;
    }

    var j := FindRight(xs, i);
    r := xs[..i] + [xs[j]] + RevSeq(xs[i+1..j] + [xs[i]] + xs[j+1..]);
    assert r == Res(xs, i, j);
    Finish(xs, i, j);
  }
}
