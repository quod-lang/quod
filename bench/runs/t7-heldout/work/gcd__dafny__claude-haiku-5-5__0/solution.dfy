module Solution {

  // d divides n (explicit witness form).
  ghost predicate Dvd(d: int, n: int) {
    exists k :: n == d * k
  }

  // d is a nonzero common divisor of a and b.
  ghost predicate IsCommonDivisor(d: int, a: int, b: int) {
    d != 0 && Dvd(d, a) && Dvd(d, b)
  }

  lemma DvdZero(d: int)
    ensures Dvd(d, 0)
  {
    assert 0 == d * 0;
  }

  lemma DvdSelf(d: int)
    ensures Dvd(d, d)
  {
    assert d == d * 1;
  }

  lemma DvdNeg(d: int, n: int)
    ensures Dvd(d, n) <==> Dvd(d, -n)
  {
    if Dvd(d, n) {
      var k :| n == d * k;
      assert -n == d * (-k);
    }
    if Dvd(d, -n) {
      var k :| -n == d * k;
      assert n == d * (-k);
    }
  }

  // Taking absolute values does not change the common nonzero divisors.
  lemma AbsCommonDivisors(a: int, b: int)
    ensures forall d :: IsCommonDivisor(d, if a < 0 then -a else a, if b < 0 then -b else b)
                        <==> IsCommonDivisor(d, a, b)
  {
    forall d
      ensures IsCommonDivisor(d, if a < 0 then -a else a, if b < 0 then -b else b)
              <==> IsCommonDivisor(d, a, b)
    {
      DvdNeg(d, a);
      DvdNeg(d, b);
    }
  }

  // A divisor d > 0 of v with |v| < d forces v == 0.
  lemma DvdSmallIsZero(d: int, v: int)
    requires d > 0
    requires Dvd(d, v)
    requires -d < v < d
    ensures v == 0
  {
    var k :| v == d * k;
    if k >= 1 {
      assert d * (k - 1) >= 0;
      assert d * k >= d;
      assert false;
    } else if k <= -1 {
      assert d * (-1 - k) >= 0;
      assert d * k <= -d;
      assert false;
    }
  }

  // One Euclid step: (x, y) -> (y, x % y) preserves the common nonzero divisors.
  lemma EuclidStepPreserves(x: int, y: int)
    requires y != 0
    ensures forall d :: IsCommonDivisor(d, x, y) <==> IsCommonDivisor(d, y, x % y)
  {
    forall d
      ensures IsCommonDivisor(d, x, y) <==> IsCommonDivisor(d, y, x % y)
    {
      if d != 0 {
        var q := x / y;
        var rr := x % y;
        assert x == q * y + rr;
        if IsCommonDivisor(d, x, y) {
          var p :| x == d * p;
          var m :| y == d * m;
          assert q * y == d * (q * m);
          assert rr == d * (p - q * m);
          assert Dvd(d, rr);
        }
        if IsCommonDivisor(d, y, rr) {
          var m :| y == d * m;
          var s :| rr == d * s;
          assert q * y == d * (q * m);
          assert x == d * (q * m + s);
          assert Dvd(d, x);
        }
      }
    }
  }

  method gcd(a: int, b: int) returns (r: int)
    ensures r >= 0
    ensures (r == 0) <==> (a == 0 && b == 0)
    ensures r != 0 ==> Dvd(r, a) && Dvd(r, b)
    ensures forall d :: IsCommonDivisor(d, a, b) ==> Dvd(d, r)
  {
    var x := if a < 0 then -a else a;
    var y := if b < 0 then -b else b;
    AbsCommonDivisors(a, b);
    while y != 0
      invariant x >= 0 && y >= 0
      invariant forall d :: IsCommonDivisor(d, x, y) <==> IsCommonDivisor(d, a, b)
      decreases y
    {
      EuclidStepPreserves(x, y);
      var t := x % y;
      x := y;
      y := t;
    }
    r := x;

    // With y == 0, a common divisor of (r, 0) is a divisor of r, and vice versa.
    forall d | IsCommonDivisor(d, a, b)
      ensures Dvd(d, r)
    {
      DvdZero(d);
      assert IsCommonDivisor(d, r, 0);
    }

    if r != 0 {
      DvdSelf(r);
      DvdZero(r);
      assert IsCommonDivisor(r, r, 0);
      assert IsCommonDivisor(r, a, b);
    }

    if a == 0 && b == 0 {
      // Every nonzero d is a common divisor of (0, 0); take d = r + 1.
      var d := r + 1;
      DvdZero(d);
      assert IsCommonDivisor(d, 0, 0);
      assert IsCommonDivisor(d, a, b);
      assert IsCommonDivisor(d, r, 0);
      DvdSmallIsZero(d, r);
      assert r == 0;
    }

    if r == 0 && (a != 0 || b != 0) {
      // Take d = |a| + |b| + 1: a common divisor of (0, 0), hence of (a, b).
      var d := (if a < 0 then -a else a) + (if b < 0 then -b else b) + 1;
      DvdZero(d);
      assert IsCommonDivisor(d, 0, 0);
      assert IsCommonDivisor(d, r, 0);
      assert IsCommonDivisor(d, a, b);
      DvdSmallIsZero(d, a);
      DvdSmallIsZero(d, b);
      assert false;
    }
  }
}
