module Solution {

  // d is a positive common divisor of x and y
  predicate IsCommonDivisor(d: int, x: int, y: int) {
    d > 0 && x % d == 0 && y % d == 0
  }

  // A multiple of d is divisible by d
  lemma MultipleMod(d: int, z: int)
    requires d > 0
    ensures (d * z) % d == 0
  {
    var q := (d * z) / d;
    var r := (d * z) % d;
    var c := z - q;
    assert d * z == d * q + r;
    assert r == d * c;
    assert 0 <= r < d;
    if c >= 1 {
      assert d * c >= d * 1;
      assert r >= d;
    }
    if c <= -1 {
      assert d * c <= d * (-1);
      assert r <= -d;
    }
    assert c == 0;
    assert r == 0;
  }

  // Divisibility is unchanged by negation (for d > 0)
  lemma NegDivisibilityFwd(x: int, d: int)
    requires d > 0
    requires x % d == 0
    ensures (-x) % d == 0
  {
    var k := x / d;
    assert x == d * k;
    assert -x == d * (-k);
    MultipleMod(d, -k);
  }

  lemma NegDivisibility(x: int, d: int)
    requires d > 0
    ensures (-x) % d == 0 <==> x % d == 0
  {
    if x % d == 0 {
      NegDivisibilityFwd(x, d);
    }
    if (-x) % d == 0 {
      NegDivisibilityFwd(-x, d);
    }
  }

  // Euclid step: common divisors of (x, y) with y > 0 are exactly those of (y, x % y)
  lemma EuclidStep(x: int, y: int, d: int)
    requires x >= 0 && y > 0 && d > 0
    ensures (x % d == 0 && y % d == 0) <==> (y % d == 0 && (x % y) % d == 0)
  {
    var q := x / y;
    var m := x % y;
    assert x == y * q + m;
    if x % d == 0 && y % d == 0 {
      var k1 := x / d;
      var k2 := y / d;
      assert x == d * k1;
      assert y == d * k2;
      assert y * q == d * (k2 * q);
      assert m == d * k1 - d * (k2 * q);
      assert m == d * (k1 - k2 * q);
      MultipleMod(d, k1 - k2 * q);
    }
    if y % d == 0 && m % d == 0 {
      var k2 := y / d;
      var k3 := m / d;
      assert y == d * k2;
      assert m == d * k3;
      assert x == d * (k2 * q + k3);
      MultipleMod(d, k2 * q + k3);
    }
  }

  // If x > 0 and d > 0 divides x, then d <= x
  lemma DivisorBound(x: int, d: int)
    requires x > 0 && d > 0 && x % d == 0
    ensures d <= x
  {
    if d > x {
      assert 0 <= x < d;
      assert x % d == x;
      assert x == 0;
    }
  }

  method gcd(a: int, b: int) returns (r: int)
    ensures r >= 0
    ensures a == 0 && b == 0 ==> r == 0
    ensures !(a == 0 && b == 0) ==> r > 0 && a % r == 0 && b % r == 0
    ensures !(a == 0 && b == 0) ==> forall d: int :: IsCommonDivisor(d, a, b) ==> d <= r
  {
    var x := if a < 0 then -a else a;
    var y := if b < 0 then -b else b;

    assert forall d: int | d > 0 :: (x % d == 0 && y % d == 0) <==> (a % d == 0 && b % d == 0) by {
      forall d: int | d > 0
        ensures (x % d == 0 && y % d == 0) <==> (a % d == 0 && b % d == 0)
      {
        NegDivisibility(a, d);
        NegDivisibility(b, d);
      }
    }

    while y != 0
      invariant x >= 0 && y >= 0
      invariant forall d: int | d > 0 :: (x % d == 0 && y % d == 0) <==> (a % d == 0 && b % d == 0)
      invariant a == 0 && b == 0 ==> x == 0 && y == 0
      invariant x == 0 && y == 0 ==> a == 0 && b == 0
      decreases y
    {
      forall d: int | d > 0
        ensures (y % d == 0 && (x % y) % d == 0) <==> (a % d == 0 && b % d == 0)
      {
        EuclidStep(x, y, d);
      }
      var t := x % y;
      x := y;
      y := t;
    }

    r := x;

    if a == 0 && b == 0 {
      assert r == 0;
    } else {
      assert x > 0 by {
        if x == 0 {
          assert y == 0;
          assert a == 0 && b == 0;
        }
      }
      assert r % r == 0;
      forall d: int | IsCommonDivisor(d, a, b)
        ensures d <= r
      {
        assert r % d == 0;
        DivisorBound(r, d);
      }
    }
  }
}
