module Solution {

  // d is a positive common divisor of a and b.
  // (Only positive divisors are needed: divisibility is insensitive to sign.)
  predicate CommonDivisor(a: int, b: int, d: int) {
    d > 0 && a % d == 0 && b % d == 0
  }

  // A multiple of a positive d is divisible by d.
  lemma ModMul(k: int, d: int)
    requires d > 0
    ensures (d * k) % d == 0
  {
    var q := (d * k) / d;
    var r := (d * k) % d;
    assert d * k == d * q + r;
    var m := k - q;
    assert d * m == r;
    assert 0 <= r < d;
    if m >= 1 {
      assert d * (m - 1) >= 0;
      assert d * m >= d;
    }
    if m <= -1 {
      assert d * (-m - 1) >= 0;
      assert d * m <= -d;
    }
  }

  // A number m with |m| < d and d | m must be 0.
  lemma SmallMultipleIsZero(m: int, d: int)
    requires d > 0
    requires -d < m < d
    requires m % d == 0
    ensures m == 0
  {
  }

  // Negating does not change divisibility by a positive d.
  lemma NegDivisibility(a: int, d: int)
    requires d > 0
    ensures (-a) % d == 0 <==> a % d == 0
  {
    if a % d == 0 {
      var k := a / d;
      assert a == d * k;
      assert -a == d * (-k);
      ModMul(-k, d);
      assert (-a) % d == (d * (-k)) % d;
    }
    if (-a) % d == 0 {
      var k := (-a) / d;
      assert -a == d * k;
      assert a == d * (-k);
      ModMul(-k, d);
      assert a % d == (d * (-k)) % d;
    }
  }

  // Euclidean step: common divisors of (x, y) and (y, x % y) coincide, for y != 0.
  lemma EuclidStep(x: int, y: int, d: int)
    requires y != 0
    requires d > 0
    ensures CommonDivisor(x, y, d) <==> CommonDivisor(y, x % y, d)
  {
    var k := x / y;
    var s := x % y;
    assert x == y * k + s;
    if CommonDivisor(x, y, d) {
      var p := x / d;
      var q := y / d;
      assert x == d * p;
      assert y == d * q;
      assert y * k == d * (q * k);
      // s = x - y*k = d*(p - q*k)
      assert s == d * (p - q * k);
      ModMul(p - q * k, d);
      assert s % d == 0;
    }
    if CommonDivisor(y, s, d) {
      var q := y / d;
      var t := s / d;
      assert y == d * q;
      assert s == d * t;
      assert y * k == d * (q * k);
      // x = y*k + s = d*(q*k + t)
      assert x == d * (q * k + t);
      ModMul(q * k + t, d);
      assert x % d == 0;
    }
  }

  method gcd(a: int, b: int) returns (r: int)
    ensures 0 <= r
    ensures r == 0 ==> a == 0 && b == 0
    ensures r != 0 ==> a % r == 0 && b % r == 0
    ensures forall d :: CommonDivisor(a, b, d) ==> r % d == 0
  {
    var x := if a < 0 then -a else a;
    var y := if b < 0 then -b else b;

    assert forall d :: CommonDivisor(a, b, d) <==> CommonDivisor(x, y, d) by {
      forall d: int ensures CommonDivisor(a, b, d) <==> CommonDivisor(x, y, d) {
        if d > 0 {
          NegDivisibility(a, d);
          NegDivisibility(b, d);
        }
      }
    }

    while y != 0
      invariant 0 <= x && 0 <= y
      invariant forall d :: CommonDivisor(a, b, d) <==> CommonDivisor(x, y, d)
      decreases y
    {
      forall d: int ensures CommonDivisor(x, y, d) <==> CommonDivisor(y, x % y, d) {
        if d > 0 {
          EuclidStep(x, y, d);
        }
      }
      var t := x % y;
      x, y := y, t;
    }

    r := x;

    if r != 0 {
      ModMul(1, r);
      assert CommonDivisor(x, 0, x);
      assert CommonDivisor(a, b, x);
    }
    if r == 0 {
      var da := (if a < 0 then -a else a) + 1;
      ModMul(1, da);
      assert CommonDivisor(x, 0, da);
      assert CommonDivisor(a, b, da);
      assert a % da == 0;
      SmallMultipleIsZero(a, da);
      var db := (if b < 0 then -b else b) + 1;
      ModMul(1, db);
      assert CommonDivisor(x, 0, db);
      assert CommonDivisor(a, b, db);
      assert b % db == 0;
      SmallMultipleIsZero(b, db);
    }
  }
}
