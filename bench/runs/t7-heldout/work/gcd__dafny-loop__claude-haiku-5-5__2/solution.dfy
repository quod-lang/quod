module Solution {

  // Euclid's algorithm on non-negative integers.
  function Gcd(x: int, y: int): int
    requires x >= 0 && y >= 0
    ensures Gcd(x, y) >= 0
    decreases y
  {
    if y == 0 then x else Gcd(y, x % y)
  }

  // r is the greatest common divisor of a and b (signs ignored),
  // with gcd(0, 0) = 0.
  ghost predicate IsGcd(a: int, b: int, r: int) {
    r >= 0 &&
    (r == 0 <==> a == 0 && b == 0) &&
    (r != 0 ==> a % r == 0 && b % r == 0) &&
    ((a != 0 || b != 0) ==> forall d: int :: d > 0 && a % d == 0 && b % d == 0 ==> d <= r)
  }

  // If x is a multiple of d > 0, then x % d == 0.
  lemma DvdMod(x: int, d: int, k: int)
    requires d > 0 && x == d * k
    ensures x % d == 0
  {
    var q := x / d;
    var r := x % d;
    assert x == d * q + r;
    var j := k - q;
    assert r == d * j;
    if j >= 1 {
      assert d * j >= d;
    }
    if j <= -1 {
      assert d * j <= -d;
    }
    assert j == 0;
  }

  lemma ModNeg(a: int, d: int)
    requires d > 0
    ensures a % d == 0 <==> (-a) % d == 0
  {
    if a % d == 0 {
      var q := a / d;
      assert a == d * q;
      DvdMod(-a, d, -q);
    }
    if (-a) % d == 0 {
      var q := (-a) / d;
      assert -a == d * q;
      DvdMod(a, d, -q);
    }
  }

  // Every positive common divisor of x and y divides Gcd(x, y).
  lemma GcdMultiple(x: int, y: int, d: int)
    requires x >= 0 && y >= 0 && d > 0 && x % d == 0 && y % d == 0
    ensures Gcd(x, y) % d == 0
    decreases y
  {
    if y != 0 {
      var q := x / y;
      var n := x / d;
      var m := y / d;
      assert x == d * n;
      assert y == d * m;
      assert x % y == x - y * q;
      assert x % y == d * (n - m * q);
      DvdMod(x % y, d, n - m * q);
      GcdMultiple(y, x % y, d);
    }
  }

  lemma GcdDivides(x: int, y: int)
    requires x >= 0 && y >= 0
    ensures var g := Gcd(x, y);
            (g == 0 ==> x == 0 && y == 0) &&
            (g != 0 ==> x % g == 0 && y % g == 0)
    decreases y
  {
    if y == 0 {
      if x != 0 {
        DvdMod(x, x, 1);
        DvdMod(0, x, 0);
      }
    } else {
      GcdDivides(y, x % y);
      var g := Gcd(y, x % y);
      if g != 0 {
        var q := x / y;
        var r := x % y;
        assert x == y * q + r;
        assert y == g * (y / g);
        assert r == g * (r / g);
        assert x == g * ((y / g) * q + r / g);
        DvdMod(x, g, (y / g) * q + r / g);
        DvdMod(y, g, y / g);
      }
    }
  }

  lemma GcdIsGcd(x: int, y: int)
    requires x >= 0 && y >= 0
    ensures IsGcd(x, y, Gcd(x, y))
  {
    GcdDivides(x, y);
    var g := Gcd(x, y);
    if x != 0 || y != 0 {
      forall d: int | d > 0 && x % d == 0 && y % d == 0
        ensures d <= g
      {
        GcdMultiple(x, y, d);
        assert g % d == 0;
        assert g > 0;
        var j := g / d;
        assert g == d * j;
        if j <= 0 {
          assert d * j <= 0;
        }
        assert j >= 1;
        assert d * j >= d;
      }
    }
  }

  lemma AbsTransfer(a: int, b: int, r: int)
    requires IsGcd(if a < 0 then -a else a, if b < 0 then -b else b, r)
    ensures IsGcd(a, b, r)
  {
    var x := if a < 0 then -a else a;
    var y := if b < 0 then -b else b;
    assert (a != 0 || b != 0) <==> (x != 0 || y != 0);
    forall d: int | d > 0
      ensures (a % d == 0) == (x % d == 0)
      ensures (b % d == 0) == (y % d == 0)
    {
      if a < 0 { ModNeg(a, d); }
      if b < 0 { ModNeg(b, d); }
    }
  }

  method gcd(a: int, b: int) returns (r: int)
    ensures IsGcd(a, b, r)
  {
    var x := if a < 0 then -a else a;
    var y := if b < 0 then -b else b;
    ghost var X := x;
    ghost var Y := y;
    while y != 0
      invariant x >= 0 && y >= 0
      invariant Gcd(x, y) == Gcd(X, Y)
      decreases y
    {
      var t := x % y;
      x := y;
      y := t;
    }
    GcdIsGcd(X, Y);
    r := x;
    AbsTransfer(a, b, r);
  }
}
