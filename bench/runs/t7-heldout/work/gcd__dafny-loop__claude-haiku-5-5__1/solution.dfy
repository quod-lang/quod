module Solution {

  // d divides x (in the integers, so sign-agnostic; d = 0 divides only 0)
  ghost predicate Dvd(d: int, x: int) {
    exists k: int :: x == d * k
  }

  lemma DvdSelf(x: int)
    ensures Dvd(x, x)
  {
    assert x == x * 1;
    assert exists k: int :: x == x * k by {
      assert x == x * 1;
    }
  }

  lemma DvdZero(x: int)
    ensures Dvd(x, 0)
  {
    assert 0 == x * 0;
    assert exists k: int :: 0 == x * k by {
      assert 0 == x * 0;
    }
  }

  lemma NegDvd(d: int, x: int)
    ensures Dvd(d, -x) <==> Dvd(d, x)
  {
    if Dvd(d, x) {
      var k :| x == d * k;
      assert -x == d * (-k);
    }
    if Dvd(d, -x) {
      var k :| -x == d * k;
      assert x == d * (-k);
    }
  }

  lemma DvdMod(d: int, x: int, y: int)
    requires y != 0
    requires Dvd(d, x) && Dvd(d, y)
    ensures Dvd(d, x % y)
  {
    var k1 :| x == d * k1;
    var k2 :| y == d * k2;
    var q := x / y;
    assert x == q * y + x % y;
    assert q * y == d * (q * k2);
    assert x % y == d * k1 - d * (q * k2);
    assert x % y == d * (k1 - q * k2);
  }

  lemma DvdComb(d: int, x: int, y: int)
    requires y != 0
    requires Dvd(d, y) && Dvd(d, x % y)
    ensures Dvd(d, x)
  {
    var k2 :| y == d * k2;
    var k3 :| x % y == d * k3;
    var q := x / y;
    assert x == q * y + x % y;
    assert q * y == d * (q * k2);
    assert x == d * (q * k2) + d * k3;
    assert x == d * (q * k2 + k3);
  }

  // One Euclid step preserves the set of common divisors.
  lemma Step(d: int, x: int, y: int)
    requires y != 0
    ensures (Dvd(d, x) && Dvd(d, y)) <==> (Dvd(d, y) && Dvd(d, x % y))
  {
    if Dvd(d, x) && Dvd(d, y) {
      DvdMod(d, x, y);
    }
    if Dvd(d, y) && Dvd(d, x % y) {
      DvdComb(d, x, y);
    }
  }

  method gcd(a: int, b: int) returns (r: int)
    ensures r >= 0
    ensures Dvd(r, a) && Dvd(r, b)
    ensures forall d: int :: (Dvd(d, a) && Dvd(d, b)) ==> Dvd(d, r)
  {
    var x := a;
    if a < 0 {
      x := -a;
    }
    var y := b;
    if b < 0 {
      y := -b;
    }

    forall d: int ensures (Dvd(d, x) && Dvd(d, y)) <==> (Dvd(d, a) && Dvd(d, b)) {
      if a < 0 {
        NegDvd(d, a);
      }
      if b < 0 {
        NegDvd(d, b);
      }
    }

    while y != 0
      invariant x >= 0 && y >= 0
      invariant forall d: int :: (Dvd(d, x) && Dvd(d, y)) <==> (Dvd(d, a) && Dvd(d, b))
      decreases y
    {
      forall d: int ensures (Dvd(d, y) && Dvd(d, x % y)) <==> (Dvd(d, x) && Dvd(d, y)) {
        Step(d, x, y);
      }
      var t := x % y;
      x := y;
      y := t;
    }

    r := x;
    DvdSelf(x);
    DvdZero(x);
  }
}
