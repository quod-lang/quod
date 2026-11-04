module Solution {

  function Abs(x: int): int {
    if x < 0 then -x else x
  }

  // Euclid's algorithm on signed integers. Dafny's % is Euclidean (always in [0, |y|)),
  // so the recursion terminates: |a % b| < |b|.
  function GcdSpec(a: int, b: int): int
    decreases Abs(b)
  {
    if b == 0 then Abs(a)
    else GcdSpec(b, a % b)
  }

  method gcd(a: int, b: int) returns (r: int)
    ensures r == GcdSpec(a, b)
    ensures r >= 0
    ensures a == 0 && b == 0 ==> r == 0
  {
    var x := a;
    var y := b;
    while y != 0
      invariant GcdSpec(x, y) == GcdSpec(a, b)
      decreases Abs(y)
    {
      var t := x % y;
      x := y;
      y := t;
    }
    r := Abs(x);
  }
}
