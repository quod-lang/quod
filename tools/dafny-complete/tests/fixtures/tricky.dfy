// Layout traps: { braces } and the word method in comments.
/* nested /* comment with } */ still a comment: method Fake() returns (x: int) */

method Main() {
  print "hello { method Nope() returns (z: int) ", '}', "\n";
}

function Square(x: int): int { x * x }

// determined
method Abs(x: int) returns (y: int)
  ensures y >= 0
  ensures y == x || y == -x
{
  if x < 0 { y := -x; } else { y := x; }
}

// underspecified: for x = 0 both 0 and 1 are >= 0
method WeakAbs(x: int) returns (y: int)
  ensures y >= 0
{
  y := if x < 0 then -x else x;
}

module Outer {
  module Inner {
    // underspecified: a is only bounded above
    method {:verify true} Pair(n: nat) returns (a: int, b: int)
      ensures b == n && a <= b
    {
      a, b := 0, n;
    }
  }
}

class Counter {
  var count: int

  // underspecified: when x is out of range, any r in [lo, hi] is accepted
  static method Clamp(x: int, lo: int, hi: int) returns (r: int)
    requires lo <= hi
    ensures lo <= r <= hi
    ensures lo <= x <= hi ==> r == x
  {
    r := if x < lo then lo else if x > hi then hi else x;
  }

  // skipped: instance method touching the heap
  method Inc() returns (prev: int)
    modifies this
    ensures count == old(count) + 1
    ensures prev == old(count)
  {
    prev := count;
    count := count + 1;
  }
}

// determined (generic: no witness search needed)
method Length<T>(xs: seq<T>) returns (n: nat)
  ensures n == |xs|
{
  n := |xs|;
}

// determined, with a set display and a primed name
method Single(x': int) returns (s: set<int>)
  ensures s == {x'}
  ensures s != {}
{
  s := {x'};
}

// bodiless: cannot be run, uniqueness not provable -> inconclusive
method Abstract(x: int) returns (y: int)
  ensures y > x

// skipped: no outputs
method NoOut(x: int)
  ensures true
{
}

// determined, labelled requires
method Copy(c: char) returns (d: char)
  requires L: c != '{'
  ensures d == c
{
  d := c;
}

// underspecified: only the length is constrained
method Bang(s: string) returns (t: string)
  ensures |t| == |s| + 1
{
  t := s + "!";
}
