// Datatypes as inputs, outputs and receivers.

datatype Color = Red | Green | Blue

datatype Option<T> = None | Some(value: T)

datatype Tree = Leaf | Node(left: Tree, val: int, right: Tree)

function Size(t: Tree): nat
{
  match t
  case Leaf => 0
  case Node(l, _, r) => Size(l) + 1 + Size(r)
}

// determined: enumeration in and out
method Next(c: Color) returns (d: Color)
  ensures c == Red ==> d == Green
  ensures c == Green ==> d == Blue
  ensures c == Blue ==> d == Red
{
  d := match c
    case Red => Green
    case Green => Blue
    case Blue => Red;
}

// underspecified: generic datatype output, None is always accepted
method Find(s: seq<int>, x: int) returns (r: Option<nat>)
  ensures r.Some? ==> r.value < |s| && s[r.value] == x
{
  r := None;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant r.Some? ==> r.value < |s| && s[r.value] == x
  {
    if s[i] == x {
      r := Some(i);
      return;
    }
    i := i + 1;
  }
}

// determined: recursive datatype input
method CountNodes(t: Tree) returns (n: nat)
  ensures n == Size(t)
{
  n := Size(t);
}

// underspecified: only the empty tree is pinned down
method WeakCount(t: Tree) returns (n: nat)
  ensures t.Leaf? ==> n == 0
{
  n := Size(t);
}

// underspecified: datatype output, only the constructor is constrained
method SomeOf(x: int) returns (r: Option<int>)
  ensures r.Some?
{
  r := Some(x);
}
