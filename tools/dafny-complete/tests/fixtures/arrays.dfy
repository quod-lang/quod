// Arrays: heap-allocated inputs and outputs.

// determined (from MBPP-DFY-153, task 101)
method KthElement(arr: array<int>, k: int) returns (result: int)
  requires 1 <= k <= arr.Length
  ensures result == arr[k - 1]
{
  result := arr[k - 1];
}

// underspecified: "some element", not the maximum
method WeakMax(a: array<int>) returns (m: int)
  requires a.Length > 0
  ensures exists i :: 0 <= i < a.Length && a[i] == m
{
  m := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant exists j :: 0 <= j < i && a[j] == m
    invariant forall j :: 0 <= j < i ==> a[j] <= m
  {
    if a[i] > m { m := a[i]; }
    i := i + 1;
  }
}

// determined: array output, contents fully specified
method CopyOf(a: array<int>) returns (b: array<int>)
  ensures b.Length == a.Length
  ensures forall i :: 0 <= i < a.Length ==> b[i] == a[i]
{
  b := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> b[j] == a[j]
  {
    b[i] := a[i];
    i := i + 1;
  }
}

// underspecified: array output, only the length is constrained
method Doubled(a: array<int>) returns (b: array<int>)
  ensures b.Length == a.Length
{
  b := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
  {
    b[i] := 2 * a[i];
    i := i + 1;
  }
}
