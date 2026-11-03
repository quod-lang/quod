module Solution {

  // Rotate `xs` to the right by `k` positions.
  // Dafny's % is Euclidean (result in [0, n) for n > 0), so negative k
  // rotates left and large k wraps around.
  method rotate(xs: seq<int>, k: int) returns (r: seq<int>)
    ensures |r| == |xs|
    ensures forall i :: 0 <= i < |xs| ==> r[i] == xs[(i - k) % |xs|]
  {
    var n := |xs|;
    r := [];
    var i := 0;
    while i < n
      invariant 0 <= i <= n == |xs|
      invariant |r| == i
      invariant forall j :: 0 <= j < i ==> r[j] == xs[(j - k) % n]
      decreases n - i
    {
      r := r + [xs[(i - k) % n]];
      i := i + 1;
    }
  }
}
