module Solution {
  // Right rotation of xs by k positions. Dafny's % on a positive divisor is
  // Euclidean (non-negative), so negative k rotates left and large k wraps.
  function RotateRight(xs: seq<int>, k: int): seq<int>
  {
    if |xs| == 0 then []
    else
      var s := k % |xs|;
      xs[|xs| - s..] + xs[..|xs| - s]
  }

  method rotate(xs: seq<int>, k: int) returns (r: seq<int>)
    ensures r == RotateRight(xs, k)
    ensures |r| == |xs|
  {
    if |xs| == 0 {
      return [];
    }
    var n := |xs|;
    var s := k % n;
    r := xs[n - s..] + xs[..n - s];
  }
}
