module Solution {

  // Rotate xs to the right by k positions.
  // Dafny's % is Euclidean (result in [0, |xs|)), so negative k and k >= |xs| are handled.
  method rotate(xs: seq<int>, k: int) returns (r: seq<int>)
    ensures |r| == |xs|
    ensures |xs| == 0 ==> r == []
    ensures |xs| > 0 ==> r == xs[|xs| - (k % |xs|)..] + xs[..|xs| - (k % |xs|)]
  {
    if |xs| == 0 {
      return xs;
    }
    var n := |xs|;
    var cut := n - (k % n);
    r := xs[cut..] + xs[..cut];
  }
}
