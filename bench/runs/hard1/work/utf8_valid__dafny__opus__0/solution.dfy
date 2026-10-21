module Solution {
  predicate InRange(x: int, lo: int, hi: int) { lo <= x <= hi }

  predicate Cont(x: int) { InRange(x, 0x80, 0xBF) }

  // Length of the well-formed UTF-8 character starting at index i, or 0 if none.
  function CharLen(bs: seq<int>, i: nat): nat
    requires i < |bs|
    ensures CharLen(bs, i) <= |bs| - i
  {
    var b0 := bs[i];
    var n := |bs| - i;
    if InRange(b0, 0x00, 0x7F) then 1
    else if InRange(b0, 0xC2, 0xDF) then
      (if n >= 2 && Cont(bs[i+1]) then 2 else 0)
    else if b0 == 0xE0 then
      (if n >= 3 && InRange(bs[i+1], 0xA0, 0xBF) && Cont(bs[i+2]) then 3 else 0)
    else if InRange(b0, 0xE1, 0xEC) || InRange(b0, 0xEE, 0xEF) then
      (if n >= 3 && Cont(bs[i+1]) && Cont(bs[i+2]) then 3 else 0)
    else if b0 == 0xED then
      (if n >= 3 && InRange(bs[i+1], 0x80, 0x9F) && Cont(bs[i+2]) then 3 else 0)
    else if b0 == 0xF0 then
      (if n >= 4 && InRange(bs[i+1], 0x90, 0xBF) && Cont(bs[i+2]) && Cont(bs[i+3]) then 4 else 0)
    else if InRange(b0, 0xF1, 0xF3) then
      (if n >= 4 && Cont(bs[i+1]) && Cont(bs[i+2]) && Cont(bs[i+3]) then 4 else 0)
    else if b0 == 0xF4 then
      (if n >= 4 && InRange(bs[i+1], 0x80, 0x8F) && Cont(bs[i+2]) && Cont(bs[i+3]) then 4 else 0)
    else 0
  }

  predicate ValidFrom(bs: seq<int>, i: nat)
    requires i <= |bs|
    decreases |bs| - i
  {
    if i == |bs| then true
    else
      var l := CharLen(bs, i);
      l > 0 && ValidFrom(bs, i + l)
  }

  predicate ValidUtf8(bs: seq<int>) { ValidFrom(bs, 0) }

  method utf8_valid(bs: seq<int>) returns (b: bool)
    requires forall k :: 0 <= k < |bs| ==> 0 <= bs[k] <= 255
    ensures b == ValidUtf8(bs)
  {
    var i := 0;
    while i < |bs|
      invariant 0 <= i <= |bs|
      invariant ValidFrom(bs, 0) == ValidFrom(bs, i)
      decreases |bs| - i
    {
      var l := CharLen(bs, i);
      if l == 0 {
        return false;
      }
      i := i + l;
    }
    return true;
  }
}
