module Solution {
  predicate IsValidUtf8Sequence(bs: seq<int>) {
    IsValidUtf8Impl(bs, 0)
  }

  predicate IsValidUtf8Impl(bs: seq<int>, pos: nat)
    decreases |bs| - pos
  {
    if pos >= |bs| then true
    else if bs[pos] < 128 then IsValidUtf8Impl(bs, pos + 1)
    else if bs[pos] < 192 then false
    else if bs[pos] < 224 then
      (pos + 1 < |bs| &&
       128 <= bs[pos + 1] && bs[pos + 1] < 192 &&
       !(bs[pos] == 0xC0 || bs[pos] == 0xC1) &&
       IsValidUtf8Impl(bs, pos + 2))
    else if bs[pos] < 240 then
      (pos + 2 < |bs| &&
       128 <= bs[pos + 1] && bs[pos + 1] < 192 &&
       128 <= bs[pos + 2] && bs[pos + 2] < 192 &&
       !(bs[pos] == 0xE0 && (bs[pos + 1] / 32) % 2 == 0) &&
       !(bs[pos] == 0xED && (bs[pos + 1] / 32) % 2 == 1 && (bs[pos + 1] / 128) % 2 == 1) &&
       IsValidUtf8Impl(bs, pos + 3))
    else if bs[pos] < 248 then
      (pos + 3 < |bs| &&
       128 <= bs[pos + 1] && bs[pos + 1] < 192 &&
       128 <= bs[pos + 2] && bs[pos + 2] < 192 &&
       128 <= bs[pos + 3] && bs[pos + 3] < 192 &&
       !(bs[pos] == 0xF0 && (bs[pos + 1] / 16) % 4 == 0) &&
       !(bs[pos] > 0xF4 || (bs[pos] == 0xF4 && (bs[pos + 1] / 16) % 4 != 0)) &&
       IsValidUtf8Impl(bs, pos + 4))
    else false
  }

  method ValidateBytes(bs: seq<int>, pos: nat) returns (b: bool)
    requires forall i :: 0 <= i < |bs| ==> 0 <= bs[i] <= 255
    requires pos <= |bs|
    ensures b <==> IsValidUtf8Impl(bs, pos)
    decreases |bs| - pos
  {
    if pos >= |bs| {
      b := true;
    } else {
      var byte := bs[pos];
      if byte < 128 {
        b := ValidateBytes(bs, pos + 1);
      } else if byte < 192 {
        b := false;
      } else if byte < 224 {
        if pos + 1 >= |bs| {
          b := false;
        } else if !(128 <= bs[pos + 1] && bs[pos + 1] < 192) {
          b := false;
        } else if byte == 0xC0 || byte == 0xC1 {
          b := false;
        } else {
          b := ValidateBytes(bs, pos + 2);
        }
      } else if byte < 240 {
        if pos + 2 >= |bs| {
          b := false;
        } else if !(128 <= bs[pos + 1] && bs[pos + 1] < 192) {
          b := false;
        } else if !(128 <= bs[pos + 2] && bs[pos + 2] < 192) {
          b := false;
        } else if byte == 0xE0 && (bs[pos + 1] / 32) % 2 == 0 {
          b := false;
        } else if byte == 0xED && (bs[pos + 1] / 32) % 2 == 1 && (bs[pos + 1] / 128) % 2 == 1 {
          b := false;
        } else {
          b := ValidateBytes(bs, pos + 3);
        }
      } else if byte < 248 {
        if pos + 3 >= |bs| {
          b := false;
        } else if !(128 <= bs[pos + 1] && bs[pos + 1] < 192) {
          b := false;
        } else if !(128 <= bs[pos + 2] && bs[pos + 2] < 192) {
          b := false;
        } else if !(128 <= bs[pos + 3] && bs[pos + 3] < 192) {
          b := false;
        } else if byte == 0xF0 && (bs[pos + 1] / 16) % 4 == 0 {
          b := false;
        } else if byte > 0xF4 || (byte == 0xF4 && (bs[pos + 1] / 16) % 4 != 0) {
          b := false;
        } else {
          b := ValidateBytes(bs, pos + 4);
        }
      } else {
        b := false;
      }
    }
  }

  method utf8_valid(bs: seq<int>) returns (b: bool)
    requires forall i :: 0 <= i < |bs| ==> 0 <= bs[i] <= 255
    ensures b <==> IsValidUtf8Sequence(bs)
  {
    b := ValidateBytes(bs, 0);
  }
}
