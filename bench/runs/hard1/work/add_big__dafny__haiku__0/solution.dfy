module Solution {
  predicate IsCanonical(s: string) {
    if s == "0" then true
    else if |s| > 0 && s[0] == '-' then
      |s| > 1 && s[1] != '0' && forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9'
    else if |s| > 0 then
      s[0] != '0' && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    else
      false
  }

  predicate IsDigitString(s: string) {
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  }

  lemma CanonicalNonZeroPositiveToDigitString(s: string)
    requires IsCanonical(s)
    requires s != "0"
    requires |s| == 0 || s[0] != '-'
    ensures s != "" && IsDigitString(s)
  {
  }

  lemma CanonicalNegativeToAbsoluteDigitString(s: string)
    requires IsCanonical(s)
    requires |s| > 0 && s[0] == '-'
    ensures s[1..] != "" && IsDigitString(s[1..])
  {
  }


  function CharToDigit(c: char): int
    requires '0' <= c <= '9'
  {
    (c as int) - ('0' as int)
  }

  function DigitToChar(d: int): char
    requires 0 <= d <= 9
  {
    ((d + ('0' as int)) as char)
  }

  method AddAbsolute(a: string, b: string) returns (s: string)
    requires a != "" && IsDigitString(a) && a[0] != '0'
    requires b != "" && IsDigitString(b) && b[0] != '0'
    ensures s != "" && IsDigitString(s)
  {
    var len_a := |a|;
    var len_b := |b|;
    var max_len := if len_a > len_b then len_a else len_b;

    var result := "";
    var carry := 0;
    var i := 0;

    while i < max_len
      invariant 0 <= i <= max_len
      invariant 0 <= carry <= 1
      invariant IsDigitString(result)
      decreases max_len - i
    {
      var digit_a := if i < len_a then CharToDigit(a[len_a - 1 - i]) else 0;
      var digit_b := if i < len_b then CharToDigit(b[len_b - 1 - i]) else 0;

      var sum := digit_a + digit_b + carry;
      var digit := sum % 10;
      carry := sum / 10;

      result := [DigitToChar(digit)] + result;
      i := i + 1;
    }

    if carry > 0 {
      result := [DigitToChar(1)] + result;
    }

    if |result| == 0 {
      result := "0";
    }

    return result;
  }

  method SubtractAbsolute(a: string, b: string) returns (s: string)
    requires a != "" && IsDigitString(a)
    requires b != "" && IsDigitString(b)
    ensures s != "" && (s == "0" || IsDigitString(s))
  {
    var len_a := |a|;
    var len_b := |b|;

    var result := "";
    var borrow := 0;
    var i := 0;

    while i < len_a
      invariant 0 <= i <= len_a
      invariant 0 <= borrow <= 1
      invariant IsDigitString(result)
      decreases len_a - i
    {
      var digit_a := CharToDigit(a[len_a - 1 - i]);
      var digit_b := if i < len_b then CharToDigit(b[len_b - 1 - i]) else 0;

      var diff := digit_a - digit_b - borrow;
      if diff < 0 {
        diff := diff + 10;
        borrow := 1;
      } else {
        borrow := 0;
      }

      result := [DigitToChar(diff)] + result;
      i := i + 1;
    }

    var j := 0;
    while j < |result| && result[j] == '0'
      decreases |result| - j
    {
      j := j + 1;
    }

    if j >= |result| {
      return "0";
    } else {
      result := result[j..];
      return result;
    }
  }

  function CompareAbsoluteValues(a: string, b: string): int
    requires a != "" && IsDigitString(a)
    requires b != "" && IsDigitString(b)
  {
    if |a| < |b| then -1
    else if |a| > |b| then 1
    else
      if a == b then 0
      else
        FindFirstDifference(a, b, 0)
  }

  method MakeCanonical(s: string) returns (result: string)
    requires (|s| == 0 || (|s| > 0 && s[0] == '-' && (|s| == 1 || IsDigitString(s[1..]))) || (|s| > 0 && s[0] != '-' && IsDigitString(s)))
    ensures IsCanonical(result)
  {
    if s == "0" || s == "-0" {
      return "0";
    }
    if s == "" {
      return "0";
    }
    var has_minus := |s| > 0 && s[0] == '-';
    var abs_part := if has_minus then s[1..] else s;

    var j := 0;
    while j < |abs_part| && abs_part[j] == '0'
      decreases |abs_part| - j
    {
      j := j + 1;
    }

    if j >= |abs_part| {
      return "0";
    }

    abs_part := abs_part[j..];
    if has_minus {
      return "-" + abs_part;
    } else {
      return abs_part;
    }
  }

  function FindFirstDifference(a: string, b: string, idx: int): int
    requires |a| == |b|
    requires 0 <= idx <= |a|
    decreases |a| - idx
  {
    if idx == |a| then 0
    else if a[idx] < b[idx] then -1
    else if a[idx] > b[idx] then 1
    else FindFirstDifference(a, b, idx + 1)
  }

  method add_big(a: string, b: string) returns (s: string)
    requires IsCanonical(a)
    requires IsCanonical(b)
    ensures IsCanonical(s)
  {
    if a == "0" {
      return b;
    }
    if b == "0" {
      return a;
    }

    var a_negative := |a| > 0 && a[0] == '-';
    var b_negative := |b| > 0 && b[0] == '-';

    var a_abs := if a_negative then a[1..] else a;
    var b_abs := if b_negative then b[1..] else b;

    if a_negative == b_negative {
      if a_negative {
        CanonicalNegativeToAbsoluteDigitString(a);
        CanonicalNegativeToAbsoluteDigitString(b);
        assert a_abs != "" && IsDigitString(a_abs) && a_abs[0] != '0';
        assert b_abs != "" && IsDigitString(b_abs) && b_abs[0] != '0';
      } else {
        CanonicalNonZeroPositiveToDigitString(a);
        CanonicalNonZeroPositiveToDigitString(b);
        assert a_abs != "" && IsDigitString(a_abs) && a_abs[0] != '0';
        assert b_abs != "" && IsDigitString(b_abs) && b_abs[0] != '0';
      }

      var sum_abs := AddAbsolute(a_abs, b_abs);
      var result_str : string;
      if a_negative {
        result_str := "-" + sum_abs;
      } else {
        result_str := sum_abs;
      }
      var canonical_result := MakeCanonical(result_str);
      return canonical_result;
    } else {
      if a_negative {
        CanonicalNegativeToAbsoluteDigitString(a);
      } else {
        CanonicalNonZeroPositiveToDigitString(a);
      }
      if b_negative {
        CanonicalNegativeToAbsoluteDigitString(b);
      } else {
        CanonicalNonZeroPositiveToDigitString(b);
      }

      assert a_abs != "" && IsDigitString(a_abs) && a_abs[0] != '0';
      assert b_abs != "" && IsDigitString(b_abs) && b_abs[0] != '0';

      var cmp := CompareAbsoluteValues(a_abs, b_abs);
      var diff_abs: string;
      var is_negative: bool;

      if cmp >= 0 {
        diff_abs := SubtractAbsolute(a_abs, b_abs);
        is_negative := a_negative;
      } else {
        diff_abs := SubtractAbsolute(b_abs, a_abs);
        is_negative := b_negative;
      }

      var result_str := if is_negative then "-" + diff_abs else diff_abs;
      var canonical_result := MakeCanonical(result_str);
      return canonical_result;
    }
  }
}
