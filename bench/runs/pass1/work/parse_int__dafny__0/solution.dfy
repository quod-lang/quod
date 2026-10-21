module Solution {
  predicate IsDigit(c: char) {
    '0' <= c <= '9'
  }

  predicate AllDigits(s: string) {
    forall i :: 0 <= i < |s| ==> IsDigit(s[i])
  }

  function DigitsVal(s: string): int
    requires AllDigits(s)
  {
    if |s| == 0 then 0
    else DigitsVal(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
  }

  predicate HasSign(s: string) {
    |s| > 0 && (s[0] == '+' || s[0] == '-')
  }

  function Body(s: string): string {
    if HasSign(s) then s[1..] else s
  }

  predicate ValidSyntax(s: string) {
    |Body(s)| > 0 && AllDigits(Body(s))
  }

  function Value(s: string): int
    requires ValidSyntax(s)
  {
    if HasSign(s) && s[0] == '-' then -DigitsVal(Body(s)) else DigitsVal(Body(s))
  }

  predicate Valid(s: string) {
    ValidSyntax(s) && -2147483648 <= Value(s) <= 2147483647
  }

  method parse_int(s: string) returns (ok: bool, v: int)
    ensures ok <==> Valid(s)
    ensures ok ==> v == Value(s)
    ensures !ok ==> v == 0
  {
    var start := 0;
    var neg := false;
    if |s| > 0 && (s[0] == '+' || s[0] == '-') {
      start := 1;
      neg := s[0] == '-';
    }
    var body := s[start..];
    assert body == Body(s);
    if |body| == 0 {
      return false, 0;
    }
    var acc := 0;
    var i := 0;
    while i < |body|
      invariant 0 <= i <= |body|
      invariant AllDigits(body[..i])
      invariant acc == DigitsVal(body[..i])
    {
      if !('0' <= body[i] <= '9') {
        assert !AllDigits(body);
        return false, 0;
      }
      assert body[..i+1][..i] == body[..i];
      acc := acc * 10 + (body[i] as int - '0' as int);
      i := i + 1;
    }
    assert body[..i] == body;
    if neg {
      acc := -acc;
    }
    if -2147483648 <= acc <= 2147483647 {
      return true, acc;
    }
    return false, 0;
  }
}
