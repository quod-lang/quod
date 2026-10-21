module Solution {
  predicate IsDigit(c: char) { '0' <= c <= '9' }

  predicate AllDigits(s: string) { forall i :: 0 <= i < |s| ==> IsDigit(s[i]) }

  predicate Canonical(s: string) {
    s == "0"
    || (|s| > 0 && AllDigits(s) && s[0] != '0')
    || (|s| > 1 && s[0] == '-' && AllDigits(s[1..]) && s[1] != '0')
  }

  function DigitsVal(s: string): nat
    requires AllDigits(s)
  {
    if |s| == 0 then 0
    else DigitsVal(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
  }

  function Val(s: string): int
    requires Canonical(s)
  {
    if s[0] == '-' then 0 - (DigitsVal(s[1..]) as int) else DigitsVal(s)
  }

  function Dig(d: nat): char
    requires d < 10
  {
    ('0' as int + d) as char
  }

  function NatStr(n: nat): string
    decreases n
  {
    if n < 10 then [Dig(n)] else NatStr(n / 10) + [Dig(n % 10)]
  }

  lemma NatStrProps(n: nat)
    ensures |NatStr(n)| > 0
    ensures AllDigits(NatStr(n))
    ensures n > 0 ==> NatStr(n)[0] != '0'
    ensures DigitsVal(NatStr(n)) == n
    decreases n
  {
    if n >= 10 {
      NatStrProps(n / 10);
      var s := NatStr(n);
      assert s[..|s|-1] == NatStr(n / 10);
    }
  }

  method ParseDigits(s: string) returns (n: nat)
    requires AllDigits(s)
    ensures n == DigitsVal(s)
  {
    n := 0;
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant n == DigitsVal(s[..i])
    {
      assert s[..i+1][..i] == s[..i];
      n := n * 10 + (s[i] as int - '0' as int);
      i := i + 1;
    }
    assert s[..|s|] == s;
  }

  method ToStr(n: nat) returns (s: string)
    ensures s == NatStr(n)
  {
    var m := n;
    s := [];
    while m >= 10
      invariant NatStr(m) + s == NatStr(n)
      decreases m
    {
      assert NatStr(m) == NatStr(m / 10) + [Dig(m % 10)];
      s := [Dig(m % 10)] + s;
      m := m / 10;
    }
    s := [Dig(m)] + s;
  }

  method add_big(a: string, b: string) returns (s: string)
    requires Canonical(a)
    requires Canonical(b)
    ensures Canonical(s)
    ensures Val(s) == Val(a) + Val(b)
  {
    var x: int;
    if a[0] == '-' {
      var t := ParseDigits(a[1..]);
      x := 0 - (t as int);
    } else {
      x := ParseDigits(a);
    }
    var y: int;
    if b[0] == '-' {
      var t := ParseDigits(b[1..]);
      y := 0 - (t as int);
    } else {
      y := ParseDigits(b);
    }
    var r := x + y;
    if r < 0 {
      var t := ToStr(-r);
      NatStrProps(-r);
      s := "-" + t;
      assert s[1..] == t;
    } else {
      s := ToStr(r);
      NatStrProps(r);
      if r == 0 { assert s == "0"; }
    }
  }
}
