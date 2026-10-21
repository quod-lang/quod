module Solution {
  predicate IsLeap(y: int) {
    (y % 4 == 0 && y % 100 != 0) || y % 400 == 0
  }

  function YearLen(y: int): int {
    if IsLeap(y) then 366 else 365
  }

  function MonthLen(y: int, m: int): int {
    if m == 2 then (if IsLeap(y) then 29 else 28)
    else if m == 4 || m == 6 || m == 9 || m == 11 then 30
    else 31
  }

  predicate ValidDate(y: int, m: int, d: int) {
    1 <= y <= 9999 && 1 <= m <= 12 && 1 <= d <= MonthLen(y, m)
  }

  function DaysBeforeYear(y: int): int
    decreases y
  {
    if y <= 1 then 0 else DaysBeforeYear(y - 1) + YearLen(y - 1)
  }

  function DaysBeforeMonth(y: int, m: int): int
    decreases m
  {
    if m <= 1 then 0 else DaysBeforeMonth(y, m - 1) + MonthLen(y, m - 1)
  }

  function Ordinal(y: int, m: int, d: int): int {
    DaysBeforeYear(y) + DaysBeforeMonth(y, m) + d
  }

  method ComputeOrdinal(y: int, m: int, d: int) returns (r: int)
    requires ValidDate(y, m, d)
    ensures r == Ordinal(y, m, d)
  {
    var acc := 0;
    var i := 1;
    while i < y
      invariant 1 <= i <= y
      invariant acc == DaysBeforeYear(i)
      decreases y - i
    {
      acc := acc + YearLen(i);
      i := i + 1;
    }
    var j := 1;
    var macc := 0;
    while j < m
      invariant 1 <= j <= m
      invariant macc == DaysBeforeMonth(y, j)
      decreases m - j
    {
      macc := macc + MonthLen(y, j);
      j := j + 1;
    }
    r := acc + macc + d;
  }

  method days_between(y1: int, m1: int, d1: int, y2: int, m2: int, d2: int) returns (n: int)
    requires ValidDate(y1, m1, d1)
    requires ValidDate(y2, m2, d2)
    ensures n == Ordinal(y2, m2, d2) - Ordinal(y1, m1, d1)
  {
    var a := ComputeOrdinal(y1, m1, d1);
    var b := ComputeOrdinal(y2, m2, d2);
    n := b - a;
  }
}
