module Solution {

predicate is_leap_year(y: int) {
    (y % 4 == 0 && y % 100 != 0) || (y % 400 == 0)
}

function days_in_month(y: int, m: int): int {
    if m == 1 then 31
    else if m == 2 then if is_leap_year(y) then 29 else 28
    else if m == 3 then 31
    else if m == 4 then 30
    else if m == 5 then 31
    else if m == 6 then 30
    else if m == 7 then 31
    else if m == 8 then 31
    else if m == 9 then 30
    else if m == 10 then 31
    else if m == 11 then 30
    else if m == 12 then 31
    else 0
}

function sum_days_before_month(y: int, m: int): int
  requires 1 <= m <= 13
  decreases m - 1
{
  if m <= 1 then 0
  else days_in_month(y, m - 1) + sum_days_before_month(y, m - 1)
}

function days_since_epoch(y: int, m: int, d: int): int
  requires 1 <= y <= 9999
  requires 1 <= m <= 12
  requires 1 <= d <= days_in_month(y, m)
{
  var days_from_years := (y - 1) * 365 + ((y - 1) / 4) - ((y - 1) / 100) + ((y - 1) / 400);
  var days_from_months := sum_days_before_month(y, m);
  days_from_years + days_from_months + d - 1
}

method days_between(y1: int, m1: int, d1: int, y2: int, m2: int, d2: int) returns (n: int)
  requires 1 <= y1 <= 9999
  requires 1 <= m1 <= 12
  requires 1 <= d1 <= days_in_month(y1, m1)
  requires 1 <= y2 <= 9999
  requires 1 <= m2 <= 12
  requires 1 <= d2 <= days_in_month(y2, m2)
  ensures n == days_since_epoch(y2, m2, d2) - days_since_epoch(y1, m1, d1)
{
  var epoch1 := days_since_epoch(y1, m1, d1);
  var epoch2 := days_since_epoch(y2, m2, d2);
  n := epoch2 - epoch1;
}

}
