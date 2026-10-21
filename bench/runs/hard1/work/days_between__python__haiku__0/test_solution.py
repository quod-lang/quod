from solution import days_between

def test_same_date():
    assert days_between(1, 1, 1, 1, 1, 1) == 0, "Same date should return 0"
    print("✓ Same date")

def test_one_day_apart():
    assert days_between(1, 1, 1, 1, 1, 2) == 1, "One day apart should return 1"
    assert days_between(1, 1, 2, 1, 1, 1) == -1, "Earlier date should return negative"
    print("✓ One day apart")

def test_month_boundary():
    # January has 31 days, so Jan 31 to Feb 1 is 1 day
    assert days_between(1, 1, 31, 1, 2, 1) == 1, "End of month transition"
    print("✓ Month boundary")

def test_year_boundary_non_leap():
    # Year 1 is not a leap year (not divisible by 4)
    # So year 1 has 365 days
    assert days_between(1, 1, 1, 2, 1, 1) == 365, "Year 1 to Year 2 (non-leap)"
    print("✓ Year boundary (non-leap)")

def test_year_boundary_leap():
    # Year 4 is a leap year (divisible by 4, not by 100)
    # So year 4 has 366 days
    assert days_between(4, 1, 1, 5, 1, 1) == 366, "Year 4 to Year 5 (leap year)"
    print("✓ Year boundary (leap year)")

def test_century_non_leap():
    # Year 100 is NOT a leap year (divisible by 100, not by 400)
    # So year 100 has 365 days
    assert days_between(100, 1, 1, 101, 1, 1) == 365, "Year 100 is not a leap year"
    print("✓ Century non-leap")

def test_century_leap():
    # Year 400 is a leap year (divisible by 400)
    # So year 400 has 366 days
    assert days_between(400, 1, 1, 401, 1, 1) == 366, "Year 400 is a leap year"
    print("✓ Century leap")

def test_leap_year_february():
    # Year 4 is a leap year, so February has 29 days
    assert days_between(4, 2, 1, 4, 3, 1) == 29, "February in leap year has 29 days"
    print("✓ Leap year February")

def test_non_leap_year_february():
    # Year 1 is not a leap year, so February has 28 days
    assert days_between(1, 2, 1, 1, 3, 1) == 28, "February in non-leap year has 28 days"
    print("✓ Non-leap year February")

def test_multi_year_span():
    # From Jan 1, Year 1 to Dec 31, Year 1
    # Year 1 has 365 days, so Dec 31 is 364 days after Jan 1
    assert days_between(1, 1, 1, 1, 12, 31) == 364, "Full year minus 1 day"
    print("✓ Multi-month span")

def test_negative_difference():
    # Earlier date to later date is negative
    assert days_between(2, 1, 1, 1, 1, 1) == -365, "Earlier year should be negative"
    print("✓ Negative difference")

if __name__ == "__main__":
    test_same_date()
    test_one_day_apart()
    test_month_boundary()
    test_year_boundary_non_leap()
    test_year_boundary_leap()
    test_century_non_leap()
    test_century_leap()
    test_leap_year_february()
    test_non_leap_year_february()
    test_multi_year_span()
    test_negative_difference()
    print("\n✅ All tests passed!")
