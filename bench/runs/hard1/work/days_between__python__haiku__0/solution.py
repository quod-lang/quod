def days_between(y1: int, m1: int, d1: int, y2: int, m2: int, d2: int) -> int:
    def is_leap_year(year):
        if year % 400 == 0:
            return True
        if year % 100 == 0:
            return False
        if year % 4 == 0:
            return True
        return False

    def days_in_month(year, month):
        if month in [1, 3, 5, 7, 8, 10, 12]:
            return 31
        elif month in [4, 6, 9, 11]:
            return 30
        else:  # month == 2
            return 29 if is_leap_year(year) else 28

    def days_from_epoch(year, month, day):
        # Calculate days from year 1, Jan 1 (which is day 1)

        # Count leap years before this year using inclusion-exclusion
        y = year - 1
        leap_years = y // 4 - y // 100 + y // 400
        non_leap_years = y - leap_years
        total_days = leap_years * 366 + non_leap_years * 365

        # Add days for all complete months in this year
        for m in range(1, month):
            total_days += days_in_month(year, m)

        # Add the day of the month
        total_days += day

        return total_days

    days1 = days_from_epoch(y1, m1, d1)
    days2 = days_from_epoch(y2, m2, d2)

    return days2 - days1
