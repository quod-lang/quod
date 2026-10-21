from solution import days_between
from datetime import date

def test_against_datetime():
    test_cases = [
        # (y1, m1, d1, y2, m2, d2)
        (2000, 1, 1, 2000, 12, 31),
        (2000, 2, 28, 2000, 3, 1),  # leap year boundary
        (1900, 2, 28, 1900, 3, 1),  # non-leap century
        (2000, 1, 1, 2001, 1, 1),   # year 2000 is leap
        (1999, 1, 1, 2000, 1, 1),   # year 1999 is non-leap
        (2024, 6, 15, 2024, 12, 25),
        (1, 1, 1, 1, 12, 31),
        (1, 1, 1, 100, 1, 1),
    ]

    for y1, m1, d1, y2, m2, d2 in test_cases:
        try:
            d1_obj = date(y1, m1, d1)
            d2_obj = date(y2, m2, d2)
            expected = (d2_obj - d1_obj).days
            result = days_between(y1, m1, d1, y2, m2, d2)
            status = "✓" if result == expected else "✗"
            print(f"{status} ({y1}-{m1:02d}-{d1:02d}) to ({y2}-{m2:02d}-{d2:02d}): {result} (expected {expected})")
            assert result == expected, f"Mismatch: got {result}, expected {expected}"
        except ValueError as e:
            print(f"⚠ Skipped {y1}-{m1}-{d1} to {y2}-{m2}-{d2}: {e}")

    print("\n✅ All datetime verifications passed!")

if __name__ == "__main__":
    test_against_datetime()
