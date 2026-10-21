from solution import add_big

def test_basic():
    assert add_big("5", "3") == "8"
    assert add_big("123", "456") == "579"
    assert add_big("0", "0") == "0"
    assert add_big("0", "5") == "5"
    assert add_big("5", "0") == "5"
    print("✓ Basic positive tests passed")

def test_negative():
    assert add_big("-5", "-3") == "-8"
    assert add_big("-123", "-456") == "-579"
    print("✓ Basic negative tests passed")

def test_mixed_signs():
    assert add_big("5", "-3") == "2"
    assert add_big("-5", "3") == "-2"
    assert add_big("10", "-5") == "5"
    assert add_big("-10", "5") == "-5"
    assert add_big("5", "-5") == "0"
    assert add_big("-5", "5") == "0"
    print("✓ Mixed sign tests passed")

def test_large_numbers():
    a = "123456789123456789"
    b = "987654321987654321"
    result = add_big(a, b)
    assert result == "1111111111111111110"
    print("✓ Large number tests passed")

def test_very_large_numbers():
    a = "9" * 100
    b = "1"
    result = add_big(a, b)
    expected = "1" + "0" * 100
    assert result == expected
    print("✓ Very large number tests passed")

def test_different_lengths():
    assert add_big("1", "9999") == "10000"
    assert add_big("9999", "1") == "10000"
    assert add_big("-1", "9999") == "9998"
    assert add_big("-9999", "1") == "-9998"
    print("✓ Different length tests passed")

def test_carry_propagation():
    assert add_big("999", "1") == "1000"
    assert add_big("999", "999") == "1998"
    assert add_big("-999", "-1") == "-1000"
    print("✓ Carry propagation tests passed")

def test_borrow_propagation():
    assert add_big("1000", "-1") == "999"
    assert add_big("1000", "-999") == "1"
    assert add_big("-1000", "1") == "-999"
    print("✓ Borrow propagation tests passed")

def test_zero_cases():
    assert add_big("0", "0") == "0"
    assert add_big("0", "-0") == "0"  # If -0 appears in input
    assert add_big("-0", "0") == "0"
    assert add_big("-0", "-0") == "0"
    print("✓ Zero cases passed")

def test_hundreds_of_digits():
    a = "1" + "0" * 500
    b = "2" + "0" * 500
    result = add_big(a, b)
    assert result == "3" + "0" * 500

    # Negative version
    result_neg = add_big("-" + a, "-" + b)
    assert result_neg == "-" + ("3" + "0" * 500)
    print("✓ Hundreds of digits tests passed")

if __name__ == "__main__":
    test_basic()
    test_negative()
    test_mixed_signs()
    test_large_numbers()
    test_very_large_numbers()
    test_different_lengths()
    test_carry_propagation()
    test_borrow_propagation()
    test_zero_cases()
    test_hundreds_of_digits()
    print("\n✅ All tests passed!")
