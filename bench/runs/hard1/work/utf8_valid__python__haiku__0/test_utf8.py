from solution import utf8_valid

# Test cases
test_cases = [
    # (input, expected_result, description)
    ([], True, "Empty list"),
    ([72], True, "Single ASCII 'H'"),
    ([72, 105], True, "ASCII 'Hi'"),
    ([0xC2, 0x80], True, "Valid 2-byte U+0080"),
    ([0xC3, 0xA9], True, "Valid 2-byte U+00E9 (é)"),
    ([0xE2, 0x82, 0xAC], True, "Valid 3-byte U+20AC (€)"),
    ([0xF0, 0x9F, 0x98, 0x80], True, "Valid 4-byte U+1F600 (😀)"),

    # Overlong encodings
    ([0xC0, 0x80], False, "Overlong encoding of U+0000"),
    ([0xC0, 0xA0], False, "Overlong encoding of U+0020"),
    ([0xE0, 0x80, 0x80], False, "Overlong encoding of U+0000 (3-byte)"),
    ([0xE0, 0x9F, 0xBF], False, "Overlong encoding (cp < 0x800)"),
    ([0xF0, 0x80, 0x80, 0x80], False, "Overlong encoding (cp < 0x10000)"),

    # Truncated sequences
    ([0xC2], False, "Incomplete 2-byte sequence"),
    ([0xE2, 0x82], False, "Incomplete 3-byte sequence"),
    ([0xF0, 0x9F, 0x98], False, "Incomplete 4-byte sequence"),

    # Invalid continuation bytes
    ([0xC2, 0x00], False, "Invalid second byte (not 10xxxxxx)"),
    ([0xC2, 0xC0], False, "Invalid second byte (starts with 11)"),
    ([0xE2, 0x82, 0x00], False, "Invalid third byte"),

    # Surrogate code points
    ([0xED, 0xA0, 0x80], False, "Surrogate U+D800"),
    ([0xED, 0xAF, 0xBF], False, "Surrogate U+DBFF"),
    ([0xED, 0xB0, 0x80], False, "Surrogate U+DC00"),
    ([0xED, 0xBF, 0xBF], False, "Surrogate U+DFFF"),

    # Code point > U+10FFFF
    ([0xF4, 0x90, 0x80, 0x80], False, "Code point U+110000 (too large)"),
    ([0xF5, 0x80, 0x80, 0x80], False, "Invalid start byte F5"),

    # Invalid start bytes
    ([0xFF], False, "Invalid start byte FF"),
    ([0xF8], False, "Invalid start byte F8"),

    # Continuation byte at start
    ([0x80], False, "Continuation byte at start"),
    ([0xBF], False, "Continuation byte at start"),

    # Mixed valid sequences
    ([72, 0xC3, 0xA9], True, "ASCII + 2-byte é"),
    ([0xE2, 0x82, 0xAC, 72], True, "3-byte € + ASCII"),
]

print("Running UTF-8 validation tests...\n")
passed = 0
failed = 0

for input_bytes, expected, description in test_cases:
    result = utf8_valid(input_bytes)
    status = "✓" if result == expected else "✗"

    if result == expected:
        passed += 1
    else:
        failed += 1

    print(f"{status} {description}")
    if result != expected:
        print(f"  Input: {input_bytes}")
        print(f"  Expected: {expected}, Got: {result}")

print(f"\n{passed} passed, {failed} failed")
