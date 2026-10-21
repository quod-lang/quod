from solution import utf8_valid

# Additional edge case tests
edge_cases = [
    # Boundary cases for valid ranges
    # U+007F (max single-byte): 7F
    ([0x7F], True, "Max single-byte U+007F"),

    # U+0080 (min 2-byte): C2 80
    ([0xC2, 0x80], True, "Min 2-byte U+0080"),

    # U+07FF (max 2-byte): DF BF
    ([0xDF, 0xBF], True, "Max 2-byte U+07FF"),

    # U+0800 (min 3-byte): E0 A0 80
    ([0xE0, 0xA0, 0x80], True, "Min 3-byte U+0800"),

    # U+FFFF (max before surrogates): EF BF BF (but not in surrogate range)
    ([0xEF, 0xBF, 0xBF], True, "Max before surrogates U+FFFF"),

    # U+10000 (min 4-byte): F0 90 80 80
    ([0xF0, 0x90, 0x80, 0x80], True, "Min 4-byte U+10000"),

    # U+10FFFF (max valid): F4 8F BF BF
    ([0xF4, 0x8F, 0xBF, 0xBF], True, "Max valid U+10FFFF"),

    # U+110000 (just over max): F4 90 80 80
    ([0xF4, 0x90, 0x80, 0x80], False, "Over max U+110000"),

    # Test all surrogate range boundaries
    ([0xED, 0x9F, 0xBF], True, "Just before surrogates U+D7FF"),
    ([0xED, 0xA0, 0x80], False, "Start of surrogates U+D800"),
    ([0xED, 0xBF, 0xBF], False, "End of surrogates U+DFFF"),
    ([0xEE, 0x80, 0x80], True, "Just after surrogates U+E000"),

    # Continuation bytes appearing separately
    ([0x80, 0x81, 0x82], False, "Multiple continuation bytes"),

    # Valid multi-byte at different positions
    ([0x7F, 0xC2, 0x80, 0xE0, 0xA0, 0x80], True, "Mixed single and multi-byte"),

    # Empty continuation (start byte not followed by required continuation)
    ([0xC2, 0x7F], False, "Non-continuation after 2-byte start"),
    ([0xE0, 0xA0, 0x7F], False, "ASCII in middle of 3-byte"),

    # All valid ASCII
    (list(range(0, 128)), True, "All ASCII characters"),
]

print("Running edge case tests...\n")
passed = 0
failed = 0

for input_bytes, expected, description in edge_cases:
    result = utf8_valid(input_bytes)
    status = "✓" if result == expected else "✗"

    if result == expected:
        passed += 1
    else:
        failed += 1

    print(f"{status} {description}")
    if result != expected:
        print(f"  Expected: {expected}, Got: {result}")

print(f"\n{passed} passed, {failed} failed")
