from solution import justify

def test_basic():
    # Test basic justification
    words = ["This", "is", "an", "example", "of", "text", "justification."]
    width = 16
    result = justify(words, width)

    print("Test: Basic justification")
    print(f"Width: {width}")
    for line in result:
        print(f"'{line}' (len={len(line)})")

    # Verify each line has correct length
    for i, line in enumerate(result):
        assert len(line) == width, f"Line {i} has length {len(line)}, expected {width}"

    # Verify last line is left-justified
    last_line = result[-1]
    assert last_line == "justification.  ", f"Last line should be left-justified, got '{last_line}'"
    print("✓ Passed\n")

def test_single_word_per_line():
    # Test when words are large
    words = ["large", "word"]
    width = 6
    result = justify(words, width)

    print("Test: Single word lines")
    print(f"Width: {width}")
    for line in result:
        print(f"'{line}' (len={len(line)})")

    for i, line in enumerate(result):
        assert len(line) == width, f"Line {i} has length {len(line)}, expected {width}"
    print("✓ Passed\n")

def test_multiple_words_one_line():
    # Test multiple words that fit on one line
    words = ["hello", "world"]
    width = 11
    result = justify(words, width)

    print("Test: Multiple words on one line (last line)")
    print(f"Width: {width}")
    for line in result:
        print(f"'{line}' (len={len(line)})")

    assert len(result) == 1, f"Expected 1 line, got {len(result)}"
    assert len(result[0]) == width
    # Last line should be left-justified
    assert result[0] == "hello world", f"Expected 'hello world', got '{result[0]}'"
    print("✓ Passed\n")

def test_empty_list():
    # Test empty words list
    words = []
    width = 16
    result = justify(words, width)

    print("Test: Empty list")
    assert result == [], f"Expected empty list, got {result}"
    print("✓ Passed\n")

def test_single_word():
    # Test single word
    words = ["hello"]
    width = 10
    result = justify(words, width)

    print("Test: Single word")
    print(f"Width: {width}")
    for line in result:
        print(f"'{line}' (len={len(line)})")

    assert len(result) == 1
    assert len(result[0]) == width
    assert result[0] == "hello     "
    print("✓ Passed\n")

def test_complex_spacing():
    # Test complex spacing distribution (non-last line)
    words = ["a", "b", "c", "xx"]
    width = 7
    result = justify(words, width)

    print("Test: Complex spacing distribution")
    print(f"Width: {width}")
    for line in result:
        print(f"'{line}' (len={len(line)})")

    # First 3 words on line 1, "xx" on line 2
    assert len(result) == 2
    # First line (not last, multiple words):
    # a(1) + b(1) + c(1) = 3 chars
    # Spaces needed: 7 - 3 = 4
    # Gaps: 2
    # Spaces per gap: 4 // 2 = 2
    # Extra: 4 % 2 = 0
    # Result: "a  b  c"
    assert result[0] == "a  b  c", f"Expected 'a  b  c', got '{result[0]}'"
    # Last line: "xx     " (2 + 5 spaces = 7)
    assert result[1] == "xx     "
    print("✓ Passed\n")

def test_uneven_spacing():
    # Test uneven spacing distribution (extra spaces go left)
    words = ["a", "b", "c", "xxx"]
    width = 8
    result = justify(words, width)

    print("Test: Uneven spacing distribution")
    print(f"Width: {width}")
    for line in result:
        print(f"'{line}' (len={len(line)})")

    # First 3 words on line 1, "xxx" on line 2
    assert len(result) == 2
    # First line (not last, multiple words):
    # a(1) + b(1) + c(1) = 3 chars
    # Spaces needed: 8 - 3 = 5
    # Gaps: 2
    # Spaces per gap: 5 // 2 = 2
    # Extra: 5 % 2 = 1
    # First gap gets extra space: "a   b  c"
    assert result[0] == "a   b  c", f"Expected 'a   b  c', got '{result[0]}'"
    # Last line: "xxx     "
    assert result[1] == "xxx     "
    print("✓ Passed\n")

if __name__ == "__main__":
    test_basic()
    test_single_word_per_line()
    test_multiple_words_one_line()
    test_empty_list()
    test_single_word()
    test_complex_spacing()
    test_uneven_spacing()
    print("All tests passed! ✓")
