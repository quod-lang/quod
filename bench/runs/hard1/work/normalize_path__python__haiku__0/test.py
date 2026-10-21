from solution import normalize_path

test_cases = [
    # Basic cases
    ("/a/b/c", "/a/b/c"),
    ("a/b/c", "a/b/c"),

    # Single component
    ("/", "/"),
    (".", "."),
    ("a", "a"),
    ("/a", "/a"),

    # Empty and dots
    ("", "."),
    ("//", "/"),
    ("a//b", "a/b"),
    ("/a//b", "/a/b"),
    ("./a", "a"),
    ("a/.", "a"),
    ("a/./b", "a/b"),
    ("/./a", "/a"),

    # .. in absolute paths
    ("/a/b/..", "/a"),
    ("/a/b/../../c", "/c"),
    ("/a/b/../../../c", "/c"),
    ("/a/../b", "/b"),
    ("/../c", "/c"),
    ("/a/b/..", "/a"),

    # .. in relative paths
    ("a/b/..", "a"),
    ("a/b/../c", "a/c"),
    ("a/b/../../c", "../c"),
    ("a/b/../../../c", "../../c"),
    ("../a", "../a"),
    ("..", ".."),
    ("../../a", "../../a"),

    # Special names (not .. or .)
    ("a/...", "a/..."),
    ("a/.a", "a/.a"),
    (".a/b", ".a/b"),
    (".../..", ".."),

    # Trailing slashes
    ("a/b/", "a/b"),
    ("/a/b/", "/a/b"),

    # Complex cases
    ("a/./b/../c", "a/c"),
    ("/a/./b/../c", "/a/c"),
    ("a/b/c/../../d", "a/d"),
    ("/../a/b/c", "/a/b/c"),
]

print("Testing normalize_path:")
passed = 0
failed = 0

for input_path, expected in test_cases:
    result = normalize_path(input_path)
    status = "✓" if result == expected else "✗"
    if result == expected:
        passed += 1
    else:
        failed += 1
        print(f"{status} normalize_path('{input_path}')")
        print(f"  Expected: '{expected}'")
        print(f"  Got:      '{result}'")

print(f"\n{passed} passed, {failed} failed")
