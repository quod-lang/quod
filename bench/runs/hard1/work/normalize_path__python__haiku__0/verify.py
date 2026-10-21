from solution import normalize_path

cases = [
    ("/a/b/../c", "/a/c"),
    ("a/b/../../c", "../c"),
    ("a/b/..", "a"),
    ("/", "/"),
    (".", "."),
    ("", "."),
    ("/a/b/c", "/a/b/c"),
]

print("Verification of key cases:")
for input_path, expected in cases:
    result = normalize_path(input_path)
    status = "✓" if result == expected else "✗"
    print(f"{status} normalize_path('{input_path}') = '{result}' (expected '{expected}')")
