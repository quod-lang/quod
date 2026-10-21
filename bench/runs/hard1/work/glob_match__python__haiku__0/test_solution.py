from solution import glob_match

# Test basic literal matching
assert glob_match("abc", "abc") == True
assert glob_match("abc", "abd") == False
assert glob_match("", "") == True

# Test ? (single character wildcard)
assert glob_match("a?c", "abc") == True
assert glob_match("a?c", "ac") == False
assert glob_match("a?c", "abbc") == False
assert glob_match("?", "a") == True
assert glob_match("?", "") == False

# Test * (any sequence wildcard)
assert glob_match("a*b", "ab") == True
assert glob_match("a*b", "axxxb") == True
assert glob_match("a*b", "axxxbyyy") == False
assert glob_match("*", "") == True
assert glob_match("*", "anything") == True
assert glob_match("a*", "a") == True
assert glob_match("a*", "abc") == True
assert glob_match("*b", "b") == True
assert glob_match("*b", "abc") == False

# Test escape sequences
assert glob_match(r"a\*b", "a*b") == True
assert glob_match(r"a\*b", "axxxb") == False
assert glob_match(r"a\?b", "a?b") == True
assert glob_match(r"a\?b", "axb") == False

# Test escaped backslash
assert glob_match(r"a\\b", "a\\b") == True
assert glob_match(r"a\\b", r"a\b") == True
assert glob_match(r"a\\b", r"a\\b") == False

# Test lone backslash at end
assert glob_match("a" + "\\", "a" + "\\") == True
assert glob_match("a\\", "a") == False

# Test combination of operators
assert glob_match("a*b?c", "axyzbxc") == True
assert glob_match("a*b?c", "abc") == False
assert glob_match("a*b*c", "axyzbc") == True
assert glob_match("*a*b*c*", "aabbcc") == True
assert glob_match("*a*b*c*", "xyz") == False

# Test complex patterns
assert glob_match("a*.txt", "abc.txt") == True
assert glob_match("a*.txt", "abc.py") == False
assert glob_match("*.txt", "file.txt") == True
assert glob_match("*.txt", "file.txt.bak") == False
assert glob_match("*.txt", ".txt") == True

# Test multiple wildcards
assert glob_match("a*b*c", "axxxbyyc") == True
assert glob_match("a*b*c", "abc") == True
assert glob_match("a*b*c", "ac") == False

# Test edge cases with backslash
assert glob_match("\\" + "\\", "\\") == True
assert glob_match(r"a\\b", r"a\b") == True

print("All tests passed!")
