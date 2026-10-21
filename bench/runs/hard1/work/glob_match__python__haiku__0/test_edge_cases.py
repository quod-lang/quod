from solution import glob_match

print('Testing edge cases...')

# Empty cases
assert glob_match('', '') == True
assert glob_match('*', '') == True
assert glob_match('*', 'anything') == True
assert glob_match('a', '') == False
print('✓ Empty cases')

# Multiple wildcards
assert glob_match('*a*b*c*', 'abc') == True
assert glob_match('*a*b*c*', 'xaxbxcx') == True
assert glob_match('?*?', 'aa') == True
assert glob_match('?*?', 'a') == False
print('✓ Multiple wildcards')

# Complex escapes
assert glob_match('a' + '\\' + '\\' + '*', 'a' + '\\' + '*') == True
assert glob_match('a' + '\\' + '\\' + '?', 'a' + '\\' + 'x') == True
print('✓ Complex escapes')

# Special patterns
assert glob_match('a?b*c', 'axbxxxc') == True
assert glob_match('a?b*c', 'axbxxxcyyy') == False
assert glob_match('***', 'anything') == True
assert glob_match('???', 'abc') == True
assert glob_match('???', 'ab') == False
print('✓ Special patterns')

# Wildcards at different positions
assert glob_match('*abc', 'xyzabc') == True
assert glob_match('abc*', 'abcxyz') == True
assert glob_match('a*c', 'axyzc') == True
print('✓ Wildcards at different positions')

# Test with consecutive wildcards
assert glob_match('a**b', 'ab') == True
assert glob_match('a**b', 'axxxb') == True
assert glob_match('a**b', 'axxxbyyy') == False

# Test escaping special chars
assert glob_match('a' + '\\' + '?b', 'a?b') == True
assert glob_match('a' + '\\' + '*b', 'a*b') == True

print('✓ Consecutive wildcards and escaping')

print('\nAll edge case tests passed!')
