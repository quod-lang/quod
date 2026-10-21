from solution import justify

# Test case from problem description
words = ['This', 'is', 'an', 'example', 'of', 'text', 'justification.']
result = justify(words, 16)
print('Example from spec:')
for line in result:
    print(f'|{line}|')

# Verify all lines have width 16
for i, line in enumerate(result):
    print(f'Line {i}: length {len(line)}')

print()

# Test with 2 words per line
words = ['What', 'must', 'be', 'acknowledgment', 'shall', 'be']
result = justify(words, 16)
print('Test 2:')
for line in result:
    print(f'|{line}|')

for i, line in enumerate(result):
    print(f'Line {i}: length {len(line)}')
