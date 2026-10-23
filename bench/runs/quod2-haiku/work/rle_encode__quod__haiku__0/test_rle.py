from solution import rle_encode

# Test cases
print('Test 1 (empty):', rle_encode([]))
print('Test 2 (single):', rle_encode([1]))
print('Test 3 (same):', rle_encode([1, 1, 1]))
print('Test 4 (diff):', rle_encode([1, 2, 1]))
print('Test 5 (mixed):', rle_encode([1, 1, 2, 3, 3, 3]))
