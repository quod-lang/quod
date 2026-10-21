from solution import topo_sort

def test_cases():
    # Test 1: Simple linear ordering
    result = topo_sort(3, [(0, 1), (1, 2)])
    assert result == [0, 1, 2], f"Test 1 failed: {result}"
    print("✓ Test 1: Linear ordering")

    # Test 2: Cycle detection
    result = topo_sort(2, [(0, 1), (1, 0)])
    assert result == [], f"Test 2 failed: {result}"
    print("✓ Test 2: Cycle detection")

    # Test 3: Self-loop detection
    result = topo_sort(2, [(0, 0), (0, 1)])
    assert result == [], f"Test 3 failed: {result}"
    print("✓ Test 3: Self-loop detection")

    # Test 4: Duplicate edges
    result = topo_sort(3, [(0, 1), (0, 1), (1, 2)])
    assert result == [0, 1, 2], f"Test 4 failed: {result}"
    print("✓ Test 4: Duplicate edges")

    # Test 5: Lexicographically smallest (parallel nodes)
    result = topo_sort(4, [(0, 2), (1, 3)])
    assert result == [0, 1, 2, 3], f"Test 5 failed: {result}"
    print("✓ Test 5: Lexicographically smallest (parallel edges)")

    # Test 6: Lexicographically smallest (diamond shape)
    result = topo_sort(4, [(0, 1), (0, 2), (1, 3), (2, 3)])
    assert result == [0, 1, 2, 3], f"Test 6 failed: {result}"
    print("✓ Test 6: Diamond DAG")

    # Test 7: Single node
    result = topo_sort(1, [])
    assert result == [0], f"Test 7 failed: {result}"
    print("✓ Test 7: Single node")

    # Test 8: Multiple disconnected components (lexicographically smallest)
    result = topo_sort(5, [(0, 1), (2, 3)])
    assert result == [0, 1, 2, 3, 4], f"Test 8 failed: {result}"
    print("✓ Test 8: Disconnected components")

    # Test 9: Complex ordering
    result = topo_sort(5, [(1, 2), (1, 3), (0, 1), (2, 4), (3, 4)])
    assert result == [0, 1, 2, 3, 4], f"Test 9 failed: {result}"
    print("✓ Test 9: Complex ordering")

    # Test 10: Lexicographically smallest among multiple valid orderings
    # Graph: 1 -> 3, 2 -> 3, 0 is independent
    # Valid orderings include [0,1,2,3], [0,2,1,3], [1,0,2,3], [1,2,0,3], [2,0,1,3], [2,1,0,3]
    # Lexicographically smallest is [0,1,2,3]
    result = topo_sort(4, [(1, 3), (2, 3)])
    assert result == [0, 1, 2, 3], f"Test 10 failed: {result}"
    print("✓ Test 10: Lexicographically smallest among valid orderings")

    # Test 11: All edges from 0
    result = topo_sort(4, [(0, 1), (0, 2), (0, 3)])
    assert result == [0, 1, 2, 3], f"Test 11 failed: {result}"
    print("✓ Test 11: All edges from single node")

    # Test 12: No edges
    result = topo_sort(3, [])
    assert result == [0, 1, 2], f"Test 12 failed: {result}"
    print("✓ Test 12: No edges (all nodes independent)")

    print("\n✅ All tests passed!")

if __name__ == "__main__":
    test_cases()
