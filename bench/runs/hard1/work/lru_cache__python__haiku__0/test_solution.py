from solution import lru_cache


def test_basic():
    # Test basic get and put
    capacity = 2
    ops = [
        (1, 1, 1),    # put(1, 1)
        (1, 2, 2),    # put(2, 2)
        (0, 1, 0),    # get(1) -> 1
        (0, 2, 0),    # get(2) -> 2
    ]
    assert lru_cache(capacity, ops) == [1, 2]
    print("✓ test_basic passed")


def test_eviction():
    # Test LRU eviction
    capacity = 2
    ops = [
        (1, 1, 1),    # put(1, 1), cache: {1: 1}
        (1, 2, 2),    # put(2, 2), cache: {1: 1, 2: 2}
        (0, 1, 0),    # get(1) -> 1, cache: {2: 2, 1: 1}
        (1, 3, 3),    # put(3, 3), evict 2 (LRU), cache: {1: 1, 3: 3}
        (0, 2, 0),    # get(2) -> -1 (not found)
    ]
    assert lru_cache(capacity, ops) == [1, -1]
    print("✓ test_eviction passed")


def test_update():
    # Test updating existing key
    capacity = 2
    ops = [
        (1, 1, 1),    # put(1, 1)
        (1, 2, 2),    # put(2, 2)
        (1, 1, 10),   # put(1, 10) - update, moves to end
        (1, 3, 3),    # put(3, 3) - evict 2, cache: {1: 10, 3: 3}
        (0, 1, 0),    # get(1) -> 10
        (0, 2, 0),    # get(2) -> -1
    ]
    assert lru_cache(capacity, ops) == [10, -1]
    print("✓ test_update passed")


def test_single_capacity():
    # Test with capacity 1
    capacity = 1
    ops = [
        (1, 1, 1),    # put(1, 1)
        (0, 1, 0),    # get(1) -> 1
        (1, 2, 2),    # put(2, 2) - evict 1
        (0, 1, 0),    # get(1) -> -1
        (0, 2, 0),    # get(2) -> 2
    ]
    assert lru_cache(capacity, ops) == [1, -1, 2]
    print("✓ test_single_capacity passed")


def test_get_nonexistent():
    # Test get on non-existent keys
    capacity = 2
    ops = [
        (0, 1, 0),    # get(1) -> -1
        (0, 2, 0),    # get(2) -> -1
        (1, 3, 3),    # put(3, 3)
        (0, 1, 0),    # get(1) -> -1
    ]
    assert lru_cache(capacity, ops) == [-1, -1, -1]
    print("✓ test_get_nonexistent passed")


def test_complex():
    # More complex scenario
    capacity = 3
    ops = [
        (1, 1, 1),    # put(1, 1): {1:1}
        (1, 2, 2),    # put(2, 2): {1:1, 2:2}
        (1, 3, 3),    # put(3, 3): {1:1, 2:2, 3:3}
        (0, 1, 0),    # get(1): {2:2, 3:3, 1:1}, result: [1]
        (1, 4, 4),    # put(4, 4): evict 2, {3:3, 1:1, 4:4}
        (0, 2, 0),    # get(2): -1
        (0, 3, 0),    # get(3): {1:1, 4:4, 3:3}, result: [1, -1, 3]
        (0, 4, 0),    # get(4): {1:1, 3:3, 4:4}, result: [1, -1, 3, 4]
        (0, 1, 0),    # get(1): {3:3, 4:4, 1:1}, result: [1, -1, 3, 4, 1]
    ]
    assert lru_cache(capacity, ops) == [1, -1, 3, 4, 1]
    print("✓ test_complex passed")


if __name__ == "__main__":
    test_basic()
    test_eviction()
    test_update()
    test_single_capacity()
    test_get_nonexistent()
    test_complex()
    print("\nAll tests passed! ✓")
