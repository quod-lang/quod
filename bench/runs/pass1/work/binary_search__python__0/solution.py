def binary_search(xs: list[int], target: int) -> int:
    lo, hi = 0, len(xs) - 1
    while lo <= hi:
        mid = (lo + hi) // 2
        v = xs[mid]
        if v == target:
            return mid
        if v < target:
            lo = mid + 1
        else:
            hi = mid - 1
    return -1
