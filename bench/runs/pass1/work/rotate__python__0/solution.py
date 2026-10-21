def rotate(xs: list[int], k: int) -> list[int]:
    n = len(xs)
    if n == 0:
        return []
    k %= n
    return xs[n - k:] + xs[:n - k]
