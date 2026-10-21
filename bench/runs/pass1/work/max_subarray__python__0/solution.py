def max_subarray(xs: list[int]) -> int:
    best = cur = xs[0]
    for x in xs[1:]:
        cur = max(x, cur + x)
        best = max(best, cur)
    return best
