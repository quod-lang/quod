def rle_encode(xs: list[int]) -> list[tuple[int, int]]:
    result: list[tuple[int, int]] = []
    for x in xs:
        if result and result[-1][0] == x:
            result[-1] = (x, result[-1][1] + 1)
        else:
            result.append((x, 1))
    return result
