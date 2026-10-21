def merge_intervals(iv: list[tuple[int, int]]) -> list[tuple[int, int]]:
    result: list[tuple[int, int]] = []
    for a, b in sorted(iv):
        if result and a <= result[-1][1]:
            if b > result[-1][1]:
                result[-1] = (result[-1][0], b)
        else:
            result.append((a, b))
    return result
