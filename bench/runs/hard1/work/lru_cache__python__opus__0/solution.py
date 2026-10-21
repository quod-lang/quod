from collections import OrderedDict


def lru_cache(capacity: int, ops: list[tuple[int, int, int]]) -> list[int]:
    cache: OrderedDict[int, int] = OrderedDict()
    out: list[int] = []
    for kind, key, value in ops:
        if kind == 0:
            if key in cache:
                cache.move_to_end(key)
                out.append(cache[key])
            else:
                out.append(-1)
        else:
            if key in cache:
                cache.move_to_end(key)
            elif len(cache) >= capacity:
                cache.popitem(last=False)
            cache[key] = value
    return out
