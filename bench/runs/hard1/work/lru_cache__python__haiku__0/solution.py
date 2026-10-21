from collections import OrderedDict


def lru_cache(capacity: int, ops: list[tuple[int, int, int]]) -> list[int]:
    cache = OrderedDict()
    result = []

    for kind, key, value in ops:
        if kind == 0:  # get
            if key in cache:
                cache.move_to_end(key)
                result.append(cache[key])
            else:
                result.append(-1)
        else:  # kind == 1, put
            if key in cache:
                cache[key] = value
                cache.move_to_end(key)
            else:
                if len(cache) >= capacity:
                    cache.popitem(last=False)
                cache[key] = value

    return result
