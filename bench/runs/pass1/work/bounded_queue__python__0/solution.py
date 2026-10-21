from collections import deque


def bounded_queue(capacity: int, ops: list[int]) -> list[int]:
    q = deque()
    out = []
    for x in ops:
        if x > 0:
            if len(q) >= capacity:
                q.popleft()
            q.append(x)
        else:
            out.append(q.popleft() if q else -1)
    return out
