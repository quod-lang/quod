import heapq


def topo_sort(n: int, edges: list[tuple[int, int]]) -> list[int]:
    adj = [set() for _ in range(n)]
    for u, v in edges:
        if u == v:
            return []
        adj[u].add(v)
    indeg = [0] * n
    for u in range(n):
        for v in adj[u]:
            indeg[v] += 1
    heap = [i for i in range(n) if indeg[i] == 0]
    heapq.heapify(heap)
    order = []
    while heap:
        u = heapq.heappop(heap)
        order.append(u)
        for v in adj[u]:
            indeg[v] -= 1
            if indeg[v] == 0:
                heapq.heappush(heap, v)
    return order if len(order) == n else []
