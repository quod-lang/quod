def topo_sort(n: int, edges: list[tuple[int, int]]) -> list[int]:
    import heapq

    # Deduplicate edges and build adjacency list and in-degree count
    adj = [[] for _ in range(n)]
    in_degree = [0] * n

    for u, v in set(edges):
        adj[u].append(v)
        in_degree[v] += 1

    # Initialize min-heap with all nodes that have in-degree 0
    heap = [i for i in range(n) if in_degree[i] == 0]
    heapq.heapify(heap)

    result = []

    # Process nodes using Kahn's algorithm with min-heap for lexicographic order
    while heap:
        u = heapq.heappop(heap)
        result.append(u)

        # Reduce in-degree of neighbors
        for v in adj[u]:
            in_degree[v] -= 1
            if in_degree[v] == 0:
                heapq.heappush(heap, v)

    # If not all nodes were processed, there's a cycle
    return result if len(result) == n else []
