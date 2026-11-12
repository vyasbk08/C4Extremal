from itertools import combinations


def edge_list(n):
    return [(i, j) for i in range(n) for j in range(i + 1, n)]


def cycle_masks(n, edge_index):
    masks = []
    for a, b, c, d in combinations(range(n), 4):
        for p, q, r, s in [(a, b, c, d), (a, b, d, c), (a, c, b, d)]:
            cycle_edges = [(p, q), (q, r), (r, s), (s, p)]
            mask = 0
            for u, v in cycle_edges:
                mask |= 1 << edge_index[(min(u, v), max(u, v))]
            masks.append(mask)
    return masks


def is_c4_free(subset_mask, masks):
    return all(subset_mask & m != m for m in masks)


def max_c4_free(n):
    edges = edge_list(n)
    edge_index = {e: i for i, e in enumerate(edges)}
    masks = cycle_masks(n, edge_index)
    best, witness = 0, []
    for s in range(1, len(edges) + 1):
        found = None
        for combo in combinations(range(len(edges)), s):
            subset_mask = 0
            for i in combo:
                subset_mask |= 1 << i
            if is_c4_free(subset_mask, masks):
                found = [edges[i] for i in combo]
                break
        if found is None:
            break
        best, witness = s, found
    return best, witness


if __name__ == "__main__":
    for n in range(3, 8):
        best, witness = max_c4_free(n)
        print(f"n={n}: max C4-free edges = {best}, example: {witness}")
