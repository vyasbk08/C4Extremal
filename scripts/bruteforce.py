"""Independent brute-force cross-check for the Lean results.

For each n, this script computes ex(n; C4): the maximum number of edges in a
graph on n labelled vertices that contains no 4-cycle (C4) as a subgraph.
It is deliberately written with no shared code or data with the Lean proofs,
so the two computations can be compared against each other.

Method: list all possible edges of the complete graph K_n, precompute every
4-cycle as a bitmask of 4 edge indices, then search subsets of edges by size.
A subset is C4-free iff it contains no complete 4-cycle mask. The maximum is
the largest s for which some C4-free subset of size s exists.

Run: python3 scripts/bruteforce.py
"""

from itertools import combinations


def edge_list(n):
    """All possible edges of K_n as sorted pairs (i, j) with i < j."""
    return [(i, j) for i in range(n) for j in range(i + 1, n)]


def cycle_masks(n, edge_index):
    """Every 4-cycle of K_n as a bitmask over edge indices.

    A set of 4 distinct vertices {a, b, c, d} supports exactly 3 different
    4-cycles, depending on which vertex is 'opposite' which: a-b-c-d-a,
    a-b-d-c-a, and a-c-b-d-a.
    """
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
    """A subset of edges is C4-free iff it contains no full cycle mask."""
    return all(subset_mask & m != m for m in masks)


def max_c4_free(n):
    """Largest s such that some C4-free subset of s edges exists, plus one witness."""
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
            break  # no C4-free set of size s, so none of any larger size either
        best, witness = s, found
    return best, witness


if __name__ == "__main__":
    for n in range(3, 8):
        best, witness = max_c4_free(n)
        print(f"n={n}: max C4-free edges = {best}, example: {witness}")
