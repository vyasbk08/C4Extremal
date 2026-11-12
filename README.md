# C4Extremal

Maximum number of edges in a C4-free graph on n vertices, machine-checked in
Lean 4 for n ≤ 7.

A graph is **C4-free** if it contains no cycle on 4 distinct vertices
(no quadrilateral `a–b–c–d–a`). The extremal question — *how many edges can a
C4-free graph on n labelled vertices have?* — is a classical problem in
extremal graph theory (the Turán-type problem ex(n; C4)). This project proves
the answer for the smallest cases, formally, in Lean 4 with Mathlib:

| n | max edges | extremal example           | upper-bound proof method | trusted base    |
|---|-----------|----------------------------|--------------------------|-----------------|
| 3 | 3         | triangle                   | `decide`                 | Lean kernel     |
| 4 | 4         | triangle + pendant edge    | `decide`                 | Lean kernel     |
| 5 | 6         | two triangles sharing a vertex ("bowtie") | `decide` | Lean kernel     |
| 6 | 7         | bowtie + pendant edge      | `native_decide`          | Lean compiler ⚠ |
| 7 | 9         | three triangles sharing a vertex (friendship graph F₃) | `native_decide` | Lean compiler ⚠ |

The main theorems are `extremal3` … `extremal7` in
[`C4Extremal/SmallCases.lean`](C4Extremal/SmallCases.lean), each of the form
`IsExtremal n k`: *some* C4-free graph on n vertices has k edges, **and**
*every* C4-free graph on n vertices has at most k edges.

## How it works

- [`C4Extremal/Defs.lean`](C4Extremal/Defs.lean) defines graphs as finite
  sets of vertex pairs `(i, j)` with `i < j` over `Fin n`, the predicates
  `HasC4` / `C4Free`, and `Decidable` instances so the statements can be
  checked by computation. One short hand-written lemma
  (`card_le_of_maxCheck`) reduces the upper bound to a finite check: since
  adding edges never destroys a 4-cycle, it is enough to verify that **every
  edge set with exactly k+1 edges** contains a C4 — C(15,8) = 6 435 sets for
  n = 6 and C(21,10) = 352 716 sets for n = 7, instead of all 2¹⁵ / 2²¹
  subsets.
- [`C4Extremal/SmallCases.lean`](C4Extremal/SmallCases.lean) runs that check
  for each n and exhibits an explicit extremal graph.
- [`scripts/bruteforce.py`](scripts/bruteforce.py) is an independent Python
  brute force (different encoding, no shared code) that prints the same
  table, as a sanity cross-check: run `python3 scripts/bruteforce.py`.

## Trust: `decide` vs `native_decide`

- For **n = 3, 4, 5** the whole computation is replayed inside Lean's
  *kernel* — the small trusted core that checks every proof. `#print axioms`
  confirms these theorems use only the three standard axioms of Lean/Mathlib
  (`propext`, `Classical.choice`, `Quot.sound`).
- For **n = 6, 7** the search space is too large for the kernel, so the
  checks use `native_decide`, which compiles the check to native machine code
  and trusts the answer. These two theorems therefore also trust the **Lean
  compiler** (a much larger program than the kernel) — a strictly weaker
  guarantee: a compiler bug could, in principle, certify a false statement.
  `#print axioms` records this honestly: `extremal6` and `extremal7` depend
  on an extra `native_decide` axiom. The full audit output is kept in a
  comment at the bottom of `SmallCases.lean`.

## Building

```
lake exe cache get   # download the pre-built Mathlib binaries (~5 min)
lake build           # build the project (~4 min, dominated by the n=7 check)
```

Requires [elan](https://github.com/leanprover/elan); the exact Lean and
Mathlib versions are pinned by `lean-toolchain` (Lean v4.35.0) and
`lake-manifest.json` (Mathlib v4.35.0), so the build is reproducible.

## Motivation and scope

This is the toy version of the extremal problem targeted by Axiom Math's
open-source tool **Axplorer** (graphs with no 4-cycle and many edges). The
general asymptotics ex(n; C4) ~ ½·n^(3/2) (Kővári–Sós–Turán / Erdős–Rényi–Sós)
are far beyond this project.

**What is proved here:** exact values of ex(n; C4) for n = 3, 4, 5, 6, 7,
by exhaustive, machine-checked case analysis — nothing more. Raw enumeration
does not scale past this (n = 8 would need ~30 million subset checks), so
larger n would require genuinely different, theory-based proofs.

See [`LEARNING_NOTES.md`](LEARNING_NOTES.md) for a line-by-line beginner's
guide to the Lean syntax and tactics used.
