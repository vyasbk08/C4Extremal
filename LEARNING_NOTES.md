# Learning notes: a walkthrough for first-time Lean readers

These notes explain every piece of Lean syntax and every tactic used in this
project, in the order you would meet them reading `C4Extremal/Defs.lean` and
`C4Extremal/SmallCases.lean`.

## 1. The project layout

- `lakefile.toml` — the build configuration (like `pyproject.toml` for Python).
  It says the project depends on **Mathlib**, the community math library.
- `lean-toolchain` — pins the exact Lean compiler version, so the build is
  reproducible.
- `lake-manifest.json` — pins the exact commit of Mathlib (like a lock file).
- `C4Extremal.lean` — the root module; it just imports the real files.
- `C4Extremal/Defs.lean` — definitions and general lemmas.
- `C4Extremal/SmallCases.lean` — the machine-checked results for each `n`.

`lake build` compiles everything; if it succeeds with no `sorry`, every
theorem in the project is checked by Lean's kernel (except where
`native_decide` is used — see §7).

## 2. `module`, `public import`, `@[expose]`

Lean 4.35 has a "module system". The three lines at the top of each file —
`module`, `public import …`, `@[expose] public section` — just mean: this
file's definitions are visible to files that import it, and Lean is allowed
to unfold them during computation. Without `@[expose]`, the `decide` tactic
in `SmallCases.lean` could not evaluate `allPairs`, `HasC4`, etc.

## 3. Types used

- **`ℕ`** (`Nat`) — natural numbers 0, 1, 2, …
- **`Fin n`** — the type of natural numbers *less than `n`*. A value of
  `Fin 5` is one of 0, 1, 2, 3, 4. We use `Fin n` as our vertex type, so the
  type system itself guarantees that a vertex index is in range. It is a
  *finite* type, which is what makes exhaustive checking possible.
- **`Fin n × Fin n`** — pairs of vertices. `(1, 3) : Fin 5 × Fin 5` is the
  pair with first component 1 and second 3. We encode the undirected edge
  {1, 3} as the pair `(1, 3)` with the smaller endpoint first.
- **`Finset α`** — a *finite set* of elements of type `α`: unordered, no
  duplicates, and crucially *computable* (internally a duplicate-free list).
  Our graphs are `Finset (Fin n × Fin n)` — finite sets of edges.
  - `Finset.univ` — the finite set of **all** values of a finite type.
  - `s.filter p` — the subset of `s` where predicate `p` holds.
  - `s.card` — the number of elements.
  - `E ⊆ F` — every element of `E` is in `F`.
  - `Finset.powersetCard k s` — the set of all `k`-element subsets of `s`.
    This is how the upper-bound check says "for every way of choosing k+1
    edges…".
- **`Prop`** — the type of mathematical statements. A `def foo : Prop := …`
  defines a *statement*, which may be true or false; a `theorem` is a proof
  that a statement is true.

## 4. The definitions, in words

- `allPairs n` — all pairs `(i, j)` with `i < j`: the edges of the complete
  graph, i.e. every edge a graph on `n` vertices could possibly have.
- `IsGraph E` — `E ⊆ allPairs n`: all stored pairs are increasing, so `E` is
  a well-formed edge set.
- `adj E u v` — `u` and `v` are joined by an edge: `(u,v) ∈ E ∨ (v,u) ∈ E`.
  We must check both orders because edges are stored sorted.
- `HasC4 E` — "there exist four pairwise-distinct vertices `a b c d` with all
  four cycle edges present". In Lean, `∃ a b c d : Fin n, …` is an
  existential statement, and the six `≠`-conditions spell out distinctness.
- `C4Free E` — `¬ HasC4 E`.
- `maxCheck n k` — "every `(k+1)`-edge subset of `allPairs n` has a C4".
  This is the finite statement the computer checks exhaustively.
- `IsExtremal n k` — the actual theorem shape: *some* C4-free graph has `k`
  edges (lower bound) **and** *every* C4-free graph has at most `k` edges
  (upper bound).

## 5. Decidability: how `decide` can work at all

A proposition is **decidable** if there is an algorithm that answers
true/false. Lean tracks this with the `Decidable` typeclass. Our statements
are built from decidable pieces:

- membership in a `Finset` — decidable (walk the list);
- `∧`, `∨`, `¬`, `→`, `≠` of decidable statements — decidable;
- `∀ x : Fin n, …` and `∃ x : Fin n, …` over the *finite* type `Fin n` —
  decidable (try all `n` values).

The `instance … : Decidable …` declarations in `Defs.lean` just tell Lean
"unfold my definition and assemble the decision procedure from those pieces"
(`infer_instance` does the assembling).

The **`decide` tactic** then proves a decidable proposition by *running* the
decision procedure inside Lean's trusted kernel and checking that the answer
is `true`. No cleverness — pure exhaustive computation, but every step is
checked by the same small kernel that checks all other proofs.

## 6. The one human proof: `card_le_of_maxCheck`

Checking all subsets of all sizes would be wasteful. The project checks only
subsets of size exactly `k+1`, and a short hand-written argument covers the
rest:

1. Suppose some C4-free graph `E` had more than `k` edges (`by_contra`).
2. Pick any `k+1` of its edges (Mathlib's `Finset.exists_subset_card_eq`).
3. That selection is one of the sets `maxCheck` covered, so it contains a C4.
4. A C4 made of edges of a subset is also a C4 of `E` (`hasC4_mono`) —
   contradicting C4-freeness.

Tactics used there:

- `intro` — "let `E` be given, assume `hgraph`, `hfree`" (moves ∀/→ premises
  into the context).
- `by_contra hcard` — proof by contradiction: assume the negation.
- `rw [Nat.not_le] at hcard` — rewrite `¬ card ≤ k` into `k < card` using the
  library lemma `Nat.not_le : ¬a ≤ b ↔ b < a`.
- `obtain ⟨F, hFE, hFcard⟩ := …` — destructure an existence statement into a
  witness `F` and its properties.
- `exact` — "this term is exactly a proof of the goal".
- `⟨…, …⟩` (anonymous constructor) — builds a proof of an `∧` or `∃` from its
  parts.
- `h.imp f g` — on `h : P ∨ Q`, produces `P' ∨ Q'` by applying `f`/`g` to
  whichever side holds (used in `adj_mono`).

## 7. `decide` vs `decide +kernel` vs `native_decide`

- **`decide`** — evaluates the decision procedure in the elaborator, then the
  kernel re-checks the evaluation. Strongest guarantee; can be slow, and deep
  computations may need `set_option maxRecDepth` raised (that option only
  raises an artificial stack-depth limit; it adds no trust).
- **`decide +kernel`** — same trust story, but skips the elaborator pass and
  hands the computation straight to the kernel. Useful when the elaborator
  is the bottleneck.
- **`native_decide`** — compiles the decision procedure to native machine
  code and trusts the *compiler's* answer. The kernel does not re-check the
  computation; the proof depends on an extra axiom (shown by `#print axioms`
  as `maxCheckN._native.native_decide.ax_1_1` — a per-theorem wrapper for
  what older Lean versions showed as the global axiom `Lean.ofReduceBool`).
  A bug in the Lean compiler (a far larger program than the kernel) could in
  principle produce a wrong result. That is why `#print axioms` matters: it
  shows exactly which theorems carry this extra assumption.

In this project `#print axioms` output is recorded in comments at the bottom
of `SmallCases.lean`, and the README states which results are kernel-checked.

## 8. Five questions an interviewer might ask

**Q1. Why did you not use Mathlib's `SimpleGraph`?**
Because I wanted every statement to be decidable by construction so that
`decide` works. `SimpleGraph` is a general-purpose structure (adjacency as an
arbitrary symmetric relation); making the extremal statements computable over
it takes extra machinery (`Fintype`/`DecidableRel` instances, `≃` plumbing).
A `Finset` of sorted pairs is self-contained, and the whole trusted path from
definition to check fits in one small file I can explain completely.

**Q2. How do I know the Lean definition of "C4-free" is the right one?**
This is the real weak point of any formalization ("specification gap"), and I
mitigated it three ways: the definitions are short enough to audit by eye;
the lower-bound witnesses (triangle, bowtie, friendship-style graphs) are
known C4-free graphs and Lean confirms them; and an independent Python brute
force with a different encoding (bitmasks over edge indices, cycles
enumerated per 4-subset of vertices) produces the same numbers.

**Q3. What exactly does `decide` prove, and what is trusted?**
`decide` reduces the proposition's decision procedure to `true` *inside the
kernel*, the ~10k-line core that checks all Lean proofs. So the trusted base
is: the kernel, and the faithfulness of my definitions. For `native_decide`
(used only for the n=6 and n=7 upper bounds here) the compiler and runtime
are also trusted, which is why those theorems are flagged separately.

**Q4. Why check only subsets of size exactly k+1 for the upper bound?**
Monotonicity. Adding edges never destroys a 4-cycle (`hasC4_mono`), so if
every (k+1)-edge set has a C4, every larger set does too — any larger set
contains a (k+1)-subset. This shrinks the n=6 check from 2^15 = 32768 subsets
to C(15,8) = 6435, and makes n=7 feasible at all (C(21,10) = 352716 instead
of 2^21 = 2097152). The reduction is itself a Lean theorem
(`card_le_of_maxCheck`), not a meta-level argument.

**Q5. Where does this stop scaling, and what would you do next?**
The number of (k+1)-subsets explodes: n=8 (k=11) needs C(28,12) ≈ 30 million
HasC4-checks, and n=10 is hopeless by raw enumeration. Real progress needs
graph-theoretic pruning (degree bounds, counting paths of length 2 — the
classical Kővári–Sós–Turán argument gives ex(n; C4) ≤ ½(1 + √(4n−3))·n/2) or
verified search with symmetry reduction. Formalizing the counting argument in
Lean would be the natural next project; this one is the honest brute-force
baseline.

## 9. Glossary of symbols

| Symbol | Meaning |
|---|---|
| `ℕ` | natural numbers |
| `×` | pair / product type |
| `∈`, `⊆` | membership, subset |
| `∃ x, P x` | "there exists x with P x" |
| `∀ x, P x` | "for all x, P x" |
| `∧`, `∨`, `¬` | and, or, not |
| `≠` | not equal |
| `→` | implies (between Props); function arrow (between types) |
| `⟨a, b, c⟩` | build a proof/value of a structure from parts |
| `#eval e` | run `e` and print the result |
| `#print axioms t` | list the axioms theorem `t` depends on |
