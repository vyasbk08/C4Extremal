/-
# Definitions: graphs on `Fin n` and the C4-free property

We represent a graph on the vertex set `Fin n = {0, 1, ..., n-1}` as a
`Finset` (finite set) of pairs `(i, j)` with `i < j`.  Storing each edge
exactly once, with its smaller endpoint first, avoids double-counting:
the edge between 1 and 3 is the pair `(1, 3)` and never `(3, 1)`.

Everything here is kept elementary on purpose (no `SimpleGraph` from
Mathlib), so that every proposition is *decidable*: Lean can evaluate it
to `true` or `false` by exhaustive computation, which is what the
`decide` tactic does in `SmallCases.lean`.
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Prod

/-
`@[expose] public section` makes every definition below visible to files
that import this one *and* lets Lean unfold them during computation —
which the `decide` tactic in SmallCases.lean needs.
-/
@[expose] public section

namespace C4Extremal

/-- The set of all possible edges on `n` vertices: every pair `(i, j)` of
vertices with `i < j`.  This is the edge set of the complete graph `K_n`,
and every graph we consider is a subset of it.
`Finset.univ` is the finite set of *all* pairs of vertices, and `filter`
keeps only the increasing ones. -/
def allPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2)

/-- An edge set is a (well-formed) graph when every stored pair is
increasing, i.e. it is a subset of `allPairs n`. -/
def IsGraph {n : ℕ} (E : Finset (Fin n × Fin n)) : Prop :=
  E ⊆ allPairs n

/-- `adj E u v`: vertices `u` and `v` are adjacent in the edge set `E`.
Edges are *unordered*, but we store them with the smaller endpoint first,
so we must check both orderings of the pair. -/
def adj {n : ℕ} (E : Finset (Fin n × Fin n)) (u v : Fin n) : Prop :=
  (u, v) ∈ E ∨ (v, u) ∈ E

/-- `HasC4 E`: the edge set `E` contains a 4-cycle, i.e. there are four
*distinct* vertices `a, b, c, d` such that the four edges `ab`, `bc`,
`cd`, `da` are all present.  The six `≠` conditions say exactly that the
four vertices are pairwise distinct. -/
def HasC4 {n : ℕ} (E : Finset (Fin n × Fin n)) : Prop :=
  ∃ a b c d : Fin n,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    adj E a b ∧ adj E b c ∧ adj E c d ∧ adj E d a

/-- `C4Free E`: the edge set `E` contains no 4-cycle. -/
def C4Free {n : ℕ} (E : Finset (Fin n × Fin n)) : Prop :=
  ¬ HasC4 E

/-!
## Decidability

`decide` only works on propositions Lean can compute.  Each instance
below just unfolds our definition and lets Lean assemble the decision
procedure from built-in pieces: membership in a `Finset` is decidable,
`∨`, `∧`, `¬`, `≠` of decidable things are decidable, and a `∃` over the
*finite* type `Fin n` is decidable by trying all values.
-/

instance {n : ℕ} (E : Finset (Fin n × Fin n)) (u v : Fin n) :
    Decidable (adj E u v) := by
  unfold adj; infer_instance

instance {n : ℕ} (E : Finset (Fin n × Fin n)) : Decidable (HasC4 E) := by
  unfold HasC4; infer_instance

instance {n : ℕ} (E : Finset (Fin n × Fin n)) : Decidable (C4Free E) := by
  unfold C4Free; infer_instance

instance {n : ℕ} (E : Finset (Fin n × Fin n)) : Decidable (IsGraph E) := by
  unfold IsGraph; infer_instance

/-!
## Monotonicity: more edges can only create 4-cycles

These two small hand-written proofs let us check the upper bound by
brute force over subsets of size exactly `k + 1` instead of *all*
subsets: any larger edge set contains a `(k+1)`-subset, and a 4-cycle in
a subset is still a 4-cycle in the whole set.
-/

/-- If `u` and `v` are adjacent in `E` and `E ⊆ F`, they are adjacent in
`F`: the witnessing pair is still a member of the bigger set. -/
theorem adj_mono {n : ℕ} {E F : Finset (Fin n × Fin n)} (hEF : E ⊆ F)
    {u v : Fin n} (h : adj E u v) : adj F u v :=
  h.imp (fun hm => hEF hm) (fun hm => hEF hm)

/-- A 4-cycle survives when edges are added: if `E ⊆ F` and `E` has a
4-cycle, so does `F`.  The proof takes the four vertices witnessing the
cycle in `E` and reuses them for `F`. -/
theorem hasC4_mono {n : ℕ} {E F : Finset (Fin n × Fin n)} (hEF : E ⊆ F)
    (h : HasC4 E) : HasC4 F := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, e1, e2, e3, e4⟩ := h
  exact ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd,
    adj_mono hEF e1, adj_mono hEF e2, adj_mono hEF e3, adj_mono hEF e4⟩

/-!
## The extremal statement and the bridge lemma
-/

/-- `IsExtremal n k`: `k` is *the* maximum number of edges of a C4-free
graph on `n` vertices.  Two halves:
* **lower bound** — some C4-free graph achieves `k` edges, and
* **upper bound** — every C4-free graph has at most `k` edges. -/
def IsExtremal (n k : ℕ) : Prop :=
  (∃ E : Finset (Fin n × Fin n), IsGraph E ∧ C4Free E ∧ E.card = k) ∧
  (∀ E : Finset (Fin n × Fin n), IsGraph E → C4Free E → E.card ≤ k)

/-- The brute-force upper-bound check that `decide` evaluates:
**every** edge set with exactly `k + 1` edges contains a 4-cycle.
`Finset.powersetCard (k+1) (allPairs n)` is the finite set of all
`(k+1)`-element subsets of the possible edges, so this is a finite
conjunction that Lean can compute. -/
def maxCheck (n k : ℕ) : Prop :=
  ∀ E ∈ (allPairs n).powersetCard (k + 1), HasC4 E

instance {n k : ℕ} : Decidable (maxCheck n k) := by
  unfold maxCheck; infer_instance

/-- **Bridge lemma**: the finite check `maxCheck n k` really does give the
upper bound `card ≤ k` for every C4-free graph.

Proof idea (by contradiction): if a C4-free graph `E` had more than `k`
edges, we could pick any `k + 1` of its edges (Mathlib's
`Finset.exists_subset_card_eq`).  That sub-edge-set appears in the
brute-force check, so it has a 4-cycle; by `hasC4_mono` the 4-cycle is
also in `E`, contradicting C4-freeness. -/
theorem card_le_of_maxCheck {n k : ℕ} (hcheck : maxCheck n k) :
    ∀ E : Finset (Fin n × Fin n), IsGraph E → C4Free E → E.card ≤ k := by
  intro E hgraph hfree
  by_contra hcard
  rw [Nat.not_le] at hcard
  -- `hcard : k < E.card`, so `E` has at least `k + 1` edges;
  -- pick a sub-edge-set `F ⊆ E` with exactly `k + 1` edges.
  obtain ⟨F, hFE, hFcard⟩ := Finset.exists_subset_card_eq hcard
  -- `F` is one of the sets covered by the brute-force check, so it has a C4...
  have hF4 : HasC4 F :=
    hcheck F (Finset.mem_powersetCard.mpr ⟨hFE.trans hgraph, hFcard⟩)
  -- ...and the C4 survives in the larger set `E`.  Contradiction.
  exact hfree (hasC4_mono hFE hF4)

/-- Convenient packaging: an explicit witness plus the finite check give
the full extremal statement. -/
theorem isExtremal_of {n k : ℕ} (E : Finset (Fin n × Fin n))
    (hwit : IsGraph E ∧ C4Free E ∧ E.card = k) (hcheck : maxCheck n k) :
    IsExtremal n k :=
  ⟨⟨E, hwit⟩, card_le_of_maxCheck hcheck⟩

end C4Extremal
