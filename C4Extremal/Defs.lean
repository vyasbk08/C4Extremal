module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace C4Extremal

def allPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2)

def IsGraph {n : ℕ} (E : Finset (Fin n × Fin n)) : Prop :=
  E ⊆ allPairs n

def adj {n : ℕ} (E : Finset (Fin n × Fin n)) (u v : Fin n) : Prop :=
  (u, v) ∈ E ∨ (v, u) ∈ E

def HasC4 {n : ℕ} (E : Finset (Fin n × Fin n)) : Prop :=
  ∃ a b c d : Fin n,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    adj E a b ∧ adj E b c ∧ adj E c d ∧ adj E d a

def C4Free {n : ℕ} (E : Finset (Fin n × Fin n)) : Prop :=
  ¬ HasC4 E

instance {n : ℕ} (E : Finset (Fin n × Fin n)) (u v : Fin n) :
    Decidable (adj E u v) := by
  unfold adj; infer_instance

instance {n : ℕ} (E : Finset (Fin n × Fin n)) : Decidable (HasC4 E) := by
  unfold HasC4; infer_instance

instance {n : ℕ} (E : Finset (Fin n × Fin n)) : Decidable (C4Free E) := by
  unfold C4Free; infer_instance

instance {n : ℕ} (E : Finset (Fin n × Fin n)) : Decidable (IsGraph E) := by
  unfold IsGraph; infer_instance

theorem adj_mono {n : ℕ} {E F : Finset (Fin n × Fin n)} (hEF : E ⊆ F)
    {u v : Fin n} (h : adj E u v) : adj F u v :=
  h.imp (fun hm => hEF hm) (fun hm => hEF hm)

theorem hasC4_mono {n : ℕ} {E F : Finset (Fin n × Fin n)} (hEF : E ⊆ F)
    (h : HasC4 E) : HasC4 F := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, e1, e2, e3, e4⟩ := h
  exact ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd,
    adj_mono hEF e1, adj_mono hEF e2, adj_mono hEF e3, adj_mono hEF e4⟩

def IsExtremal (n k : ℕ) : Prop :=
  (∃ E : Finset (Fin n × Fin n), IsGraph E ∧ C4Free E ∧ E.card = k) ∧
  (∀ E : Finset (Fin n × Fin n), IsGraph E → C4Free E → E.card ≤ k)

def maxCheck (n k : ℕ) : Prop :=
  ∀ E ∈ (allPairs n).powersetCard (k + 1), HasC4 E

instance {n k : ℕ} : Decidable (maxCheck n k) := by
  unfold maxCheck; infer_instance

theorem card_le_of_maxCheck {n k : ℕ} (hcheck : maxCheck n k) :
    ∀ E : Finset (Fin n × Fin n), IsGraph E → C4Free E → E.card ≤ k := by
  intro E hgraph hfree
  by_contra hcard
  rw [Nat.not_le] at hcard
  obtain ⟨F, hFE, hFcard⟩ := Finset.exists_subset_card_eq hcard
  have hF4 : HasC4 F :=
    hcheck F (Finset.mem_powersetCard.mpr ⟨hFE.trans hgraph, hFcard⟩)
  exact hfree (hasC4_mono hFE hF4)

theorem isExtremal_of {n k : ℕ} (E : Finset (Fin n × Fin n))
    (hwit : IsGraph E ∧ C4Free E ∧ E.card = k) (hcheck : maxCheck n k) :
    IsExtremal n k :=
  ⟨⟨E, hwit⟩, card_le_of_maxCheck hcheck⟩

end C4Extremal
