module

public import C4Extremal.Defs
meta import C4Extremal.Defs

@[expose] public section

namespace C4Extremal

def edges3 : Finset (Fin 3 × Fin 3) := {(0, 1), (0, 2), (1, 2)}

theorem edges3_spec : IsGraph edges3 ∧ C4Free edges3 ∧ edges3.card = 3 := by
  decide

theorem maxCheck3 : maxCheck 3 3 := by decide

theorem extremal3 : IsExtremal 3 3 := isExtremal_of edges3 edges3_spec maxCheck3

def edges4 : Finset (Fin 4 × Fin 4) := {(0, 1), (0, 2), (0, 3), (1, 2)}

theorem edges4_spec : IsGraph edges4 ∧ C4Free edges4 ∧ edges4.card = 4 := by
  decide

theorem maxCheck4 : maxCheck 4 4 := by decide

theorem extremal4 : IsExtremal 4 4 := isExtremal_of edges4 edges4_spec maxCheck4

def edges5 : Finset (Fin 5 × Fin 5) :=
  {(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)}

theorem edges5_spec : IsGraph edges5 ∧ C4Free edges5 ∧ edges5.card = 6 := by
  decide

set_option maxRecDepth 100000 in
theorem maxCheck5 : maxCheck 5 6 := by decide

theorem extremal5 : IsExtremal 5 6 := isExtremal_of edges5 edges5_spec maxCheck5

def edges6 : Finset (Fin 6 × Fin 6) :=
  {(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)}

theorem edges6_spec : IsGraph edges6 ∧ C4Free edges6 ∧ edges6.card = 7 := by
  decide

set_option linter.style.native false in
theorem maxCheck6 : maxCheck 6 7 := by native_decide

theorem extremal6 : IsExtremal 6 7 := isExtremal_of edges6 edges6_spec maxCheck6

def edges7 : Finset (Fin 7 × Fin 7) :=
  {(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (3, 4), (5, 6)}

set_option maxRecDepth 100000 in
theorem edges7_spec : IsGraph edges7 ∧ C4Free edges7 ∧ edges7.card = 9 := by
  decide

set_option linter.style.native false in
theorem maxCheck7 : maxCheck 7 9 := by native_decide

theorem extremal7 : IsExtremal 7 9 := isExtremal_of edges7 edges7_spec maxCheck7

#print axioms extremal3
#print axioms extremal4
#print axioms extremal5
#print axioms extremal6
#print axioms extremal7

end C4Extremal
