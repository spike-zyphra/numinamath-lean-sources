import Mathlib

theorem calculus_11547 {a b v : Fin 3 → ℝ}
    (ha : a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 0)
    (hb : b 0 = 2 ∧ b 1 = 0 ∧ b 2 = -1)
    (h1 : crossProduct v a = crossProduct b a)
    (h2 : crossProduct v b = crossProduct a b) :
    v 0 = 3 ∧ v 1 = 1 ∧ v 2 = -1 := by

  rcases ha with ⟨ha0, ha1, ha2⟩
  rcases hb with ⟨hb0, hb1, hb2⟩
  have eq1 := congr_arg (λ x => x 0) h1
  have eq2 := congr_arg (λ x => x 1) h1
  have eq3 := congr_arg (λ x => x 2) h1

  have eq4 := congr_arg (λ x => x 0) h2
  have eq5 := congr_arg (λ x => x 1) h2
  have eq6 := congr_arg (λ x => x 2) h2

  simp [crossProduct, ha0, ha1, ha2, hb0, hb1, hb2] at eq1 eq2 eq3 eq4 eq5 eq6

  have hv0 : v 0 = 3 := by 
    linarith
  have hv1 : v 1 = 1 := by
    linarith
  have hv2 : v 2 = -1 := by
    linarith

  exact ⟨hv0, hv1, hv2⟩