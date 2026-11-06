import Mathlib

theorem inequalities_108911 (a : Fin 4 → ℝ) (ha : ∀ i, 1 < a i) :
    8 * (a 0 * a 1 * a 2 * a 3 + 1) ≥ (1 + a 0) * (1 + a 1) * (1 + a 2) * (1 + a 3) := by
  have ha0 : 1 < a 0 := ha 0
  have ha1 : 1 < a 1 := ha 1
  have ha2 : 1 < a 2 := ha 2
  have ha3 : 1 < a 3 := ha 3
  have h1 : 0 < a 0 - 1 := by linarith
  have h2 : 0 < a 1 - 1 := by linarith
  have h3 : 0 < a 2 - 1 := by linarith
  have h4 : 0 < a 3 - 1 := by linarith
  nlinarith [mul_pos (sub_pos.mpr ha0) (sub_pos.mpr ha1), 
          mul_pos (sub_pos.mpr ha0) (sub_pos.mpr ha2), 
          mul_pos (sub_pos.mpr ha0) (sub_pos.mpr ha3), 
          mul_pos (sub_pos.mpr ha1) (sub_pos.mpr ha2), 
          mul_pos (sub_pos.mpr ha1) (sub_pos.mpr ha3), 
          mul_pos (sub_pos.mpr ha2) (sub_pos.mpr ha3), 
          mul_pos (mul_pos (sub_pos.mpr ha0) (sub_pos.mpr ha1)) (mul_pos (sub_pos.mpr ha2) (sub_pos.mpr ha3))
          ]