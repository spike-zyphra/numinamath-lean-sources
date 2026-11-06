import Mathlib

open Real

theorem calculus_13899 : cos (5 * π / 4) = -1 / sqrt 2 := by
  have h1 : cos (5 * π / 4) = cos (π + (π / 4)) := by
    ring_nf
  rw [h1]
  have h2 : cos (π + (π / 4)) = - cos (π / 4) := by 
    rw [cos_add]
    simp [cos_pi, sin_pi]
    all_goals linarith
  rw [h2]
  have h3 : cos (π / 4) = Real.sqrt 2 / 2 := by 
    exact cos_pi_div_four
  rw [h3]
  have h4 : - (sqrt 2 / 2) = -1 / sqrt 2 := by 
    have h5 : sqrt 2 > 0 := Real.sqrt_pos.mpr (by linarith)
    field_simp 
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  exact h4