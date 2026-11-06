import Mathlib
open Real

theorem algebra_8192 (d : ℝ) (h : d > 0) (h1 : 450 / d = 350 / (1.5 * d)) (h2 : 350 / (1.5 * d) = 250 / (d - 250)) :
    d - 250 = 1100 := by
  have h4 : d ≠ 0 := by linarith
  field_simp [h4] at h1 h2 ⊢
  all_goals nlinarith