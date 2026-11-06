import Mathlib

theorem algebra_192610 {p : ℝ} (hp : p = (21^3 - 11^3) / (21^2 + 21 * 11 + 11^2)) :
    p = 10 := by 
  rw [hp]
  norm_num