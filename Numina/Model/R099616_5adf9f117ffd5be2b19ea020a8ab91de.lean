import Mathlib

theorem algebra_106288 (x : ℝ) : (x - 4) * (x - 6) + 3 > 0 := by
  have h1 : (x - 4) * (x - 6) + 3 = (x - 5) ^ 2 + 2 := by 
    ring
  rw [h1]
  have h2 : (x - 5) ^ 2 ≥ 0 := by 
    apply sq_nonneg
  linarith