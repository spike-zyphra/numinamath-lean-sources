import Mathlib

theorem algebra_2435
  (a : ℚ) : (0 < (a - 1993)^2 + 0.001) := by 
  have h2 : (0 : ℚ) ≤ (a - 1993)^2 := by 
    apply sq_nonneg
  linarith [h2, show 0 < (0.001 : ℚ) by norm_num]