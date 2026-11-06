import Mathlib

theorem algebra_2373 {a : ℚ} : 0 < a^2 + 1 := by
  have h1 : 0 ≤ a ^ 2 := by
    apply sq_nonneg
  linarith