import Mathlib
theorem algebra_9122 {a : ℝ} : a^2 - 6 = (a + Real.sqrt 6) * (a - Real.sqrt 6) := by
  nlinarith [Real.sq_sqrt (by norm_num : (6 : ℝ) ≥ 0), Real.sqrt_nonneg 6]