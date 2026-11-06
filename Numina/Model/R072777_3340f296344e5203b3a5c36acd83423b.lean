import Mathlib

theorem algebra_8043 {x : ℝ} (hx : x = Real.sqrt 2) :
    (2 * x - 1) ^ 2 - (3 * x + 2) * (3 * x - 2) + (5 * x - 4) * (x + 2) = 2 * Real.sqrt 2 - 3 := by
  rw [hx]
  have h1 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [h1, Real.sqrt_nonneg 2, pow_two_nonneg (Real.sqrt 2), pow_two_nonneg (Real.sqrt 2 - 1), pow_two_nonneg (3 * Real.sqrt 2 + 2), pow_two_nonneg (5 * Real.sqrt 2 - 4)]