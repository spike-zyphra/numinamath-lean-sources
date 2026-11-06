import Mathlib

theorem algebra_180928 {x : ℝ} (hx : x = √3 - 1 ∨ x = √3 + 1) :
    x^4 - 8 * x^2 + 4 = 0 := by
  rcases hx with (rfl | rfl)
  · -- Case x = √3 - 1
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 by norm_num), pow_two_nonneg (√3 - 1), pow_two_nonneg (√3 + 1), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), sq_nonneg (√3 * √3 - 1)]
  · -- Case x = √3 + 1
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 by norm_num), pow_two_nonneg (√3 - 1), pow_two_nonneg (√3 + 1), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), sq_nonneg (√3 * √3 - 1)]