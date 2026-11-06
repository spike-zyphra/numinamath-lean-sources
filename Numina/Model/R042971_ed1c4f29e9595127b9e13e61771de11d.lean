import Mathlib

open Real

theorem algebra_208462 : (4 - sqrt 6 + 2 * sqrt 3 - sqrt 2) / (sqrt 3 - sqrt 2 + 1) - sqrt 3 = 1 := by
  have h1 : sqrt 6 = sqrt 2 * sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h2 : sqrt 2 > 0 := by positivity
  have h3 : sqrt 3 > 0 := by positivity
  have h4 : sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h5 : sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h6 : sqrt 3 - sqrt 2 + 1 ≠ 0 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num : (2 : ℝ) > 0), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num : (3 : ℝ) > 0)]
  field_simp [h6, h1, Real.sq_sqrt, mul_comm]
  <;> nlinarith [mul_pos h2 h3, h4, h5, sq_nonneg (sqrt 3 - 2), sq_nonneg (sqrt 2 - 1),
          Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num : (2 : ℝ) > 0),
          Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num : (3 : ℝ) > 0),
          sq_nonneg (sqrt 3 ^ 2 - 3), sq_nonneg (sqrt 2 ^ 2 - 2)
        ]