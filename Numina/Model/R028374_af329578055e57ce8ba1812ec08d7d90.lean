import Mathlib

theorem algebra_92940 : (Real.sqrt 3 - Real.sqrt 2) / Real.sqrt 3 = 1 / (3 + Real.sqrt 6) := by
  have h1 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num]
    rw [Real.sqrt_mul]
    all_goals linarith
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := h1
  field_simp [(show Real.sqrt 3 ≠ 0 by positivity), (show 3 + Real.sqrt 6 ≠ 0 by positivity)]
  <;> nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (6 : ℝ),
    Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num),
    Real.sqrt_le_sqrt (show 2 ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (6 : ℝ),
    mul_nonneg (Real.sqrt_nonneg (3 : ℝ)) (Real.sqrt_nonneg (2 : ℝ)), 
    Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]