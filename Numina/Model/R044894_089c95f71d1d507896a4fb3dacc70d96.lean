import Mathlib

theorem algebra_149649 : ∃ x, (Real.sqrt 3 - Real.sqrt 2) / Real.sqrt 3 = x / (3 + Real.sqrt 6) := by
  use 1
  have h1 : 0 < Real.sqrt 3 := by
    positivity
  have h2 : Real.sqrt 6 = Real.sqrt 3 * Real.sqrt 2 := by
    have h3 : (6 : ℝ) = (3 : ℝ) * (2 : ℝ) := by norm_num
    rw [h3]
    have h4 : 0 ≤ (3 : ℝ) := by norm_num
    have h5 : 0 ≤ (2 : ℝ) := by norm_num
    rw [Real.sqrt_mul (by norm_num)]
  field_simp [(show Real.sqrt 3 ≠ 0 by positivity), (show (3 + Real.sqrt 6) ≠ 0 by
    have h6 : Real.sqrt 6 > 0 := by positivity
    linarith
  ), h2]
  <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 - Real.sqrt 2), Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 2), h2]