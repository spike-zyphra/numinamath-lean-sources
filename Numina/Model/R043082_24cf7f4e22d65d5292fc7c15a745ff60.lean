import Mathlib

theorem algebra_10496 : Real.sqrt (6 + 4 * Real.sqrt 2) + Real.sqrt (6 - 4 * Real.sqrt 2) = 4 := by
  have h1 : Real.sqrt (6 + 4 * Real.sqrt 2) = 2 + Real.sqrt 2 := by
    have h2 : (2 + Real.sqrt 2) ^ 2 = 6 + 4 * Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h3 : 2 + Real.sqrt 2 ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 2]
    rw [← h2]
    field_simp [Real.sqrt_sq, h3]
  have h4 : Real.sqrt (6 - 4 * Real.sqrt 2) = 2 - Real.sqrt 2 := by
    have h5 : (2 - Real.sqrt 2) ^ 2 = 6 - 4 * Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h6 : 2 - Real.sqrt 2 ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), show Real.sqrt 2 ≤ 2 by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]]
    rw [← h5]
    field_simp [Real.sqrt_sq, h6]
  rw [h1, h4]
  ring_nf
  <;> norm_num