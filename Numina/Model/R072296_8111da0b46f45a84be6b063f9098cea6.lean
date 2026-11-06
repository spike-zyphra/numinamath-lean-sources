import Mathlib

open Real

theorem algebra_321936 : sqrt (14 + 6 * sqrt 5) - sqrt (14 - 6 * sqrt 5) = 2 * sqrt 5 := by
  have h1 : sqrt (14 + 6 * sqrt 5) = 3 + sqrt 5 := by
    have h2 : (3 + Real.sqrt 5) ^ 2 = 14 + 6 * Real.sqrt 5 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    have h3 : 0 ≤ (3 + Real.sqrt 5 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 5]
    rw [← h2]
    field_simp [Real.sqrt_sq h3]
  have h4 : sqrt (14 - 6 * sqrt 5) = 3 - sqrt 5 := by
    have h5 : (3 - Real.sqrt 5) ^ 2 = 14 - 6 * Real.sqrt 5 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    have h6 : 0 ≤ (3 - Real.sqrt 5 : ℝ) := by
      have h7 : Real.sqrt 5 ≤ 3 := by
        rw [Real.sqrt_le_left]
        all_goals norm_num
      linarith [h7]
    rw [← h5]
    field_simp [Real.sqrt_sq h6]
  rw [h1, h4]
  ring