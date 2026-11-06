import Mathlib

open Real

theorem algebra_185148 : (6 / (sqrt 2 + sqrt 3 + sqrt 5)) = (2 * sqrt 3 + 3 * sqrt 2 - sqrt 30) / 2 := by
  have h1 : sqrt 2 + sqrt 3 + sqrt 5 ≠ 0 := by
    positivity
  have h2 : 6 / (sqrt 2 + sqrt 3 + sqrt 5) = (2 * sqrt 3 + 3 * sqrt 2 - sqrt 30) / 2 := by
    have h3 : sqrt 2 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
    have h4 : sqrt 3 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)
    have h5 : sqrt 5 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num)
    have h6 : sqrt 30 = sqrt 5 * sqrt 6 := by
      rw [show (30 : ℝ) = 5 * 6 by norm_num]
      field_simp [Real.sqrt_mul]
    have h7 : sqrt 6 = sqrt 2 * sqrt 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num]
      field_simp [Real.sqrt_mul]
    have h8 : sqrt 30 = sqrt 5 * (sqrt 2 * sqrt 3) := by
      rw [h6, h7]
      all_goals ring_nf <;> norm_num
    field_simp [h1, h8]
    have h9 : sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    have h10 : sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
    have h11 : sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, sq_nonneg (sqrt 2 - sqrt 3), sq_nonneg (sqrt 2 - sqrt 5), sq_nonneg (sqrt 3 - sqrt 5), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  linarith [h2]