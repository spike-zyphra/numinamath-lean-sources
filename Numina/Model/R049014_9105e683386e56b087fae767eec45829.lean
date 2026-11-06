import Mathlib

open Real

theorem algebra_13433 : sqrt (20 + 4 * sqrt 24) = 2 * sqrt 2 + 2 * sqrt 3 := by
  have h2 : sqrt 24 = 2 * Real.sqrt 2 * Real.sqrt 3 := by
    have h8 : sqrt 24 = sqrt (4 * 6) := by
      norm_num [Real.sqrt_eq_iff_mul_self_eq]
    have h9 : sqrt (4 * 6) = sqrt 4 * sqrt 6 := by
      rw [Real.sqrt_mul (by norm_num)]
    have h10 : sqrt 4 = 2 := by
      rw [Real.sqrt_eq_cases]
      all_goals norm_num
    have h11 : sqrt 6 = sqrt 2 * Real.sqrt 3 := by
      have h14 : Real.sqrt 6 = Real.sqrt (2 * 3) := by
        norm_num [Real.sqrt_eq_iff_mul_self_eq]
      have h15 : Real.sqrt (2 * 3) = Real.sqrt 2 * Real.sqrt 3 := by
        rw [Real.sqrt_mul (by norm_num)]
      rw [h14, h15]
      all_goals ring_nf <;> norm_num [Real.sq_sqrt]
    rw [h8, h9, h10, h11]
    all_goals ring_nf <;> norm_num [Real.sq_sqrt]
  have h3 : 20 + 4 * Real.sqrt 24 = (2 * Real.sqrt 2 + 2 * Real.sqrt 3) ^ 2 := by
    rw [h2]
    nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (24 : ℝ) by norm_num)]
  rw [h3]
  have h4 : 0 ≤ (2 * Real.sqrt 2 + 2 * Real.sqrt 3 : ℝ) := by
    positivity
  rw [Real.sqrt_sq (h4)]
  all_goals norm_num [Real.sq_sqrt]
  all_goals try ring_nf <;> norm_num
  all_goals try nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (24 : ℝ) by norm_num)]
  all_goals norm_num [Real.sq_sqrt]
  all_goals try ring_nf <;> norm_num
  all_goals try nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (24 : ℝ) by norm_num)]