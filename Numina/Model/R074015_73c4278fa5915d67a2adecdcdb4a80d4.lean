import Mathlib

theorem algebra_283622 : √(9 + 4 * √5) - √(9 - 4 * √5) = 4 := by
  have h1 : √(9 + 4 * √5) = √5 + 2 := by
    have h2 : (√5 + 2) ^ 2 = 9 + 4 * √5 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
    have h3 : √5 + 2 ≥ 0 := by positivity
    have h4 : √(9 + 4 * √5) = √((√5 + 2) ^ 2) := by
      rw [h2] 
    rw [h4]
    rw [Real.sqrt_sq (show (√5 + 2) ≥ 0 by positivity)]
  have h5 : √(9 - 4 * √5) = √5 - 2 := by
    have h6 : (√5 - 2) ^ 2 = 9 - 4 * √5 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
    have h7 : √5 - 2 ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
    have h8 : √(9 - 4 * √5) = √((√5 - 2) ^ 2) := by 
      rw [h6] 
    rw [h8]
    rw [Real.sqrt_sq (show (√5 - 2) ≥ 0 by nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)])]
  rw [h1, h5]
  nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]