import Mathlib

theorem algebra_287556 (x y : ℝ) (h : x + 2 * y = 3) :
    2 ^ x + 4 ^ y ≥ 4 * Real.sqrt 2 := by
  have h1 : (4 : ℝ) ^ y = (2 : ℝ) ^ (2 * y) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num]
    rw [← Real.rpow_mul]
    ring
    all_goals linarith
  have h2 : (2 : ℝ) ^ x = (2 : ℝ) ^ (3 - 2 * y) := by
    have h3 : x = (3 - 2 * y) := by 
      linarith
    rw [h3]
  have h3 : (2 : ℝ) ^ x + (4 : ℝ) ^ y = (2 : ℝ) ^ (3 - 2 * y) + (2 : ℝ) ^ (2 * y) := by
    rw [h2, h1]
  have h4 : (2 : ℝ) ^ (3 - 2 * y) + (2 : ℝ) ^ (2 * y) ≥ 4 * Real.sqrt 2 := by
    have h5 : (2 : ℝ) ^ (3 - 2 * y) > 0 := by positivity
    have h6 : (2 : ℝ) ^ (2 * y) > 0 := by positivity
    have h7 : (2 : ℝ) ^ (3 - 2 * y) * (2 : ℝ) ^ (2 * y) = (8 : ℝ) := by
      have h8 : (2 : ℝ) ^ (3 - 2 * y) * (2 : ℝ) ^ (2 * y) = (2 : ℝ) ^ ((3 - 2 * y) + (2 * y) ) := by
        rw [← Real.rpow_add]
        ring_nf
        all_goals linarith
      rw [h8]
      have h3 : (3 - 2 * y : ℝ) + (2 * y : ℝ) = (3 : ℝ) := by
        linarith
      rw [h3]
      norm_num
    nlinarith [sq_nonneg ((2 : ℝ) ^ (3 - 2 * y) - (2 : ℝ) ^ (2 * y)), sq_nonneg ((2 : ℝ) ^ (3 - 2 * y) - 2 * Real.sqrt 2), sq_nonneg ((2 : ℝ) ^ (2 * y) - 2 * Real.sqrt 2), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), h7, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), mul_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  nlinarith [h3, h4]