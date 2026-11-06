import Mathlib

theorem algebra_174913 {x y : ℝ} (hy : y ≠ 0) (h : (8 * y - 1) ^ 2 + abs (x - 16 * y) = 0) :
    Real.logb 2 (y ^ x) = -6 := by
  have h1 : (8 * y - 1) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h2 : abs (x - 16 * y) ≥ 0 := by
    apply abs_nonneg
  have h3 : (8 * y - 1) ^ 2 = 0 := by 
    linarith
  have h4 : abs (x - 16 * y) = 0 := by 
    linarith
  have hy_val : y = 1 / 8 := by
    have h5 : 8 * y - 1 = 0 := by
      nlinarith [h3]
    linarith
  have hx_val : x = 2 := by
    have h5 : x - 16 * y = 0 := by
      rwa [abs_eq_zero] at h4
    rw [hy_val] at h5
    linarith
  rw [hx_val, hy_val]
  have h1 : Real.logb 2 ((1 / 8 : ℝ) ^ (2 : ℝ)) = -6 := by
    have h2 : (1 / 8 : ℝ) ^ (2 : ℝ) = (2 : ℝ) ^ (-6 : ℝ) := by
      rw [show (1 / 8 : ℝ) = (2 : ℝ) ^ (-3 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
      all_goals norm_num
    have h3 : Real.logb 2 ((2 : ℝ) ^ (-6 : ℝ)) = -6 := by
      rw [Real.logb_rpow]
      all_goals norm_num
      all_goals norm_num
    rw [h2]
    all_goals try rw [h3]
    all_goals norm_num
  exact h1
  all_goals try norm_num
  all_goals norm_num
  all_goals try tauto
  all_goals norm_num
  all_goals try linarith