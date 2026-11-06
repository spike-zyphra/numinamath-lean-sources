import Mathlib

theorem algebra_153452 (x : ℝ) (hx : x > 0) (h : Real.sqrt (5^x) = 25 ^ ((1 : ℝ) / 3)) :
    x = 4 / 3 := by
  have h1 : Real.sqrt (5 ^ x) = (5 : ℝ) ^ (x / 2 : ℝ) := by
    have h2 : Real.sqrt (5 ^ x) = (5 ^ x) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      all_goals positivity
    rw [h2]
    rw [← Real.rpow_mul]
    ring_nf
    all_goals positivity
  have h3 : (25 : ℝ) ^ ((1 : ℝ) / 3) = (5 : ℝ) ^ (2 / 3 : ℝ) := by
    have h4 : (25 : ℝ) ^ ((1 : ℝ) / 3) = ((5 : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 3) := by
      norm_num
    have h5 : ((5 : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 3) = (5 : ℝ) ^ (2 * (1 / 3 : ℝ)) := by
      rw [← Real.rpow_mul]
      ring_nf
      all_goals positivity
    rw [h4, h5]
    all_goals ring_nf
  rw [h1, h3] at h
  have h6 : x / 2 = (2 / 3 : ℝ) := by
    have h7 : Real.logb (5 : ℝ) ((5 : ℝ) ^ (x / 2 : ℝ)) = (x / 2 : ℝ) * Real.logb (5 : ℝ) (5 : ℝ) := by
      apply Real.logb_rpow_eq_mul_logb_of_pos
      all_goals norm_num
    have h8 : Real.logb (5 : ℝ) ((5 : ℝ) ^ (2 / 3 : ℝ)) = (2 / 3 : ℝ) * Real.logb (5 : ℝ) (5 : ℝ) := by
      apply Real.logb_rpow_eq_mul_logb_of_pos
      all_goals norm_num
    have h9 : Real.logb (5 : ℝ) (5 : ℝ) = 1 := by
      rw [Real.logb_self_eq_one]
      all_goals norm_num
    apply_fun (Real.logb (5 : ℝ)) at h
    rw [h7, h8, h9] at h
    linarith
  linarith