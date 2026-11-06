import Mathlib

theorem algebra_153470 (x : ℝ) (h : (0.25 : ℝ)^(2 - x) = 256 / 2^(x + 3)) : x = 3 := by

  have h1 : (0.25 : ℝ) ^ (2 - x) = (2 : ℝ) ^ (2 * x - 4) := by
    have h2 : (0.25 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by norm_num
    rw [h2]
    rw [← Real.rpow_mul]
    ring_nf
    all_goals norm_num

  have h3 : (256 / (2 : ℝ) ^ (x + 3)) = (2 : ℝ) ^ (5 - x) := by
    have h4 : (256 : ℝ) = (2 : ℝ) ^ (8 : ℝ) := by norm_num
    rw [h4]
    have h5 : (2 : ℝ) ^ (8 : ℝ) / (2 : ℝ) ^ (x + 3 : ℝ) = (2 : ℝ) ^ ((8 : ℝ) - (x + 3 : ℝ)) := by 
      rw [← Real.rpow_sub]
      ring_nf
      all_goals linarith
    rw [h5]
    ring_nf

  rw [h1, h3] at h

  have h4 : (2 * x - 4 : ℝ) = (5 - x : ℝ) := by
    apply_fun (Real.logb (2 : ℝ)) at h
    have h5 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (2 * x - 4 : ℝ)) = Real.logb (2 : ℝ) ((2 : ℝ) ^ (5 - x : ℝ)) := by 
      linarith [h]
    have h6 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (2 * x - 4 : ℝ)) = (2 * x - 4 : ℝ) := by 
      rw [Real.logb_rpow]
      all_goals norm_num
    have h7 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (5 - x : ℝ)) = (5 - x : ℝ) := by 
      rw [Real.logb_rpow]
      all_goals norm_num
    rw [h6, h7] at h5
    linarith

  linarith