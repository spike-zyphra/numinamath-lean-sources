import Mathlib

theorem algebra_153444 (x : ℝ) (h : (16 : ℝ)^x = 1 / 4) : x = -1 / 2 := by 
  have h1 : (16 : ℝ) ^ x = 1 / 4 := h
  have h2 : (16 : ℝ) ^ x = (2 : ℝ) ^ (4 * x) := by 
    rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num]
    rw [← Real.rpow_mul]
    ring_nf
    all_goals linarith
  have h3 : (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by 
    norm_num [Real.rpow_natCast, Real.rpow_neg, Real.rpow_mul]
    all_goals norm_num
  rw [h2] at h1
  rw [h3] at h1
  have h4 : 4 * x = -2 := by 
    apply_fun (Real.logb (2 : ℝ)) at h1
    simp [Real.logb_rpow] at h1 
    all_goals linarith 
    all_goals linarith
  linarith