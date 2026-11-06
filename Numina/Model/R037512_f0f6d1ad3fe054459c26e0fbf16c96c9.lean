import Mathlib

theorem algebra_19813 {b c : ℝ} (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : (125 : ℝ)^b = 5) (h2 : (27 : ℝ)^b = c) : c = 3 := by
  have h3 : (125 : ℝ) ^ b = 5 := h1
  have h4 : (125 : ℝ) = (5 : ℝ) ^ (3 : ℝ) := by norm_num
  rw [h4] at h3
  have h5 : ((5 : ℝ) ^ (3 : ℝ)) ^ b = (5 : ℝ) ^ (3 * b : ℝ) := by
    rw [← Real.rpow_mul]
    ring
    all_goals linarith
  rw [h5] at h3
  have h8 : (3 * b : ℝ) = 1 := by
    have h7 : (5 : ℝ) ^ (3 * b : ℝ) = (5 : ℝ) := by linarith [h3]
    apply_fun (Real.log) at h7
    have h9 : Real.log ((5 : ℝ) ^ (3 * b : ℝ)) = (3 * b) * Real.log (5 : ℝ) := by 
      rw [Real.log_rpow]
      all_goals linarith
    rw [h9] at h7
    have h10 : Real.log (5 : ℝ) > 0 := by 
      apply Real.log_pos
      all_goals norm_num
    nlinarith
  have h3b : b = 1 / 3 := by
    linarith
  have h27 : (27 : ℝ) ^ b = c := by linarith [h2]
  rw [show b = (1 / 3 : ℝ) by linarith [h3b]] at h27
  have h27_eq : (27 : ℝ) ^ ((1 / 3 : ℝ) ) = 3 := by
    have : (27 : ℝ) = (3 : ℝ) ^ (3 : ℝ) := by norm_num
    rw [this]
    have h9 : ((3 : ℝ) ^ (3 : ℝ)) ^ ((1 / 3 : ℝ) ) = (3 : ℝ) ^ (3 * (1 / 3 : ℝ) ) := by
      rw [← Real.rpow_mul]
      ring
      all_goals linarith
    rw [h9]
    norm_num
  linarith [h27, h27_eq]