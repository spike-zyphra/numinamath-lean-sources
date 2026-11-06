import Mathlib

theorem algebra_232043 (x : ℝ) : (64 : ℝ)^x = (512 : ℝ)^5 ↔ x = 7.5 := by
  constructor
  · -- Assume (64 : ℝ)^x = (512 : ℝ)^5, we need to prove x = 7.5
    intro h
    have h1 : (64 : ℝ) ^ x = (512 : ℝ) ^ 5 := h
    have h2 : (64 : ℝ) ^ x = (2 : ℝ) ^ (6 * x) := by
      rw [show (64 : ℝ) = (2 : ℝ) ^ (6 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    have h3 : (512 : ℝ) ^ 5 = (2 : ℝ) ^ (45 : ℝ) := by
      norm_num
    rw [h2, h3] at h1
    have h4 : 6 * x = (45 : ℝ) := by
      apply_fun (Real.logb (2 : ℝ)) at h1
      have h5 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (6 * x)) = Real.logb (2 : ℝ) ((2 : ℝ) ^ (45 : ℝ)) := by
        linarith [h1]
      have h6 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (6 * x)) = (6 * x : ℝ) := by
        rw [Real.logb_rpow]
        all_goals norm_num
      have h7 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (45 : ℝ)) = (45 : ℝ) := by
        rw [Real.logb_rpow]
        all_goals norm_num
      rw [h6, h7] at h5
      linarith
    have h8 : x = (7.5 : ℝ) := by
      linarith
    linarith
  · -- Assume x = 7.5, prove (64 : ℝ)^x = (512 : ℝ)^5
    intro h
    rw [h]
    have h1 : (64 : ℝ) ^ (7.5 : ℝ) = (2 : ℝ) ^ (45 : ℝ) := by
      rw [show (64 : ℝ) = (2 : ℝ) ^ (6 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    have h2 : (512 : ℝ) ^ 5 = (2 : ℝ) ^ (45 : ℝ) := by
      norm_num
    rw [h1, h2]