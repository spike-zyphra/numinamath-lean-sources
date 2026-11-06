import Mathlib

theorem algebra_20608 (x : ℝ) : (1 / 8 : ℝ)^x = 2^12 ↔ x = -4 := by
  constructor
  · -- Assume (1 / 8 : ℝ)^x = 2^12, prove x = -4
    intro h
    have h1 : (1 / 8 : ℝ) ^ x = (2 : ℝ) ^ (12 : ℝ) := by
      norm_num at h ⊢
      linarith
    have h2 : (1 / 8 : ℝ) ^ x = (2 : ℝ) ^ (-3 * x : ℝ) := by
      rw [show (1 / 8 : ℝ) = (2 : ℝ) ^ (-3 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    rw [h2] at h1
    have h3 : -3 * x = (12 : ℝ) := by
      apply_fun (Real.logb (2 : ℝ)) at h1
      have h4 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (-3 * x : ℝ)) = -3 * x := by
        rw [Real.logb_rpow]
        all_goals linarith
      have h5 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (12 : ℝ)) = (12 : ℝ) := by
        rw [Real.logb_rpow]
        all_goals linarith
      rw [h4, h5] at h1
      linarith
    linarith
  · -- Assume x = -4, prove (1 / 8 : ℝ)^x = 2^12
    intro h
    rw [h]
    norm_num