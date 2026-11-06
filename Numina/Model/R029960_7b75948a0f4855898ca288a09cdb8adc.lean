import Mathlib

theorem algebra_93339 (x : ℝ) : (8 : ℝ)^x = 32 ↔ x = 5 / 3 := by
  constructor
  · -- Assume $8^x = 32$, prove $x = \frac{5}{3}$
    intro h
    have h1 : (8 : ℝ) ^ x = (2 : ℝ) ^ (3 * x) := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    have h2 : (2 : ℝ) ^ (3 * x) = (2 : ℝ) ^ (5 : ℝ) := by
      rw [←h1]
      linarith [h]
    have h3 : 3 * x = (5 : ℝ) := by
      apply_fun (Real.logb (2 : ℝ)) at h2
      have h4 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (3 * x)) = Real.logb (2 : ℝ) ((2 : ℝ) ^ (5 : ℝ)) := by
        linarith [h2]
      have h5 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (3 * x)) = 3 * x := by 
        rw [Real.logb_rpow]
        all_goals norm_num
      have h6 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (5 : ℝ)) = (5 : ℝ) := by
        rw [Real.logb_rpow]
        all_goals norm_num
      rw [h5, h6] at h4
      linarith
    linarith
  · -- Assume x = 5/3, prove 8^x = 32
    intro h
    rw [h]
    have h1 : (8 : ℝ) ^ (5 / 3 : ℝ) = (2 : ℝ) ^ (5 : ℝ) := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    rw [h1]
    norm_num