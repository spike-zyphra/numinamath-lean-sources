import Mathlib

theorem algebra_252697 (x : ℝ) : (4 : ℝ)^x = 8^(2*x - 3) ↔ x = 9/4 := by
  constructor
  · -- Forward direction: If (4 : ℝ) ^ x = 8 ^ (2 * x - 3), then x = 9 / 4
    intro h
    have h1 : (8 : ℝ) ^ (2 * x - 3) = (2 : ℝ) ^ (3 * (2 * x - 3)) := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    have h2 : (4 : ℝ) ^ x = (2 : ℝ) ^ (2 * x) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    rw [h1] at h
    rw [h2] at h
    have h3 : (2 * x) = (3 * (2 * x - 3)) := by
      apply_fun (Real.logb (2 : ℝ)) at h
      simp at h
      linarith
    nlinarith
  · -- Backward direction: If x = 9 / 4, then (4 : ℝ) ^ x = 8 ^ (2 * x - 3)
    intro h
    rw [h]
    have h3 : (4 : ℝ) ^ (9 / 4 : ℝ) = (2 : ℝ) ^ (9 / 2 : ℝ) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    have h4 : (8 : ℝ) ^ (2 * (9 / 4 : ℝ) - 3) = (2 : ℝ) ^ (9 / 2 : ℝ) := by
      have h5 : (2 * (9 / 4 : ℝ) - 3) = (3 / 2 : ℝ) := by norm_num
      rw [h5]
      rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    rw [h3, h4]