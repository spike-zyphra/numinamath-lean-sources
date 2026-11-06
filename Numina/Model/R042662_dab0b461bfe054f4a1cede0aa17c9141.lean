import Mathlib

theorem algebra_10374 {x : ℝ}: (81:ℝ) ^ (2 * x) = 27 ^ (3 * x - 4) ↔ x = 12 := by
  constructor
  · -- Assume (81:ℝ) ^ (2 * x) = 27 ^ (3 * x - 4), prove x = 12
    intro h
    have h1 : (81:ℝ) ^ (2 * x) = (3 : ℝ) ^ (8 * x) := by
      rw [show (81 : ℝ) = (3 ^ (4 : ℝ) ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    have h2 : (27:ℝ) ^ (3 * x - 4) = (3 : ℝ) ^ (9 * x - 12) := by
      rw [show (27 : ℝ) = (3 ^ (3 : ℝ) ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    rw [h1, h2] at h
    have h3 : 8 * x = 9 * x - 12 := by
      apply_fun (Real.logb (3 : ℝ)) at h
      have h5 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (8 * x)) = 8 * x := by
        rw [Real.logb_rpow]
        all_goals linarith
      have h6 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (9 * x - 12 : ℝ)) = 9 * x - 12 := by
        rw [Real.logb_rpow]
        all_goals linarith
      linarith [h5, h6, h]
    linarith
  · -- Assume x = 12, prove (81:ℝ) ^ (2 * x) = 27 ^ (3 * x - 4)
    intro h
    rw [h]
    have h1 : (81:ℝ) ^ (2 * (12 : ℝ)) = (3 : ℝ) ^ (8 * (12 : ℝ)) := by
      rw [show (81 : ℝ) = (3 ^ (4 : ℝ) ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    have h2 : (27:ℝ) ^ (3 * (12 : ℝ) - 4) = (3 : ℝ) ^ (9 * (12 : ℝ) - 12) := by
      rw [show (27 : ℝ) = (3 ^ (3 : ℝ) ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    rw [h1, h2]
    norm_num