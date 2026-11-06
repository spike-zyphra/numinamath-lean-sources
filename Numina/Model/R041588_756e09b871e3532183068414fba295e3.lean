import Mathlib

theorem algebra_13200 : {x : ℝ | (8 : ℝ)^(4 * x - 6) = (1 / 2)^(x + 5)} = {1} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume (8 : ℝ)^(4 * x - 6) = (1 / 2)^(x + 5), prove x = 1
    intro h_eq
    have h1 : (8 : ℝ) ^ (4 * x - 6) = (2 : ℝ) ^ (12 * x - 18) := by
      have h2 : (8 : ℝ) ^ (4 * x - 6) = ((2 : ℝ) ^ (3 : ℝ)) ^ (4 * x - 6) := by
        norm_num
      rw [h2]
      have h3 : ((2 : ℝ) ^ (3 : ℝ)) ^ (4 * x - 6) = (2 : ℝ) ^ (3 * (4 * x - 6 : ℝ)) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals linarith
      rw [h3]
      ring_nf
    have h2 : (1 / 2 : ℝ) ^ (x + 5) = (2 : ℝ) ^ (-x - 5 : ℝ) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by norm_num]
      have h3 : ((2 : ℝ) ^ (-1 : ℝ)) ^ (x + 5) = (2 : ℝ) ^ (-1 * (x + 5 : ℝ)) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals linarith
      rw [h3]
      ring_nf
    rw [h1, h2] at h_eq
    have h3 : 12 * x - 18 = -x - 5 := by
      apply_fun (Real.logb (2 : ℝ)) at h_eq
      have h4 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (12 * x - 18 : ℝ)) = Real.logb (2 : ℝ) ((2 : ℝ) ^ (-x - 5 : ℝ)) := by
        linarith [h_eq]
      have h5 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (12 * x - 18 : ℝ)) = (12 * x - 18 : ℝ) := by
        rw [Real.logb_rpow]
        all_goals norm_num
      have h6 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (-x - 5 : ℝ)) = (-x - 5 : ℝ) := by
        rw [Real.logb_rpow]
        all_goals norm_num
      linarith [h5, h6, h4]
    linarith
  · -- Assume x = 1, prove (8 : ℝ)^(4 * x - 6) = (1 / 2)^(x + 5)
    intro h_eq
    rw [h_eq]
    norm_num