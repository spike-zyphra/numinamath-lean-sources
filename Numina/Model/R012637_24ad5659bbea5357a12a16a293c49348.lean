import Mathlib

theorem algebra_16344 (m : ℝ) : (81 : ℝ) ^ ((1 : ℝ) / 2) = 3 ^ m ↔ m = 2 := by
  constructor
  · -- Assume (81 : ℝ) ^ ((1 : ℝ) / 2) = 3 ^ m, prove m = 2
    intro h
    have h1 : (81 : ℝ) ^ ((1 : ℝ) / 2) = (3 : ℝ) ^ (2 : ℝ) := by
      have h2 : (81 : ℝ) ^ ((1 : ℝ) / 2) = ((3 : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 2) := by
        norm_num
      rw [h2]
      have h3 : ((3 : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 2) = (3 : ℝ) ^ (4 * (1 / 2) : ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals linarith
      rw [h3]
      norm_num
    rw [h1] at h
    have h2 : m = (2 : ℝ) := by
      apply_fun (Real.logb (3 : ℝ)) at h
      have h3 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (2 : ℝ)) = (2 : ℝ) := by
        rw [Real.logb_rpow]
        all_goals norm_num
      have h4 : Real.logb (3 : ℝ) ((3 : ℝ) ^ m) = m := by
        rw [Real.logb_rpow]
        all_goals norm_num
      rw [h3, h4] at h
      linarith
    linarith
  · -- Assume m = 2, prove (81 : ℝ) ^ ((1 : ℝ) / 2) = 3 ^ m
    intro h
    rw [h]
    have h1 : (81 : ℝ) ^ ((1 : ℝ) / 2) = (3 : ℝ) ^ (2 : ℝ) := by
      have h2 : (81 : ℝ) ^ ((1 : ℝ) / 2) = ((3 : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 2) := by
        norm_num
      rw [h2]
      have h3 : ((3 : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 2) = (3 : ℝ) ^ (4 * (1 / 2) : ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals linarith
      rw [h3]
      norm_num
    linarith [h1]