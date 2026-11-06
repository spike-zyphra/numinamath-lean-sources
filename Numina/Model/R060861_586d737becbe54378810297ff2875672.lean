import Mathlib

theorem algebra_21569 (x : ℝ) : Real.logb (64 ^ ((1 : ℝ) / 3)) (4 ^ x) = 1 ↔ x = 1 := by 
  have h1 : (64 : ℝ) ^ ((1 : ℝ) / 3) = 4 := by 
    have h2 : (64 : ℝ) ^ ((1 : ℝ) / 3) = ((4 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) := by
      norm_num
    rw [h2]
    have h3 : ((4 : ℝ) ^ (3 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) = (4 : ℝ) ^ (3 * (1 / 3 : ℝ)) := by
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    rw [h3]
    all_goals norm_num
  rw [h1]
  constructor
  · -- Assume Real.logb (4 : ℝ) (4 ^ x) = 1 implies x = 1
    intro h 
    have h3 : Real.logb (4 : ℝ) (4 ^ x) = x := by 
      rw [Real.logb_rpow]
      all_goals norm_num
    rw [h3] at h
    linarith
  · -- Assume x = 1 implies Real.logb (4 : ℝ) (4 ^ x) = 1 
    intro h 
    rw [h]
    norm_num [Real.logb_eq_iff_rpow_eq]
    all_goals norm_num