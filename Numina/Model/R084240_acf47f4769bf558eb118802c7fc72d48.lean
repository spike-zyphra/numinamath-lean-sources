import Mathlib

theorem algebra_242801 (k : ℝ) (h : Real.sqrt 2016 + Real.sqrt 56 = 14^k) :
    k = 3 / 2 := by
  have h1 : Real.sqrt 2016 = 12 * Real.sqrt 14 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h2 : Real.sqrt 56 = 2 * Real.sqrt 14 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h3 : Real.sqrt 2016 + Real.sqrt 56 = 14 * Real.sqrt 14 := by
    rw [h1, h2]
    ring_nf
  have h4 : (14 : ℝ) ^ (k : ℝ) = 14 * Real.sqrt 14 := by
    linarith [h, h3]
  have h5 : Real.sqrt 14 = (14 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
  have h6 : (14 : ℝ) * Real.sqrt 14 = (14 : ℝ) ^ (3 / 2 : ℝ) := by
    rw [h5]
    have h7 : (14 : ℝ) ^ (3 / 2 : ℝ) = (14 : ℝ) ^ (1 : ℝ) * (14 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = (1 : ℝ) + (1 / 2 : ℝ) by ring]
      rw [Real.rpow_add]
      norm_num
      all_goals norm_num
    rw [h7]
    norm_num
  rw [h6] at h4
  have h8 : k = (3 / 2 : ℝ) := by
    apply_fun (Real.logb (14 : ℝ)) at h4
    have h9 : Real.logb (14 : ℝ) ((14 : ℝ) ^ (k : ℝ)) = k := by
      rw [Real.logb_rpow]
      all_goals norm_num
    have h10 : Real.logb (14 : ℝ) ((14 : ℝ) ^ (3 / 2 : ℝ)) = (3 / 2 : ℝ) := by
      rw [Real.logb_rpow]
      all_goals norm_num
    rw [h9] at h4
    rw [h10] at h4
    linarith [h4]
  linarith [h8]
  <;> try { linarith [h4, h5, h6, h8] }