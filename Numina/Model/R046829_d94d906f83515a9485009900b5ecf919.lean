import Mathlib

open Real Set
open scoped Real

theorem calculus_17263 : Real.cos (72 * π / 180) = (-1 + sqrt 5) / 4 := by
  have h1 : 72 * π / 180 = 2 * (Real.pi / 5) := by
    ring_nf
  rw [h1]
  have h2 : Real.cos (2 * (Real.pi / 5)) = 2 * (Real.cos (Real.pi / 5)) ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  rw [h2]
  have h3 : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by
    have h4 : Real.cos (3 * (Real.pi / 5)) = 4 * (Real.cos (Real.pi / 5)) ^ 3 - 3 * Real.cos (Real.pi / 5) := by
      rw [Real.cos_three_mul]
    have h5 : 3 * (Real.pi / 5) = Real.pi - 2 * (Real.pi / 5) := by
      ring_nf
    have h6 : Real.cos (3 * (Real.pi / 5)) = - Real.cos (2 * (Real.pi / 5)) := by
      rw [h5]
      rw [Real.cos_pi_sub]
    have h7 : Real.cos (2 * (Real.pi / 5)) = 2 * (Real.cos (Real.pi / 5)) ^ 2 - 1 := by
      rw [Real.cos_two_mul]
    rw [h7] at h6
    rw [h4] at h6
    have h8 : 4 * (Real.cos (Real.pi / 5)) ^ 3 + 2 * (Real.cos (Real.pi / 5)) ^ 2 - 3 * Real.cos (Real.pi / 5) - 1 = 0 := by 
      nlinarith [h4, h5, h6, h7]
    have h9 : Real.cos (Real.pi / 5) > 0 := by 
      apply Real.cos_pos_of_mem_Ioo 
      constructor
      · -- Show 0 < π/5
        linarith [Real.pi_pos]
      · -- Show π/5 < π 
        linarith [Real.pi_pos]
    have h10 : (Real.cos (Real.pi / 5) + 1) * (4 * (Real.cos (Real.pi / 5)) ^ 2 - 2 * Real.cos (Real.pi / 5) - 1) = 0 := by
      nlinarith [h8]
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- h11 : Real.cos (Real.pi / 5) + 1 = 0 
      nlinarith [h9, h11]
    · -- h12 : 4 * (Real.cos (Real.pi / 5)) ^ 2 - 2 * Real.cos (Real.pi / 5) - 1 = 0 
      have h13 : (Real.cos (Real.pi / 5) - (1 + Real.sqrt 5) / 4) * (Real.cos (Real.pi / 5) - (1 - Real.sqrt 5) / 4) = 0 := by 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), h12]
      cases' (mul_eq_zero.mp h13) with h14 h15
      · -- h14 : Real.cos (Real.pi / 5) - (1 + Real.sqrt 5) / 4 = 0 
        linarith
      · -- h15 : Real.cos (Real.pi / 5) - (1 - Real.sqrt 5) / 4 = 0 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 5, h15, h9]
  rw [h3]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]