import Mathlib

open Real Set
open scoped Real

theorem algebra_134858 {x : ℝ} (hx : x = cos (36 * π / 180) - cos (72 * π / 180)) :
    x = 1 / 2 := by 
  rw [hx]
  have h1 : cos (36 * π / 180) = (1 + Real.sqrt 5) / 4 := by
    have h4 : 36 * π / 180 = Real.pi / 5 := by
      ring_nf
    rw [h4]
    have h3 : cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by
      rw [cos_pi_div_five]
    linarith 
  have h2 : cos (72 * π / 180) = (Real.sqrt 5 - 1) / 4 := by 
    have h5 : 72 * π / 180 = 2 * (Real.pi / 5) := by
      ring_nf
    rw [h5]
    have h6 : cos (2 * (Real.pi / 5)) = 2 * cos (Real.pi / 5) ^ 2 - 1 := by 
      rw [cos_two_mul]
    rw [h6]
    have h3 : cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by 
      rw [cos_pi_div_five]
    rw [h3]
    nlinarith [Real.sqrt_pos.mpr (show (0: ℝ) < 5 by norm_num : (0: ℝ) < 5), Real.sq_sqrt (show (0: ℝ) ≤ (5: ℝ) by norm_num : (0: ℝ) ≤ (5: ℝ)), Real.sqrt_nonneg 5]
  rw [h1, h2]
  field_simp
  <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0: ℝ) ≤ (5: ℝ) by norm_num : (0: ℝ) ≤ (5: ℝ)), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num : (5 : ℝ) > 0)]