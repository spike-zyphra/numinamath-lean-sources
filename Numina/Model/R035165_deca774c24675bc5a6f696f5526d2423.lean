import Mathlib

open Real

theorem algebra_283194 : cos (2 * π / 5) + cos (4 * π / 5) = -1 / 2 := by
  have h1 : cos (4 * π / 5) = -cos (π / 5) := by
    have h2 : 4 * π / 5 = π - (π / 5) := by
      ring
    rw [h2]
    have h3 : cos (π - (π / 5)) = -cos (π / 5) := by 
      rw [cos_pi_sub]
    exact h3
  have h2 : cos (2 * π / 5) = 2 * (cos (π / 5)) ^ 2 - 1 := by
    have h3 : 2 * π / 5 = 2 * (π / 5) := by
      ring
    rw [h3]
    rw [cos_two_mul]
  rw [h1, h2]
  have h3 : cos (π / 5) = (1 + Real.sqrt 5) / 4 := by
    rw [Real.cos_pi_div_five]
  rw [h3]
  nlinarith [Real.sqrt_pos.mpr (show (0: ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0: ℝ) ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]