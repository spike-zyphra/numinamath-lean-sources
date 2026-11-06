import Mathlib

open Real

theorem algebra_109406 : cos (2 * π / 5) + cos (4 * π / 5) = -1 / 2 := by
  have h1 : cos (4 * π / 5) = -cos (π / 5) := by
    have h2 : 4 * π / 5 = π - (π / 5) := by
      linarith [pi_pos]
    rw [h2]
    rw [cos_pi_sub]
  have h2 : cos (2 * π / 5) = 2 * cos (π / 5) ^ 2 - 1 := by
    have h3 : 2 * π / 5 = 2 * (π / 5) := by 
      ring
    rw [h3]
    rw [cos_two_mul]
  have h3 : cos (2 * π / 5) + cos (4 * π / 5) = 2 * cos (π / 5) ^ 2 - cos (π / 5) - 1 := by
    rw [h1, h2]
    all_goals 
      ring 
  have h4 : cos (π / 5) = (1 + Real.sqrt 5) / 4 := by
    rw [cos_pi_div_five]
  rw [h3]
  rw [h4]
  nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]