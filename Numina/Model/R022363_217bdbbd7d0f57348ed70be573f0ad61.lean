import Mathlib

open Real

theorem algebra_252756 : cos (36 * π / 180) * cos (72 * π / 180) = 1 / 4 := by
  have h1 : cos (36 * π / 180) = cos (π / 5) := by 
    ring_nf
  have h2 : cos (72 * π / 180) = cos (2 * π / 5) := by 
    ring_nf
  rw [h1, h2]

  have h3 : cos (π / 5) * cos (2 * π / 5) = 1 / 4 := by
    have h4 : cos (π / 5) = (1 + Real.sqrt 5) / 4 := by 
      rw [cos_pi_div_five]
      all_goals linarith
    have h5 : cos (2 * π / 5) = (Real.sqrt 5 - 1) / 4 := by
      have h8 : cos (2 * π / 5) = 2 * cos (π / 5) ^ 2 - 1 := by
        rw [show 2 * π / 5 = 2 * (π / 5) by ring]
        rw [cos_two_mul]
      rw [h8, h4]
      field_simp
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (0 : ℝ) < (5 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ))]
    
    rw [h4, h5]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (0 : ℝ) < (5 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ))]

  linarith [h3]