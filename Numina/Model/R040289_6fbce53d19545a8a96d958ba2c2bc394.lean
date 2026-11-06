import Mathlib

open Real

theorem algebra_102972 {A : ℝ}
    (hA : A = cos (10 * π / 180) ^ 2 + cos (50 * π / 180) ^ 2 - sin (40 * π / 180) * sin (80 * π / 180)) :
    100 * A = 75 := by
  have h1 : cos (50 * π / 180) = 1 / 2 * cos (10 * π / 180) + Real.sqrt 3 / 2 * sin (10 * π / 180) := by
    have h2 : 50 * π / 180 = Real.pi / 3 - 10 * π / 180 := by
      linarith [Real.pi_pos]
    rw [h2]
    rw [cos_sub]
    simp [cos_pi_div_three, sin_pi_div_three]
    all_goals ring
  have h3 : sin (40 * π / 180) = 1 / 2 * cos (10 * π / 180) + Real.sqrt 3 / 2 * sin (10 * π / 180) := by
    have h4 : 40 * π / 180 = Real.pi / 6 + 10 * π / 180 := by
      linarith [Real.pi_pos]
    rw [h4]
    rw [sin_add]
    simp [sin_pi_div_six, cos_pi_div_six]
    all_goals ring
  have h5 : sin (80 * π / 180) = cos (10 * π / 180) := by
    have h6 : 80 * π / 180 = Real.pi / 2 - 10 * π / 180 := by
      linarith [Real.pi_pos]
    rw [h6]
    rw [sin_pi_div_two_sub]
  rw [hA]
  rw [h1, h3, h5]
  have h7 : cos (10 * π / 180) ^ 2 + sin (10 * π / 180) ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq (10 * π / 180)
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), 
          h7
        ]