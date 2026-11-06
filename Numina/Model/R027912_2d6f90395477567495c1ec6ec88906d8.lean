import Mathlib

open Real

theorem calculus_22645 : tan (15 * π / 180) = 2 - sqrt 3 := by
  have h1 : 15 * π / 180 = π / 12 := by 
    ring_nf
  rw [h1]
  have h2 : π / 12 = π / 4 - π / 6 := by
    linarith [Real.pi_pos]
  rw [h2]
  rw [tan_eq_sin_div_cos]
  have h3 : sin (π / 4 - π / 6) = (Real.sqrt 2 / 2) * (Real.sqrt 3 / 2) - (Real.sqrt 2 / 2) * (1 / 2) := by
    rw [sin_sub]
    simp [sin_pi_div_four, cos_pi_div_four, sin_pi_div_six, cos_pi_div_six]
    all_goals linarith
  have h4 : cos (π / 4 - π / 6) = (Real.sqrt 2 / 2) * (Real.sqrt 3 / 2) + (Real.sqrt 2 / 2) * (1 / 2) := by
    rw [cos_sub]
    simp [sin_pi_div_four, cos_pi_div_four, sin_pi_div_six, cos_pi_div_six]
    all_goals linarith
  rw [h3, h4]
  have h5 : 0 < Real.sqrt 2 := by positivity
  have h6 : 0 < Real.sqrt 3 := by positivity
  field_simp [(show Real.sqrt 2 ≠ 0 by positivity), (show Real.sqrt 3 ≠ 0 by positivity)]
  nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), 
          sq_nonneg (Real.sqrt 2 - Real.sqrt 3), Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)]