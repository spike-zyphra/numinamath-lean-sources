import Mathlib

open Real

theorem algebra_13630 : cos (π / 12) = (sqrt 6 + sqrt 2) / 4 := by
  have h1 : cos (π / 12) = cos (π / 4 - π / 6) := by 
    ring_nf
  rw [h1]
  rw [cos_sub]
  have h2 : cos (π / 4) = Real.sqrt 2 / 2 := by 
    rw [cos_pi_div_four]
  have h3 : sin (π / 4) = Real.sqrt 2 / 2 := by 
    rw [sin_pi_div_four]
  have h4 : cos (π / 6) = Real.sqrt 3 / 2 := by
    rw [cos_pi_div_six]
  have h5 : sin (π / 6) = 1 / 2 := by
    rw [sin_pi_div_six]
  rw [h2, h3, h4, h5]
  have h6 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num)]
    all_goals norm_num
  have eq1 : (Real.sqrt 2 / 2 : ℝ) * (Real.sqrt 3 / 2 : ℝ) = Real.sqrt 6 / 4 := by
    calc
      (Real.sqrt 2 / 2 : ℝ) * (Real.sqrt 3 / 2 : ℝ) = (Real.sqrt 2 * Real.sqrt 3) / 4 := by ring
      _ = Real.sqrt 6 / 4 := by rw [h6]
  have eq2 : (Real.sqrt 2 / 2 : ℝ) * (1 / 2 : ℝ) = Real.sqrt 2 / 4 := by
    ring
  rw [eq1, eq2]
  ring