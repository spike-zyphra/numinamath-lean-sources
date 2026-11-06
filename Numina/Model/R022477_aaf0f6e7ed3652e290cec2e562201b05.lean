import Mathlib

open Real

theorem calculus_23104 : sin (π/12) + sin (3*π/12) + sin (5*π/12) +
    sin (7*π/12) + sin (9*π/12) + sin (11*π/12) = sqrt 2 + sqrt 6 := by

  have h1 : sin (3 * π / 12) = Real.sqrt 2 / 2 := by
    have h1 : 3 * π / 12 = π / 4 := by ring
    rw [h1]
    rw [sin_pi_div_four]

  have h2 : sin (9 * π / 12) = Real.sqrt 2 / 2 := by 
    have h2 : 9 * π / 12 = π - (3 * π / 12) := by ring
    rw [h2]
    rw [sin_pi_sub]
    rw [h1]

  have h3 : sin (11 * π / 12) = sin (π / 12) := by
    have h3 : 11 * π / 12 = π - (π / 12) := by ring
    rw [h3]
    rw [sin_pi_sub]

  have h4 : sin (7 * π / 12) = sin (5 * π / 12) := by
    have h4 : 7 * π / 12 = π - (5 * π / 12) := by ring
    rw [h4]
    rw [sin_pi_sub]

  have h5 : sin (π / 12) + sin (5 * π / 12) = Real.sqrt 6 / 2 := by

    have h1 : sin (π / 12) + sin (5 * π / 12) = 2 * sin ( (π / 12 + 5 * π / 12) / 2 ) * cos ( (5 * π / 12 - π / 12) / 2 ) := by 
      rw [show (π / 12 : ℝ) = ( (π / 12 + 5 * π / 12) / 2 - (5 * π / 12 - π / 12) / 2 ) by ring]
      rw [show (5 * π / 12 : ℝ) = ( (π / 12 + 5 * π / 12) / 2 + (5 * π / 12 - π / 12) / 2 ) by ring]
      rw [sin_add, sin_sub]
      ring

    have h2 : (π / 12 + 5 * π / 12) / 2 = π / 4 := by ring

    have h3 : (5 * π / 12 - π / 12) / 2 = π / 6 := by ring

    rw [h1, h2, h3]

    have h4 : sin (π / 4) = Real.sqrt 2 / 2 := by 
      rw [sin_pi_div_four]

    have h5 : cos (π / 6) = Real.sqrt 3 / 2 := by 
      rw [cos_pi_div_six]

    rw [h4, h5]

    have h6 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by 
      rw [← Real.sqrt_mul (by norm_num)]
      all_goals norm_num

    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (6 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]

  calc 
    sin (π / 12) + sin (3 * π / 12) + sin (5 * π / 12) + 
      sin (7 * π / 12) + sin (9 * π / 12) + sin (11 * π / 12)
        = sin (π / 12) + (Real.sqrt 2 / 2) + sin (5 * π / 12) + sin (7 * π / 12) + (Real.sqrt 2 / 2) + sin (11 * π / 12) := by 
          rw [h1, h2]
    _ = sin (π / 12) + (Real.sqrt 2 / 2) + sin (5 * π / 12) + sin (5 * π / 12) + (Real.sqrt 2 / 2) + sin (π / 12) := by 
      rw [h3, h4]
    _ = 2 * (sin (π / 12) + sin (5 * π / 12)) + Real.sqrt 2 := by ring
    _ = 2 * (Real.sqrt 6 / 2) + Real.sqrt 2 := by 
      rw [h5]
    _ = Real.sqrt 2 + Real.sqrt 6 := by ring