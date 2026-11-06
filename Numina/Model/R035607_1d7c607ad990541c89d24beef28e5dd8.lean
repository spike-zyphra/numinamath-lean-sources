import Mathlib

open Real Set
open scoped Real

theorem algebra_4477 : tan (π / 12) = 2 - sqrt 3 := by
  have htan : tan (π / 12) = sin (π / 12) / cos (π / 12) := by 
    rw [tan_eq_sin_div_cos]
  rw [htan]
  have h1 : sin (π / 12) = (Real.sqrt 2 / 2) * (Real.sqrt 3 / 2) - (Real.sqrt 2 / 2) * (1 / 2) := by
    have h1 : sin (π / 12) = sin (π / 4 - π / 6) := by
      ring_nf
    rw [h1]
    rw [sin_sub]
    have h1 : sin (π / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    have h2 : cos (π / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    have h3 : sin (π / 6) = 1 / 2 := by
      exact sin_pi_div_six
    have h4 : cos (π / 6) = Real.sqrt 3 / 2 := by
      exact cos_pi_div_six
    simp [h1, h2, h3, h4]
    <;> ring
  have h2 : cos (π / 12) = (Real.sqrt 2 / 2) * (Real.sqrt 3 / 2) + (Real.sqrt 2 / 2) * (1 / 2) := by 
    have h1 : cos (π / 12) = cos (π / 4 - π / 6) := by
      ring_nf
    rw [h1]
    rw [cos_sub]
    have h1 : cos (π / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    have h2 : sin (π / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    have h3 : cos (π / 6) = Real.sqrt 3 / 2 := by
      exact cos_pi_div_six
    have h4 : sin (π / 6) = 1 / 2 := by
      exact sin_pi_div_six
    simp [h1, h2, h3, h4]
    <;> ring
  rw [h1, h2]
  have h3 : Real.sqrt 3 > 0 := by positivity
  have h4 : Real.sqrt 3 + 1 > 0 := by nlinarith
  have h5 : Real.sqrt 2 > 0 := by positivity
  have h6 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by linarith)
  have h7 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by linarith)
  field_simp [(show Real.sqrt 3 + 1 ≠ 0 by nlinarith), (show Real.sqrt 2 ≠ 0 by positivity)]
  nlinarith [Real.sqrt_pos.mpr (by norm_num : (0: ℝ) < 3), Real.sqrt_pos.mpr (by norm_num : (0: ℝ) < 2), 
    Real.sq_sqrt (show (0 : ℝ) ≤ 3 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by linarith), 
    mul_pos (show Real.sqrt 3 > 0 by positivity) (show Real.sqrt 2 > 0 by positivity), h6, h7, sq_nonneg (Real.sqrt 3 - 1)
  ]