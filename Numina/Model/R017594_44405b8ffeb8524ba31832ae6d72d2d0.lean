import Mathlib

open Real Set
open scoped Real

theorem algebra_221834 : sqrt (sin (15 * π / 180)^4 + 4 * cos (15 * π / 180)^2) -
    sqrt (cos (15 * π / 180)^4 + 4 * sin (15 * π / 180)^2) = sqrt 3 / 2 := by

  have h1 : sin (15 * π / 180)^4 + 4 * cos (15 * π / 180)^2 = (1 + cos (15 * π / 180)^2) ^ 2 := by
    have h2 : sin (15 * π / 180) ^ 2 = 1 - cos (15 * π / 180) ^ 2 := by 
      have h3 : sin (15 * π / 180) ^ 2 + cos (15 * π / 180) ^ 2 = 1 := by 
        exact Real.sin_sq_add_cos_sq (15 * π / 180)
      linarith
    calc
      sin (15 * π / 180) ^ 4 + 4 * cos (15 * π / 180) ^ 2
        = (sin (15 * π / 180) ^ 2) ^ 2 + 4 * cos (15 * π / 180) ^ 2 := by ring
      _ = (1 - cos (15 * π / 180) ^ 2) ^ 2 + 4 * cos (15 * π / 180) ^ 2 := by rw [h2]
      _ = (1 + cos (15 * π / 180) ^ 2) ^ 2 := by ring

  have h2 : cos (15 * π / 180) ^ 4 + 4 * sin (15 * π / 180) ^ 2 = (1 + sin (15 * π / 180) ^ 2) ^ 2 := by
    have h3 : cos (15 * π / 180) ^ 2 = 1 - sin (15 * π / 180) ^ 2 := by
      have h4 : sin (15 * π / 180) ^ 2 + cos (15 * π / 180) ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq (15 * π / 180)
      linarith
    calc
      cos (15 * π / 180) ^ 4 + 4 * sin (15 * π / 180) ^ 2
        = (cos (15 * π / 180) ^ 2) ^ 2 + 4 * sin (15 * π / 180) ^ 2 := by ring
      _ = (1 - sin (15 * π / 180) ^ 2) ^ 2 + 4 * sin (15 * π / 180) ^ 2 := by rw [h3]
      _ = (1 + sin (15 * π / 180) ^ 2) ^ 2 := by ring
  
  have h3 : sqrt (sin (15 * π / 180)^4 + 4 * cos (15 * π / 180)^2) = 1 + cos (15 * π / 180) ^ 2 := by
    rw [h1]
    have h4 : (0 : ℝ) ≤ (1 + cos (15 * π / 180) ^ 2 : ℝ) := by
      positivity
    rw [Real.sqrt_sq (h4)]

  have h4 : sqrt (cos (15 * π / 180) ^ 4 + 4 * sin (15 * π / 180) ^ 2) = 1 + sin (15 * π / 180) ^ 2 := by
    rw [h2]
    have h5 : (0 : ℝ) ≤ (1 + sin (15 * π / 180) ^ 2 : ℝ) := by
      positivity
    rw [Real.sqrt_sq (h5)]

  rw [h3, h4]
  have h5 : cos (15 * π / 180) ^ 2 - sin (15 * π / 180) ^ 2 = sqrt 3 / 2 := by
    have h6 : cos (15 * π / 180) ^ 2 - sin (15 * π / 180) ^ 2 = cos (2 * (15 * π / 180)) := by
      rw [cos_two_mul, sin_sq]
      ring_nf
    rw [h6]
    have h7 : 2 * (15 * π / 180) = Real.pi / 6 := by
      ring_nf
    rw [h7]
    have h8 : cos (Real.pi / 6) = Real.sqrt 3 / 2 := by 
      exact Real.cos_pi_div_six
    rw [h8]
    all_goals ring_nf
  nlinarith [h5, Real.sqrt_nonneg 3, Real.sin_sq_add_cos_sq (15 * π / 180)]