import Mathlib

open Real Set
open scoped Real

theorem algebra_276121 : sin (100 * π / 180) ^ 2 - sin (50 * π / 180) * sin (70 * π / 180) = 1 / 4 := by
  have h1 : sin (100 * π / 180) = cos (10 * π / 180) := by
    have h2 : 100 * π / 180 = Real.pi / 2 + 10 * π / 180 := by
      ring_nf
    rw [h2]
    rw [sin_add, sin_pi_div_two, cos_pi_div_two]
    all_goals ring
  have h11 : sin (100 * π / 180) ^ 2 = cos (10 * π / 180) ^ 2 := by
    rw [h1]
  have h3 : sin (50 * π / 180) = sin (60 * π / 180 - 10 * π / 180) := by
    ring_nf
  have h4 : sin (70 * π / 180) = sin (60 * π / 180 + 10 * π / 180) := by
    ring_nf
  have h5 : sin (60 * π / 180 - 10 * π / 180) = sin (60 * π / 180) * cos (10 * π / 180) - cos (60 * π / 180) * sin (10 * π / 180) := by
    rw [sin_sub]
  have h6 : sin (60 * π / 180 + 10 * π / 180) = sin (60 * π / 180) * cos (10 * π / 180) + cos (60 * π / 180) * sin (10 * π / 180) := by
    rw [sin_add]
  have h7 : sin (50 * π / 180) * sin (70 * π / 180) =
      (sin (60 * π / 180) * cos (10 * π / 180) - cos (60 * π / 180) * sin (10 * π / 180)) *
      (sin (60 * π / 180) * cos (10 * π / 180) + cos (60 * π / 180) * sin (10 * π / 180)) := by
    rw [h3, h4, h5, h6]
  rw [h11, h7]
  have h8 : sin (60 * π / 180) = Real.sqrt 3 / 2 := by 
    have h9 : 60 * π / 180 = π / 3 := by 
      ring_nf
    rw [h9]
    rw [sin_pi_div_three]
  have h10 : cos (60 * π / 180) = 1 / 2 := by 
    have h11 : 60 * π / 180 = π / 3 := by 
      ring_nf
    rw [h11]
    rw [cos_pi_div_three]
  rw [h8, h10]
  have h12 : cos (10 * π / 180) ^ 2 + sin (10 * π / 180) ^ 2 = 1 := by 
    exact Real.cos_sq_add_sin_sq (10 * π / 180)
  nlinarith [ Real.sin_sq_add_cos_sq (10 * π / 180), Real.sin_sq_add_cos_sq (60 * π / 180), sq_nonneg (cos (10 * π / 180) - sin (10 * π / 180) * Real.sqrt 3), sq_nonneg (cos (10 * π / 180) * Real.sqrt 3 - sin (10 * π / 180)), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ]