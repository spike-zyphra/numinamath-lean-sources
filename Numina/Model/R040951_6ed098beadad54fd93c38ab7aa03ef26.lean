import Mathlib

open Real

theorem algebra_100184 {x : ℝ}
    (hx : x = sin (π / 8) ^ 4 + cos (π / 8) ^ 4 + sin (7 * π / 8) ^ 4 + cos (7 * π / 8) ^ 4) :
    36 * x = 54 := by
  have h1 : sin (7 * π / 8) = sin (π / 8) := by 
    have h2 : 7 * π / 8 = π - (π / 8) := by 
      linarith [Real.pi_pos]
    rw [h2]
    rw [sin_pi_sub]
  have h1' : cos (7 * π / 8) = -cos (π / 8) := by 
    have h2 : 7 * π / 8 = π - (π / 8) := by 
      linarith [Real.pi_pos]
    rw [h2]
    rw [cos_pi_sub]
  have hx2 : x = 2 * (sin (π / 8) ^ 4 + cos (π / 8) ^ 4) := by
    rw [hx, h1, h1']
    ring_nf
  have h3 : sin (π / 8) ^ 4 + cos (π / 8) ^ 4 = 1 - 2 * (sin (π / 8) * cos (π / 8)) ^ 2 := by
    have h4 : sin (π / 8) ^ 2 + cos (π / 8) ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq (π / 8)
    have h5 : sin (π / 8) ^ 4 + cos (π / 8) ^ 4 = (sin (π / 8) ^ 2 + cos (π / 8) ^ 2) ^ 2 - 2 * (sin (π / 8) * cos (π / 8)) ^ 2 := by
      ring_nf
    rw [h4] at h5
    linarith [h5]
  have h4 : sin (π / 8) * cos (π / 8) = Real.sqrt 2 / 4 := by
    have h5 : sin (π / 4) = Real.sqrt 2 / 2 := by
      rw [Real.sin_pi_div_four]
    have h6 : sin (π / 4) = 2 * sin (π / 8) * cos (π / 8) := by
      rw [←Real.sin_two_mul (π / 8)]
      ring_nf
    rw [h5] at h6
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by linarith), Real.sqrt_nonneg 2]
  rw [hx2, h3, h4]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith)]