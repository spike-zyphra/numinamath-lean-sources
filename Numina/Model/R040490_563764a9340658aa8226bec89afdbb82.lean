import Mathlib

open Real

theorem algebra_315349 : sin (35 * π / 180) ^ 2 + sin (85 * π / 180) ^ 2 -
    cos (5 * π / 180) * cos (55 * π / 180) = 3 / 4 := by
  have h1 : sin (85 * π / 180) = cos (5 * π / 180) := by
    have h2 : 85 * π / 180 = π / 2 - 5 * π / 180 := by
      ring_nf
    rw [h2]
    rw [sin_pi_div_two_sub]
  have h2 : sin (35 * π / 180) = sin (30 * π / 180 + 5 * π / 180) := by
    ring_nf
  have h3 : cos (55 * π / 180) = cos (60 * π / 180 - 5 * π / 180) := by
    ring_nf
  have h4 : sin (30 * π / 180 + 5 * π / 180) = sin (30 * π / 180) * cos (5 * π / 180) + cos (30 * π / 180) * sin (5 * π / 180) := by
    rw [sin_add]
  have h5 : cos (60 * π / 180 - 5 * π / 180) = cos (60 * π / 180) * cos (5 * π / 180) + sin (60 * π / 180) * sin (5 * π / 180) := by
    rw [cos_sub]
  have h6 : 30 * π / 180 = π / 6 := by 
    ring_nf
  have h7 : 60 * π / 180 = π / 3 := by 
    ring_nf
  have h8 : sin (30 * π / 180) = 1 / 2 := by
    rw [h6]
    exact sin_pi_div_six
  have h9 : cos (30 * π / 180) = Real.sqrt 3 / 2 := by 
    rw [h6]
    have h10 : cos (π / 6) = Real.sqrt 3 / 2 := by 
      exact cos_pi_div_six
    exact h10
  have h10 : cos (60 * π / 180) = 1 / 2 := by 
    rw [h7]
    exact cos_pi_div_three
  have h11 : sin (60 * π / 180) = Real.sqrt 3 / 2 := by 
    rw [h7]
    have h12 : sin (π / 3) = Real.sqrt 3 / 2 := by 
      exact sin_pi_div_three
    exact h12
  rw [h1, h2, h4, h3, h5]
  rw [h8, h9, h10, h11]
  have h5' : sin (5 * π / 180) ^ 2 + cos (5 * π / 180) ^ 2 = 1 := by 
    exact Real.sin_sq_add_cos_sq (5 * π / 180)
  nlinarith [sq_nonneg (sin (5 * π / 180) - Real.sqrt 3 * cos (5 * π / 180)), sq_nonneg (cos (5 * π / 180) * Real.sqrt 3 - 2 * sin (5 * π / 180)), sq_nonneg (sin (5 * π / 180) * 2 - Real.sqrt 3), Real.sqrt_pos.mpr (show (0 : ℝ) < (3) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]