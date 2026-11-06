import Mathlib

open Real Set
open scoped Real

theorem algebra_153885 : sin (75 * π / 180) + sin (15 * π / 180) = sqrt 6 / 2 := by
  have h1 : sin (75 * π / 180) + sin (15 * π / 180) = 2 * sin (45 * π / 180) * cos (30 * π / 180) := by
    rw [show 75 * π / 180 = 45 * π / 180 + 30 * π / 180 by ring]
    rw [show 15 * π / 180 = 45 * π / 180 - 30 * π / 180 by ring]
    rw [sin_add, sin_sub]
    ring_nf
  have h2 : sin (45 * π / 180) = Real.sqrt 2 / 2 := by
    have h1 : 45 * π / 180 = Real.pi / 4 := by
      ring_nf
    rw [h1]
    rw [sin_pi_div_four]
  have h3 : cos (30 * π / 180) = Real.sqrt 3 / 2 := by 
    have h1 : 30 * π / 180 = Real.pi / 6 := by
      ring_nf
    rw [h1]
    rw [cos_pi_div_six]
  rw [h1, h2, h3]
  have h4 : 2 * (Real.sqrt 2 / 2) * (Real.sqrt 3 / 2) = Real.sqrt 6 / 2 := by
    have h5 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
      rw [← Real.sqrt_mul (by norm_num)]
      all_goals norm_num
    linarith [h5]
  linarith [h4]