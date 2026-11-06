import Mathlib

open Real

theorem algebra_2637 : sin (π / 12) * sin (5 * π / 12) = 1 / 4 := by 
  have h1 : sin (5 * π / 12) = cos (π / 12) := by
    have h2 : 5 * π / 12 = π / 2 - π / 12 := by
      linarith [Real.pi_pos]
    rw [h2]
    rw [sin_pi_div_two_sub]
  rw [h1]
  have h2 : sin (π / 12) * cos (π / 12) = (1 / 2) * sin (2 * (π / 12)) := by
    have h3 : sin (2 * (π / 12)) = 2 * sin (π / 12) * cos (π / 12) := by
      rw [sin_two_mul]
    linarith [h3]
  have h3 : 2 * (π / 12) = π / 6 := by
    ring_nf
  have h4 : sin (π / 6) = 1 / 2 := by
    exact sin_pi_div_six
  have h5 : (1 / 2) * sin (2 * (π / 12)) = (1 / 2) * sin (π / 6) := by
    rw [h3]
  have h6 : (1 / 2) * sin (π / 6) = 1 / 4 := by
    rw [h4]
    norm_num
  rw [h2, h5, h6]