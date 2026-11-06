import Mathlib

open Real

theorem algebra_124901 (x : ℝ) :
    sin (x + π / 3) + 2 * sin (x - π / 3) - sqrt 3 * cos (2 * π / 3 - x) = 0 := by
  have h1 : sin (x + π / 3) = sin x * cos (π / 3) + cos x * sin (π / 3) := by 
    rw [sin_add]
  have h2 : sin (x - π / 3) = sin x * cos (π / 3) - cos x * sin (π / 3) := by 
    rw [sin_sub]
  have h3 : cos (2 * π / 3 - x) = cos (2 * π / 3) * cos x + sin (2 * π / 3) * sin x := by 
    rw [cos_sub]
  have h4 : cos (π / 3) = 1 / 2 := by 
    exact cos_pi_div_three
  have h5 : sin (π / 3) = sqrt 3 / 2 := by 
    exact sin_pi_div_three
  have h6 : cos (2 * π / 3) = -1 / 2 := by 
    have h7 : 2 * π / 3 = π - π / 3 := by 
      ring_nf
    rw [h7]
    rw [cos_pi_sub]
    rw [h4]
    all_goals ring
  have h8 : sin (2 * π / 3) = sqrt 3 / 2 := by 
    have h9 : 2 * π / 3 = π - π / 3 := by 
      ring_nf
    rw [h9]
    rw [sin_pi_sub]
    rw [h5]
    all_goals ring
  rw [h1, h2, h3]
  rw [h4, h5, h6, h8]
  ring_nf
  <;> simp [mul_add, mul_sub, add_mul, sub_mul, mul_comm]
  <;> ring_nf
  <;> simp [Real.sq_sqrt]
  <;> ring