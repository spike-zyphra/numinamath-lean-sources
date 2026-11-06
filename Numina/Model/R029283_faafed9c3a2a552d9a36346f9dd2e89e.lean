import Mathlib

open Real

theorem algebra_311497 : (cos (10 * π / 180))^2 + (cos (50 * π / 180))^2 -
    sin (40 * π / 180) * sin (80 * π / 180) = 3 / 4 := by
  have h1 : cos (50 * π / 180) = (1 / 2) * cos (10 * π / 180) + (Real.sqrt 3 / 2) * sin (10 * π / 180) := by 
    have h2 : 50 * π / 180 = Real.pi / 3 - 10 * π / 180 := by
      ring_nf
      <;> linarith [Real.pi_pos]
    rw [h2]
    rw [cos_sub]
    simp [cos_pi_div_three, sin_pi_div_three]
    <;> ring_nf
  have h3 : sin (40 * π / 180) = (1 / 2) * cos (10 * π / 180) + (Real.sqrt 3 / 2) * sin (10 * π / 180) := by
    have h4 : 40 * π / 180 = Real.pi / 6 + 10 * π / 180 := by
      ring_nf
      <;> linarith [Real.pi_pos]
    rw [h4]
    rw [sin_add]
    simp [sin_pi_div_six, cos_pi_div_six]
    <;> ring_nf
  have h5 : sin (80 * π / 180) = cos (10 * π / 180) := by
    have h6 : 80 * π / 180 = Real.pi / 2 - 10 * π / 180 := by
      ring_nf
      <;> linarith [Real.pi_pos]
    rw [h6]
    rw [sin_pi_div_two_sub]
  rw [h1, h3, h5]
  nlinarith [Real.cos_sq_add_sin_sq (10 * π / 180), Real.sin_sq_le_one (10 * π / 180), Real.cos_sq_le_one (10 * π / 180), sq_nonneg (cos (10 * π / 180) - sin (10 * π / 180) * Real.sqrt 3), sq_nonneg (cos (10 * π / 180) * Real.sqrt 3 + sin (10 * π / 180)), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]