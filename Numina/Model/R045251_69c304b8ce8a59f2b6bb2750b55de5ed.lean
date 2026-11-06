import Mathlib

open Real Set
open scoped Real

theorem algebra_284940 : 1 / sin (10 * π / 180) - 4 * sin (70 * π / 180) = 2 := by
  have h1 : sin (70 * π / 180) = cos (20 * π / 180) := by
    have h2 : 70 * π / 180 = Real.pi / 2 - 20 * π / 180 := by
      linarith [Real.pi_pos]
    rw [h2]
    rw [sin_pi_div_two_sub]
  have h2 : cos (20 * π / 180) = 2 * (cos (10 * π / 180))^2 - 1 := by 
    have h3 : 20 * π / 180 = 2 * (10 * π / 180) := by 
      ring
    rw [h3]
    rw [cos_two_mul]
  have h3 : 4 * sin (70 * π / 180) = 4 * (2 * (cos (10 * π / 180))^2 - 1) := by
    rw [h1, h2]
    all_goals nlinarith
  have sin_pos : sin (10 * π / 180) > 0 := by 
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h4 : 1 / sin (10 * π / 180) - 4 * sin (70 * π / 180) = 
      (1 - 4 * sin (10 * π / 180) * (2 * (cos (10 * π / 180))^2 - 1)) / sin (10 * π / 180) := by
    rw [h3]
    field_simp [show sin (10 * π / 180) ≠ 0 by linarith [sin_pos]]
    <;> ring
  rw [h4]
  have h5 : 1 - 4 * sin (10 * π / 180) * (2 * (cos (10 * π / 180))^2 - 1) = 2 * sin (10 * π / 180) := by
    have h6 : sin (30 * π / 180) = 1 / 2 := by 
      have h8 : 30 * π / 180 = π / 6 := by 
        ring_nf
      rw [h8]
      exact sin_pi_div_six
    have h9 : 2 * sin (10 * π / 180) * cos (20 * π / 180) = 
      sin (30 * π / 180) - sin (10 * π / 180) := by
      have h99 : 2 * sin (10 * π / 180) * cos (20 * π / 180) = 
          sin (10 * π / 180 + 20 * π / 180) + sin (10 * π / 180 - 20 * π / 180) := by 
        rw [sin_add, sin_sub]
        ring
      have h10 : sin (10 * π / 180 + 20 * π / 180) = sin (30 * π / 180) := by 
        ring_nf
      have h11 : sin (10 * π / 180 - 20 * π / 180) = - sin (10 * π / 180) := by 
        have h8 : 10 * π / 180 - 20 * π / 180 = - (10 * π / 180) := by 
          ring_nf
        rw [h8]
        rw [sin_neg]
        <;> ring_nf
      rw [h99, h10, h11]
      ring_nf
    have h55 : 1 - 4 * sin (10 * π / 180) * (2 * (cos (10 * π / 180))^2 - 1) = 1 -4 * sin (10 * π / 180) * cos (20 * π / 180) := by
      have hcos : 2 * (cos (10 * π / 180))^2 - 1 = cos (20 * π / 180) := by 
        linarith [ h2 ]
      rw [hcos]
    have h56 : 1 -4 * sin (10 * π / 180) * cos (20 * π / 180) = 2 * sin (10 * π / 180) := by
      nlinarith [ h9, h6, Real.sin_sq_add_cos_sq (10 * π / 180), Real.sin_sq_add_cos_sq (20 * π / 180) ]
    linarith [ h55, h56 ]
  rw [h5]
  field_simp [ sin_pos ]