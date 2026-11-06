import Mathlib

theorem algebra_307461 : Real.cos (Real.pi / 9) * Real.cos (2 * Real.pi / 9) * Real.cos (3 * Real.pi / 9) * Real.cos (4 * Real.pi / 9) = 1 / 16 := by 
  have h1 : Real.cos (3 * Real.pi / 9) = 1 / 2 := by
    have h2 : 3 * Real.pi / 9 = Real.pi / 3 := by
      ring
    rw [h2]
    exact Real.cos_pi_div_three
  have h4 : Real.sin (8 * Real.pi / 9) = Real.sin (Real.pi / 9) := by
    have h2 : Real.sin (8 * Real.pi / 9) = Real.sin (Real.pi - (Real.pi / 9)) := by 
      ring_nf
    have h3 : Real.sin (Real.pi - (Real.pi / 9)) = Real.sin (Real.pi / 9) := by 
      rw [Real.sin_pi_sub]
    rw [h2, h3]
  have h5 : Real.cos (Real.pi / 9) * Real.cos (2 * Real.pi / 9) * Real.cos (4 * Real.pi / 9) = (Real.sin (8 * Real.pi / 9)) / (8 * Real.sin (Real.pi / 9)) := by
    have h6 : Real.sin (8 * Real.pi / 9) = 8 * Real.sin (Real.pi / 9) * (Real.cos (Real.pi / 9) * Real.cos (2 * Real.pi / 9) * Real.cos (4 * Real.pi / 9)) := by
      have h11 : Real.sin (8 * Real.pi / 9) = 2 * Real.sin (4 * Real.pi / 9) * Real.cos (4 * Real.pi / 9) := by 
        rw [show 8 * Real.pi / 9 = 2 * (4 * Real.pi / 9) by ring]
        rw [Real.sin_two_mul]
      have h12 : Real.sin (4 * Real.pi / 9) = 2 * Real.sin (2 * Real.pi / 9) * Real.cos (2 * Real.pi / 9) := by 
        rw [show 4 * Real.pi / 9 = 2 * (2 * Real.pi / 9) by ring]
        rw [Real.sin_two_mul]
      have h13 : Real.sin (2 * Real.pi / 9) = 2 * Real.sin (Real.pi / 9) * Real.cos (Real.pi / 9) := by 
        rw [show 2 * Real.pi / 9 = 2 * (Real.pi / 9) by ring]
        rw [Real.sin_two_mul]
      rw [h11, h12, h13]
      ring
    have h7 : Real.sin (Real.pi / 9) ≠ 0 := by 
      apply ne_of_gt 
      apply Real.sin_pos_of_pos_of_lt_pi 
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    field_simp [h7] at *
    nlinarith 
  have h9 : Real.cos (Real.pi / 9) * Real.cos (2 * Real.pi / 9) * Real.cos (3 * Real.pi / 9) * Real.cos (4 * Real.pi / 9) = (Real.cos (Real.pi / 9) * Real.cos (2 * Real.pi / 9) * Real.cos (4 * Real.pi / 9)) * Real.cos (3 * Real.pi / 9) := by
    ring
  rw [h9, h1]
  rw [h5]
  rw [h4]
  have h10 : Real.sin (Real.pi / 9) ≠ 0 := by 
    apply ne_of_gt 
    apply Real.sin_pos_of_pos_of_lt_pi 
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  field_simp [h10]
  <;> linarith [Real.sin_pos_of_pos_of_lt_pi (show (0 : ℝ) < Real.pi / 9 by linarith [Real.pi_pos] ) (show Real.pi / 9 < Real.pi by linarith [Real.pi_pos] ) ]