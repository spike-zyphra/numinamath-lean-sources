import Mathlib

theorem algebra_172679 : Real.sin 3 > Real.sin (3 * Real.pi / 180) := by
  have h1 : Real.sin 3 = Real.sin (Real.pi - 3) := by 
    rw [show Real.pi - 3 = Real.pi - 3 by rfl]
    rw [Real.sin_pi_sub]
  have h2 : Real.sin (3 * Real.pi / 180) = Real.sin (Real.pi / 60) := by
    have h3 : 3 * Real.pi / 180 = Real.pi / 60 := by 
      linarith
    rw [h3]
  rw [h1, h2]
  have h3 : Real.pi - 3 > 0 := by
    linarith [Real.pi_gt_three]
  have h4 : Real.pi / 60 > 0 := by 
    linarith [Real.pi_pos]
  have h5 : Real.pi - 3 > Real.pi / 60 := by 
    nlinarith [Real.pi_gt_31415, Real.pi_lt_31416]
  have h6 : Real.pi - 3 < Real.pi / 2 := by 
    nlinarith [Real.pi_gt_three, Real.pi_lt_31416]
  have h7 : Real.pi / 60 < Real.pi / 2 := by
    nlinarith [Real.pi_pos, Real.pi_gt_three, Real.pi_lt_31416]
  have h8 : Real.sin (Real.pi - 3) > Real.sin (Real.pi / 60) := by
    have h6' : Real.pi - 3 < Real.pi / 2 := h6
    have h7' : Real.pi / 60 < Real.pi / 2 := h7
    have h5' : Real.pi - 3 > Real.pi / 60 := h5
    have h4' : Real.pi / 60 > 0 := h4
    have h3' : Real.pi - 3 > 0 := h3
    have h9 : Real.sin (Real.pi / 60) < Real.sin (Real.pi - 3) := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
      linarith [Real.pi_gt_three, Real.pi_lt_31416]
    linarith
  linarith [h8]