import Mathlib

open Real

theorem inequalities_160066 : sin (3 * π / 180) / sin (4 * π / 180) > sin (1 * π / 180) / sin (2 * π / 180) := by
  have h1 : sin (4 * π / 180) > 0 := by
    have h1 : 0 < 4 * π / 180 := by
      linarith [Real.pi_pos]
    have h2 : sin (4 * π / 180) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith [Real.pi_pos]
    exact h2
  have h2 : sin (2 * π / 180) > 0 := by
    have h1 : 0 < 2 * π / 180 := by
      linarith [Real.pi_pos]
    have h2 : sin (2 * π / 180) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith [Real.pi_pos]
    exact h2
  have h3 : sin (3 * π / 180) * sin (2 * π / 180) > sin (1 * π / 180) * sin (4 * π / 180) := by
    have h4 : sin (3 * π / 180) * sin (2 * π / 180) = (1 / 2) * (cos (3 * π / 180 - 2 * π / 180) - cos (3 * π / 180 + 2 * π / 180)) := by
      rw [show 3 * π / 180 - 2 * π / 180 = (3 * π / 180 - 2 * π / 180) by ring]
      rw [show 3 * π / 180 + 2 * π / 180 = (3 * π / 180 + 2 * π / 180) by ring]
      have h5 : sin (3 * π / 180) * sin (2 * π / 180) = (1 / 2) * (cos (3 * π / 180 - 2 * π / 180) - cos (3 * π / 180 + 2 * π / 180)) := by
        rw [cos_sub, cos_add]
        ring_nf
        <;> simp [sin_sq, cos_sq]
        <;> ring_nf
        <;> simp [sin_sq, cos_sq]
        <;> ring_nf
      linarith [h5]
    have h5 : sin (1 * π / 180) * sin (4 * π / 180) = (1 / 2) * (cos (1 * π / 180 - 4 * π / 180) - cos (1 * π / 180 + 4 * π / 180)) := by
      rw [show 1 * π / 180 - 4 * π / 180 = (1 * π / 180 - 4 * π / 180) by ring]
      rw [show 1 * π / 180 + 4 * π / 180 = (1 * π / 180 + 4 * π / 180) by  ring]
      have h6 : sin (1 * π / 180) * sin (4 * π / 180) = (1 / 2) * (cos (1 * π / 180 - 4 * π / 180) - cos (1 * π / 180 + 4 * π / 180)) := by
        rw [cos_sub, cos_add]
        ring_nf
        <;> simp [sin_sq, cos_sq]
        <;> ring_nf
        <;> simp [sin_sq, cos_sq]
        <;> ring_nf
      linarith [h6]
    rw [h4, h5]
    have h7 : cos (3 * π / 180 - 2 * π / 180) = cos (π / 180) := by 
      ring_nf
    have h8 : cos (1 * π / 180 - 4 * π / 180) = cos (3 * π / 180) := by 
      have h9 : 1 * π / 180 - 4 * π / 180 = - (3 * π / 180) := by
        linarith [Real.pi_pos]
      rw [h9]
      rw [cos_neg]
      all_goals linarith [Real.pi_pos]
    have h9 : cos (3 * π / 180 + 2 * π / 180) = cos (5 * π / 180) := by 
      ring_nf
    have h10 : cos (1 * π / 180 + 4 * π / 180) = cos (5 * π / 180) := by
      ring_nf
    rw [h7, h8, h9, h10]
    have h11 : cos (π / 180) > cos (3 * π / 180) := by 
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      all_goals linarith [Real.pi_pos]
    linarith 
  have h4 : sin (4 * π / 180) > 0 := h1
  have h5 : sin (2 * π / 180) > 0 := h2
  have h6 : sin (3 * π / 180) / sin (4 * π / 180) - sin (1 * π / 180) / sin (2 * π / 180) > 0 := by
    have h7 : sin (3 * π / 180) * sin (2 * π / 180) > sin (1 * π / 180) * sin (4 * π / 180) := h3
    have h8 : sin (4 * π / 180) > 0 := h1
    have h9 : sin (2 * π / 180) > 0 := h2
    have h10 : sin (3 * π / 180) / sin (4 * π / 180) - sin (1 * π / 180) / sin (2 * π / 180) = (sin (3 * π / 180) * sin (2 * π / 180) - sin (1 * π / 180) * sin (4 * π / 180)) / (sin (4 * π / 180) * sin (2 * π / 180)) := by
      field_simp
      <;> linarith 
    rw [h10]
    apply div_pos
    linarith 
    positivity
  linarith 
  all_goals linarith 
  all_goals linarith 
  all_goals linarith 
  all_goals linarith 
  all_goals linarith
  all_goals linarith [Real.pi_pos]