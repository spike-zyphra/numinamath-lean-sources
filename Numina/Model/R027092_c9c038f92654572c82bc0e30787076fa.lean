import Mathlib

open Real

theorem inequalities_197702 : (1 / 8 < cos (20 * π / 180) * cos (40 * π / 180) * cos (70 * π / 180)) ∧
    (cos (20 * π / 180) * cos (40 * π / 180) * cos (70 * π / 180) < 1 / 4) := by
  have h1 : cos (70 * π / 180) = sin (20 * π / 180) := by
    have h2 : 70 * π / 180 = π / 2 - 20 * π / 180 := by 
      linarith [pi_pos]
    rw [h2]
    rw [cos_pi_div_two_sub]
  
  have h2 : cos (40 * π / 180) = 2 * cos (20 * π / 180) ^ 2 - 1 := by
    have h3 : 40 * π / 180 = 2 * (20 * π / 180) := by
      ring_nf
    rw [h3]
    rw [cos_two_mul]

  have h4 : cos (20 * π / 180) * cos (40 * π / 180) * cos (70 * π / 180) = sin (4 * (20 * π / 180)) / 4 := by
    rw [h1]
    rw [h2]
    have h5 : sin (4 * (20 * π / 180)) = 2 * sin (2 * (20 * π / 180)) * cos (2 * (20 * π / 180)) := by 
      rw [show 4 * (20 * π / 180) = 2 * (2 * (20 * π / 180)) by ring]
      rw [sin_two_mul]

    have h6 : sin (2 * (20 * π / 180)) = 2 * sin (20 * π / 180) * cos (20 * π / 180) := by
      rw [sin_two_mul]
    
    have h7 : cos (2 * (20 * π / 180)) = 2 * cos (20 * π / 180) ^ 2 - 1 := by
      rw [cos_two_mul]
    rw [h5, h6, h7]
    ring_nf

  have h5 : 0 < 20 * π / 180 := by 
    nlinarith [pi_pos]

  have h6 : 20 * π / 180 < π / 2 := by 
    nlinarith [pi_pos]

  have h7 : 0 < sin (4 * (20 * π / 180)) := by
    have h8 : 0 < 4 * (20 * π / 180) := by 
      nlinarith [pi_pos]
    have h9 : 4 * (20 * π / 180) < π := by 
      nlinarith [pi_pos]
    apply sin_pos_of_pos_of_lt_pi
    all_goals nlinarith

  have h8 : sin (4 * (20 * π / 180)) < 1 := by
    have h9 : 4 * (20 * π / 180) > 0 := by 
      nlinarith [pi_pos]
    have h9' : 4 * (20 * π / 180) < π / 2 := by
      nlinarith [pi_pos]
    have h10 : sin (4 * (20 * π / 180)) < sin (π / 2) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals 
        linarith
    have h11 : sin (π / 2) = 1 := sin_pi_div_two
    linarith [h10, h11]

  have h9 : sin (4 * (20 * π / 180)) > 1 / 2 := by
    have h10 : 4 * (20 * π / 180) > π / 6 := by
      nlinarith [pi_pos]
    have h11 : sin (4 * (20 * π / 180)) > sin (π / 6) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals 
        linarith
    have h12 : sin (π / 6) = 1 / 2 := by 
      rw [sin_pi_div_six]
    linarith [h11, h12]

  constructor
  · -- Proof of 1/8 < cos(20) * cos(40) * cos(70)
    have h6 : cos (20 * π / 180) * cos (40 * π / 180) * cos (70 * π / 180) = sin (4 * (20 * π / 180)) / 4 := h4
    rw [h6]
    nlinarith [h9, h7]

  · -- Proof of cos(20) * cos(40) * cos(70) < 1/4
    have h6 : cos (20 * π / 180) * cos (40 * π / 180) * cos (70 * π / 180) = sin (4 * (20 * π / 180)) / 4 := h4
    rw [h6]
    nlinarith [h8, h7]