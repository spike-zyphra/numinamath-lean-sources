import Mathlib

open Real

theorem algebra_164318 : cos (70 * π / 180) + 8 * cos (20 * π / 180) * cos (40 * π / 180) * cos (80 * π / 180) = 2 * (cos (35 * π / 180))^2 := by
  have h1 : cos (70 * π / 180) = sin (20 * π / 180) := by
    have h2 : 70 * π / 180 = π / 2 - (20 * π / 180) := by
      ring_nf
      <;> linarith [Real.pi_pos]
    rw [h2]
    rw [cos_pi_div_two_sub]
  have h3 : 8 * cos (20 * π / 180) * cos (40 * π / 180) * cos (80 * π / 180) = 1 := by
    have h4 : sin (8 * (20 * π / 180)) = 8 * sin (20 * π / 180) * cos (20 * π / 180) * cos (40 * π / 180) * cos (80 * π / 180) := by
      have h9 : sin (8 * (20 * π / 180)) = 2 * sin (4 * (20 * π / 180)) * cos (4 * (20 * π / 180)) := by
        rw [show 8 * (20 * π / 180) = 2 * (4 * (20 * π / 180)) by ring]
        rw [sin_two_mul]
      have h10 : sin (4 * (20 * π / 180)) = 2 * sin (2 * (20 * π / 180)) * cos (2 * (20 * π / 180)) := by
        rw [show 4 * (20 * π / 180) = 2 * (2 * (20 * π / 180)) by  ring]
        rw [sin_two_mul]
      have h11 : sin (2 * (20 * π / 180)) = 2 * sin (20 * π / 180) * cos (20 * π / 180) := by
        rw [sin_two_mul]
      rw [h9, h10, h11]
      ring_nf
    have h5 : sin (8 * (20 * π / 180)) = sin (20 * π / 180) := by
      have h10 : 8 * (20 * π / 180) = π - (20 * π / 180) := by
        ring_nf
        <;> linarith [Real.pi_pos]
      rw [h10]
      rw [sin_pi_sub]
    have h7 : sin (20 * π / 180) ≠ 0 := by
      have h1 : 0 < 20 * π / 180 := by
        nlinarith [Real.pi_pos]
      have h2 : sin (20 * π / 180) > 0 := by
        apply sin_pos_of_pos_of_lt_pi
        all_goals linarith [Real.pi_pos]
      nlinarith
    have eq1 : 8 * cos (20 * π / 180) * cos (40 * π / 180) * cos (80 * π / 180) = 1 := by
      apply (mul_left_inj' h7).mp
      linarith [h4, h5]
    linarith
  rw [h1, h3]
  have h5 : 2 * (cos (35 * π / 180))^2 = 1 + cos (70 * π / 180) := by
    have h6 : 2 * (cos (35 * π / 180))^2 = 1 + cos (2 * (35 * π / 180)) := by
      have h7 : cos (2 * (35 * π / 180)) = 2 * (cos (35 * π / 180))^2 - 1 := by
        rw [cos_two_mul]
        all_goals ring_nf <;> nlinarith
      linarith [h7]
    have h7 : 2 * (35 * π / 180) = 70 * π / 180 := by
      ring_nf
      <;> nlinarith
    rw [h7] at h6
    linarith [h6]
  rw [h5]
  have h8 : cos (70 * π / 180) = sin (20 * π / 180) := by
    have h2 : 70 * π / 180 = π / 2 - (20 * π / 180) := by
      ring_nf
      <;> linarith [Real.pi_pos]
    rw [h2]
    rw [cos_pi_div_two_sub]
  rw [h8]
  all_goals linarith
  all_goals linarith