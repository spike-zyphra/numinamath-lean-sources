import Mathlib

open Real

theorem algebra_164003 : (cos (66 * π / 180) * cos (6 * π / 180) +
    cos (84 * π / 180) * cos (24 * π / 180)) /
    (cos (65 * π / 180) * cos (5 * π / 180) +
    cos (85 * π / 180) * cos (25 * π / 180)) = 1 := by
  have h1 : cos (66 * π / 180) = sin (24 * π / 180) := by
    have h2 : 66 * π / 180 = π / 2 - 24 * π / 180 := by
      ring
    rw [h2]
    rw [cos_pi_div_two_sub]

  have h2 : cos (84 * π / 180) = sin (6 * π / 180) := by
    have h3 : 84 * π / 180 = π / 2 - 6 * π / 180 := by
      ring
    rw [h3]
    rw [cos_pi_div_two_sub]

  have h3 : cos (65 * π / 180) = sin (25 * π / 180) := by
    have h4 : 65 * π / 180 = π / 2 - 25 * π / 180 := by
      ring
    rw [h4]
    rw [cos_pi_div_two_sub]

  have h4 : cos (85 * π / 180) = sin (5 * π / 180) := by
    have h5 : 85 * π / 180 = π / 2 - 5 * π / 180 := by
      ring
    rw [h5]
    rw [cos_pi_div_two_sub]

  have h5 : cos (66 * π / 180) * cos (6 * π / 180) + cos (84 * π / 180) * cos (24 * π / 180) = 1 / 2 := by
    rw [h1, h2]
    have h6 : sin (24 * π / 180) * cos (6 * π / 180) + sin (6 * π / 180) * cos (24 * π / 180) = sin ( (24 * π / 180 + 6 * π / 180) ) := by
      rw [sin_add]
      <;> ring_nf <;> ring
    rw [h6]
    have h7 : 24 * π / 180 + 6 * π / 180 = π / 6 := by
      linarith [pi_pos]
    rw [h7]
    rw [sin_pi_div_six]

  have h6 : cos (65 * π / 180) * cos (5 * π / 180) + cos (85 * π / 180) * cos (25 * π / 180) = 1 / 2 := by
    rw [h3, h4]
    have h7 : sin (25 * π / 180) * cos (5 * π / 180) + sin (5 * π / 180) * cos (25 * π / 180) = sin ( (25 * π / 180 + 5 * π / 180) ) := by
      rw [sin_add]
      <;> ring_nf <;> ring
    rw [h7]
    have h8 : 25 * π / 180 + 5 * π / 180 = π / 6 := by
      linarith [pi_pos]
    rw [h8]
    rw [sin_pi_div_six]

  have h7 : cos (66 * π / 180) * cos (6 * π / 180) + cos (84 * π / 180) * cos (24 * π / 180) = cos (65 * π / 180) * cos (5 * π / 180) + cos (85 * π / 180) * cos (25 * π / 180) := by
    linarith [h5, h6]

  have h8 : cos (65 * π / 180) * cos (5 * π / 180) + cos (85 * π / 180) * cos (25 * π / 180) ≠ 0 := by
    have h7_pos : cos (65 * π / 180) * cos (5 * π / 180) + cos (85 * π / 180) * cos (25 * π / 180) > 0 := by
      have h8 : cos (65 * π / 180) * cos (5 * π / 180) + cos (85 * π / 180) * cos (25 * π / 180) = 1 / 2 := h6
      linarith
    have h7_ne : cos (65 * π / 180) * cos (5 * π / 180) + cos (85 * π / 180) * cos (25 * π / 180) ≠ 0 := by
      linarith [h7_pos]
    exact h7_ne

  rw [show cos (66 * π / 180) * cos (6 * π / 180) + cos (84 * π / 180) * cos (24 * π / 180) = cos (65 * π / 180) * cos (5 * π / 180) + cos (85 * π / 180) * cos (25 * π / 180) by linarith [h7]]
  all_goals
    field_simp [h8]
    <;> linarith