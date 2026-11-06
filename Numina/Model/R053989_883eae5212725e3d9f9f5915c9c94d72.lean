import Mathlib

open Real

theorem algebra_153815 : (sin (11 * π / 180) * cos (15 * π / 180) +
    sin (15 * π / 180) * cos (11 * π / 180)) /
    (sin (18 * π / 180) * cos (12 * π / 180) +
    sin (12 * π / 180) * cos (18 * π / 180)) = 2 * sin (26 * π / 180) := by
  have h1 : sin (11 * π / 180) * cos (15 * π / 180) + sin (15 * π / 180) * cos (11 * π / 180) = sin (26 * π / 180) := by
    rw [show sin (26 * π / 180) = sin (11 * π / 180 + 15 * π / 180) by ring]
    rw [sin_add]
    ring
  have h2 : sin (18 * π / 180) * cos (12 * π / 180) + sin (12 * π / 180) * cos (18 * π / 180) = sin (30 * π / 180) := by
    rw [show sin (30 * π / 180) = sin (18 * π / 180 + 12 * π / 180) by ring]
    rw [sin_add]
    ring
  have h3 : sin (30 * π / 180) = 1 / 2 := by
    have h3 : 30 * π / 180 = π / 6 := by
      ring_nf
      <;> linarith [Real.pi_pos]
    rw [h3]
    rw [sin_pi_div_six]
  rw [h1, h2, h3]
  ring_nf <;> simp [Real.sin_pos_of_pos_of_lt_pi] <;> ring