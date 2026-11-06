import Mathlib

theorem algebra_271848 : Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) * Real.cos (6 * Real.pi / 7) = 1 / 8 := by
  have h1 : Real.cos (6 * Real.pi / 7) = - Real.cos (Real.pi / 7) := by
    have h2 : 6 * Real.pi / 7 = Real.pi - Real.pi / 7 := by
      linarith [Real.pi_pos]
    rw [h2]
    rw [Real.cos_pi_sub]
  have h3 : Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) * Real.cos (6 * Real.pi / 7) =
      - (Real.cos (Real.pi / 7) * Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7)) := by
    rw [h1]
    <;> ring
  have h4 : Real.sin (Real.pi / 7) ≠ 0 := by
    have h5 : Real.sin (Real.pi / 7) > 0 := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    linarith [h5]
  have h5 : Real.sin (8 * (Real.pi / 7)) = 8 * Real.sin (Real.pi / 7) * Real.cos (Real.pi / 7) * Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) := by
    have h1 : Real.sin (8 * (Real.pi / 7)) = 2 * Real.sin (4 * (Real.pi / 7)) * Real.cos (4 * (Real.pi / 7)) := by
      rw [show 8 * (Real.pi / 7) = 2 * (4 * (Real.pi / 7)) by ring]
      rw [Real.sin_two_mul]
    have h2 : Real.sin (4 * (Real.pi / 7)) = 2 * Real.sin (2 * (Real.pi / 7)) * Real.cos (2 * (Real.pi / 7)) := by
      rw [show 4 * (Real.pi / 7) = 2 * (2 * (Real.pi / 7)) by ring]
      rw [Real.sin_two_mul]
    have h3 : Real.sin (2 * (Real.pi / 7)) = 2 * Real.sin (Real.pi / 7) * Real.cos (Real.pi / 7) := by
      rw [show 2 * (Real.pi / 7) = 2 * (Real.pi / 7) by ring]
      rw [Real.sin_two_mul]
    rw [h1, h2, h3]
    ring_nf
  have h6 : Real.sin (8 * (Real.pi / 7)) = - Real.sin (Real.pi / 7) := by 
    have h7 : 8 * (Real.pi / 7) = Real.pi + (Real.pi / 7) := by
      linarith [Real.pi_pos]
    rw [h7]
    have h8 : Real.sin (Real.pi + (Real.pi / 7)) = - Real.sin (Real.pi / 7) := by
      rw [Real.sin_add, Real.sin_pi, Real.cos_pi]
      ring_nf
    rw [h8]
  have h8 : - Real.sin (Real.pi / 7) = 8 * Real.sin (Real.pi / 7) * Real.cos (Real.pi / 7) * Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) := by
    linarith [h5, h6]
  have h9 : Real.cos (Real.pi / 7) * Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) = -1 / 8 := by
    have h7' : Real.sin (Real.pi / 7) ≠ 0 := h4
    have eq1 : Real.cos (Real.pi / 7) * Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) = -1 / 8 := by
      apply (mul_left_inj' h7').mp
      linarith
    linarith [eq1]
  have h10 : - (Real.cos (Real.pi / 7) * Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7)) = 1 / 8 := by
    linarith [h9]
  rw [h3]
  rw [h10]