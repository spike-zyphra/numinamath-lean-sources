import Mathlib

open Real

theorem algebra_94866 (c : ℝ) (hc : c = 2 * π / 11) :
    sin (3 * c) * sin (6 * c) * sin (9 * c) * sin (12 * c) * sin (15 * c) /
    (sin c * sin (2 * c) * sin (3 * c) * sin (4 * c) * sin (5 * c)) = 1 := by
  rw [hc]
  have h1 : sin (3 * (2 * π / 11)) = sin (6 * π / 11) := by
    ring_nf
  have h2 : sin (6 * (2 * π / 11)) = sin (12 * π / 11) := by
    ring_nf
  have h3 : sin (9 * (2 * π / 11)) = sin (18 * π / 11) := by
    ring_nf
  have h4 : sin (12 * (2 * π / 11)) = sin (24 * π / 11) := by
    ring_nf
  have h5 : sin (15 * (2 * π / 11)) = sin (30 * π / 11) := by
    ring_nf
  have h6 : sin ( (2 * π / 11) ) = sin (2 * π / 11) := by
    rfl
  have h7 : sin (2 * (2 * π / 11)) = sin (4 * π / 11) := by
    ring_nf
  have h8 : sin (4 * (2 * π / 11)) = sin (8 * π / 11) := by
    ring_nf
  have h9 : sin (5 * (2 * π / 11)) = sin (10 * π / 11) := by
    ring_nf
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9]

  have h10 : sin (12 * π / 11) = -sin (π / 11) := by
    have h12 : 12 * π / 11 = π + (π / 11) := by
      linarith [Real.pi_pos]
    rw [h12]
    rw [sin_add, sin_pi, cos_pi]
    ring_nf
  have h11 : sin (18 * π / 11) = -sin (7 * π / 11) := by
    have h18 : 18 * π / 11 = π + (7 * π / 11) := by
      linarith [Real.pi_pos]
    rw [h18]
    rw [sin_add, sin_pi, cos_pi]
    ring_nf
  have h12 : sin (24 * π / 11) = sin (2 * π / 11) := by
    have h24 : 24 * π / 11 = 2 * π + (2 * π / 11) := by
      linarith [Real.pi_pos]
    rw [h24]
    simp [sin_add, sin_two_pi, cos_two_pi]
  have h13 : sin (30 * π / 11) = sin (8 * π / 11) := by
    have h30 : 30 * π / 11 = 2 * π + (8 * π / 11) := by
      linarith [Real.pi_pos]
    rw [h30]
    simp [sin_add, sin_two_pi, cos_two_pi]
  have h14 : sin (8 * π / 11) = sin (3 * π / 11) := by
    have h811 : 8 * π / 11 = π - (3 * π / 11) := by
      linarith [Real.pi_pos]
    rw [h811]
    rw [sin_pi_sub]
  have h15 : sin (10 * π / 11) = sin (π / 11) := by
    have h1011 : 10 * π / 11 = π - (π / 11) := by
      linarith [Real.pi_pos]
    rw [h1011]
    rw [sin_pi_sub]

  simp only [h10, h11, h12, h13, h14, h15]

  have h17 : sin (7 * π / 11) = sin (π - (4 * π / 11)) := by
    ring_nf
  have h18 : sin (π - (4 * π / 11)) = sin (4 * π / 11) := by
    rw [sin_pi_sub]
  have h19 : sin (3 * π / 11) = sin (3 * π / 11) := by
    rfl
  have h19 : sin (4 * π / 11) = sin (4 * π / 11) := by
    rfl
  simp only [h17, h18, h19, h19]

  have h1 : sin (2 * π / 11) ≠ 0 := by
    have h1 : sin (2 * π / 11) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    nlinarith
  have h2 : sin (4 * π / 11) ≠ 0 := by
    have h1 : sin (4 * π / 11) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    nlinarith
  have h3 : sin (6 * π / 11) ≠ 0 := by
    have h1 : sin (6 * π / 11) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    nlinarith
  have h4 : sin (π / 11) ≠ 0 := by
    have h1 : sin (π / 11) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    nlinarith
  have h5 : sin (3 * π / 11) ≠ 0 := by
    have h1 : sin (3 * π / 11) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    nlinarith
  have h6 : sin (8 * π / 11) ≠ 0 := by
    have h1 : sin (8 * π / 11) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    nlinarith
  field_simp [h1, h2, h3, h4, h5, h6]
  <;> nlinarith [Real.sin_sq_add_cos_sq (2 * π / 11), Real.sin_sq_add_cos_sq (4 * π / 11), Real.sin_sq_add_cos_sq (6 * π / 11), Real.sin_sq_add_cos_sq (π / 11), Real.sin_sq_add_cos_sq (3 * π / 11), Real.sin_sq_add_cos_sq (8 * π / 11)]