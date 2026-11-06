import Mathlib

open Real

theorem algebra_162191 : sin (π / 24) ^ 4 + cos (5 * π / 24) ^ 4 + sin (19 * π / 24) ^ 4 + cos (23 * π / 24) ^ 4 = 3 / 2 := by
  have h1 : sin (19 * π / 24) = sin (5 * π / 24) := by
    have h1 : 19 * π / 24 = π - (5 * π / 24) := by
      linarith [Real.pi_pos]
    rw [h1]
    rw [sin_pi_sub]
  have h2 : cos (23 * π / 24) = - cos (π / 24) := by
    have h2 : 23 * π / 24 = π - (π / 24) := by
      linarith [Real.pi_pos]
    rw [h2]
    rw [cos_pi_sub]
  rw [h1, h2]
  have h3 : sin (π / 24) ^ 4 + cos (π / 24) ^ 4 = 1 - 2 * (sin (π / 24) * cos (π / 24)) ^ 2 := by
    calc
      sin (π / 24) ^ 4 + cos (π / 24) ^ 4 = (sin (π / 24) ^ 2 + cos (π / 24) ^ 2) ^ 2 - 2 * (sin (π / 24) * cos (π / 24)) ^ 2 := by
        ring
      _ = (1) ^ 2 - 2 * (sin (π / 24) * cos (π / 24)) ^ 2 := by
        rw [Real.sin_sq_add_cos_sq (π / 24)]
      _ = 1 - 2 * (sin (π / 24) * cos (π / 24)) ^ 2 := by
        ring
  have h4 : sin (5 * π / 24) ^ 4 + cos (5 * π / 24) ^ 4 = 1 - 2 * (sin (5 * π / 24) * cos (5 * π / 24)) ^ 2 := by
    calc
      sin (5 * π / 24) ^ 4 + cos (5 * π / 24) ^ 4 = (sin (5 * π / 24) ^ 2 + cos (5 * π / 24) ^ 2) ^ 2 - 2 * (sin (5 * π / 24) * cos (5 * π / 24)) ^ 2 := by
        ring
      _ = (1) ^ 2 - 2 * (sin (5 * π / 24) * cos (5 * π / 24)) ^ 2 := by
        rw [Real.sin_sq_add_cos_sq (5 * π / 24)]
      _ = 1 - 2 * (sin (5 * π / 24) * cos (5 * π / 24)) ^ 2 := by
        ring
  have h5 : sin (π / 24) * cos (π / 24) = (1 / 2) * sin (2 * (π / 24)) := by
    rw [sin_two_mul]
    all_goals ring
  have h6 : sin (5 * π / 24) * cos (5 * π / 24) = (1 / 2) * sin (2 * (5 * π / 24)) := by
    rw [sin_two_mul]
    all_goals ring
  have h7 : sin (2 * (π / 24)) = sin (π / 12) := by
    ring_nf
  have h8 : sin (2 * (5 * π / 24)) = sin (5 * π / 12) := by
    ring_nf
  have h9 : sin (5 * π / 12) = cos (π / 12) := by
    have h9 : 5 * π / 12 = π / 2 - (π / 12) := by
      linarith [Real.pi_pos]
    rw [h9]
    rw [sin_pi_div_two_sub]
  have h10 : sin (π / 24) ^ 4 + cos (5 * π / 24) ^ 4 + sin (5 * π / 24) ^ 4 + (-cos (π / 24)) ^ 4 = (sin (π / 24) ^ 4 + cos (π / 24) ^ 4) + (sin (5 * π / 24) ^ 4 + cos (5 * π / 24) ^ 4) := by 
    ring
  rw [h10]
  rw [h3, h4]
  rw [h5, h6, h7, h8, h9]
  have h11 : sin (π / 12) ^ 2 + cos (π / 12) ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq (π / 12)
  nlinarith [Real.sin_sq_add_cos_sq (π / 24), Real.sin_sq_add_cos_sq (5 * π / 24), 
          Real.sin_sq_add_cos_sq (π / 12)]