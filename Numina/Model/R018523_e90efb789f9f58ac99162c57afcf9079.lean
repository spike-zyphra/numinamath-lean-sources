import Mathlib

open Real Set
open scoped Real

theorem inequalities_197761 : (1/8 < sin (20 * π/180) * sin (50 * π/180) * sin (70 * π/180) ∧
    sin (20 * π/180) * sin (50 * π/180) * sin (70 * π/180) < 1/4) := by
  have h1 : sin (20 * π/180) * sin (50 * π/180) * sin (70 * π/180) = 1/4 * sin (4 * π / 9) := by
    have h2 : sin (70 * π / 180) = cos (π / 9) := by
      have h3 : 70 * π / 180 = π / 2 - π / 9 := by
        nlinarith [Real.pi_pos]
      rw [h3]
      rw [sin_pi_div_two_sub]
    have h4 : sin (50 * π / 180) = cos (2 * π / 9) := by
      have h5 : 50 * π / 180 = π / 2 - 2 * π / 9 := by
        nlinarith [Real.pi_pos]
      rw [h5]
      rw [sin_pi_div_two_sub]
    have h6 : sin (20 * π/180) = sin (π / 9) := by
      ring_nf
    rw [h6, h4, h2]
    have h7 : sin (π / 9) * cos (2 * π / 9) * cos (π / 9) = 1 / 4 * sin (4 * π / 9) := by
      have h71 : sin (π / 9) * cos (π / 9) = (1 / 2) * sin (2 * π / 9) := by
        have h8 : sin (2 * π / 9) = 2 * sin (π / 9) * cos (π / 9) := by
          rw [show 2 * π / 9 = 2 * (π / 9) by ring]
          rw [sin_two_mul]
        linarith
      have h72 : (1 / 2) * sin (2 * π / 9) * cos (2 * π / 9) = (1 / 4) * sin (4 * π / 9) := by
        have h9 : sin (4 * π / 9) = 2 * sin (2 * π / 9) * cos (2 * π / 9) := by
          rw [show 4 * π / 9 = 2 * (2 * π / 9) by ring]
          rw [sin_two_mul]
        nlinarith
      calc
        sin (π / 9) * cos (2 * π / 9) * cos (π / 9)
          = (sin (π / 9) * cos (π / 9)) * cos (2 * π / 9) := by ring
        _ = ( (1 / 2) * sin (2 * π / 9) ) * cos (2 * π / 9) := by rw [h71]
        _ = (1 / 4) * sin (4 * π / 9) := by
          rw [h72]
          <;> ring
    linarith
  constructor
  · -- Prove the first inequality: 1/8 < sin (20 * π/180) * sin (50 * π/180) * sin (70 * π/180)
    rw [h1]
    have h8 : sin (4 * π / 9) > 1 / 2 := by
      have h9 : 4 * π / 9 > Real.pi / 6 := by
        nlinarith [Real.pi_gt_31415, Real.pi_lt_31416]
      have h10 : sin (4 * π / 9) > sin (Real.pi / 6) := by
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals
          nlinarith [Real.pi_pos]
      have h11 : sin (Real.pi / 6) = 1 / 2 := by
        rw [sin_pi_div_six]
      linarith [h11, h10]
    linarith [h8]
  · -- Prove the second inequality: sin (20 * π/180) * sin (50 * π/180) * sin (70 * π/180) < 1/4
    rw [h1]
    have h40 : sin (4 * π / 9) < 1 := by
      have h20 : sin (4 * π / 9) < sin (Real.pi / 2) := by
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals
          nlinarith [Real.pi_pos]
      have h10 : sin (Real.pi / 2) = 1 := by
        rw [sin_pi_div_two]
      linarith [h10, h20]
    linarith [h40]