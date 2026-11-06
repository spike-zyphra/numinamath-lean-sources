import Mathlib

open Real Set
open scoped Real

theorem algebra_154146 : sin ((1998 * π / 180) + (237 * π / 180)) *
    sin ((1998 * π / 180) - (1653 * π / 180)) = -1 / 4 := by
  -- First angle: 2235° = 75° + 6 * 360° ≅ 75°, so it's angle is (75 * π / 180) in radians.
  have h1 : sin ((1998 * π / 180) + (237 * π / 180)) = sin (5 * π / 12) := by
    have h1 : (1998 * π / 180) + (237 * π / 180) = 5 * π / 12 + 12 * π := by
      ring_nf
      <;> linarith
    rw [h1]
    have h2 : sin (5 * π / 12 + 12 * π) = sin (5 * π / 12) := by
      have h3 : sin (5 * π / 12 + 12 * π) = sin (5 * π / 12 + 6 * (2 * π)) := by
        ring_nf
      rw [h3]
      have h4 : sin (5 * π / 12 + 6 * (2 * π)) = sin (5 * π / 12) := by
        have h5 : sin (5 * π / 12 + 6 * (2 * π)) = sin (5 * π / 12 + (6 : ℕ) * (2 * π)) := by
          ring_nf
        rw [h5]
        rw [Real.sin_add_nat_mul_two_pi]
      linarith
    exact h2
  -- Second angle: 345° ≅ -15°, so it's angle is (-π / 12) in radians.
  have h2 : sin ((1998 * π / 180) - (1653 * π / 180)) = -sin (π / 12) := by
    have h3 : (1998 * π / 180) - (1653 * π / 180) = (23 * π / 12 : ℝ) := by
      linarith [pi_pos]
    rw [h3]
    have h4 : sin (23 * π / 12) = -sin (π / 12) := by
      have h5 : 23 * π / 12 = 2 * π - (π / 12 : ℝ) := by
        linarith [pi_pos]
      rw [h5]
      have h6 : sin (2 * π - (π / 12 : ℝ)) = -sin (π / 12 : ℝ) := by
        rw [sin_two_pi_sub]
      exact h6
    exact h4
  rw [h1, h2]
  have h3 : sin (5 * π / 12) * sin (π / 12) = 1 / 4 := by
    have h4 : sin (5 * π / 12) * sin (π / 12) = (1 / 2) * (cos ((5 * π / 12 : ℝ) - (π / 12 : ℝ)) - cos ((5 * π / 12 : ℝ) + (π / 12 : ℝ)) ) := by
      rw [cos_sub, cos_add]
      ring_nf
    have h5 : (5 * π / 12 : ℝ) - (π / 12 : ℝ) = π / 3 := by 
      linarith
    have h6 : (5 * π / 12 : ℝ) + (π / 12 : ℝ) = π / 2 := by 
      linarith
    rw [h4]
    rw [h5, h6]
    have h7 : cos (π / 3) = 1 / 2 := Real.cos_pi_div_three
    have h8 : cos (π / 2) = 0 := by 
      rw [cos_pi_div_two]
    rw [h7, h8]
    all_goals linarith
  have h4 : sin (5 * π / 12) * (-sin (π / 12)) = - (sin (5 * π / 12) * sin (π / 12)) := by
    ring
  rw [h4]
  rw [h3]
  all_goals linarith