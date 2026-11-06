import Mathlib

open Real Set
open scoped Real

theorem algebra_194748 {a : ℝ} (ha : a = sin (30 * π / 180) + sin (300 * π / 180) + sin (3000 * π / 180)) :
    a = 1 / 2 := by
  have h1 : a = sin (30 * π / 180) + sin (300 * π / 180) + sin (3000 * π / 180) := by
    linarith [ha]
  rw [h1]
  have h2 : sin (30 * π / 180) = 1 / 2 := by
    have h1 : 30 * π / 180 = π / 6 := by 
      ring_nf
    rw [h1]
    exact sin_pi_div_six
  have h3 : sin (300 * π / 180) = -Real.sqrt 3 / 2 := by
    have h1 : 300 * π / 180 = 5 * π / 3 := by 
      ring_nf
    rw [h1]
    have h4 : 5 * π / 3 = 2 * π - π / 3 := by 
      linarith [pi_pos]
    rw [h4]
    have h5 : sin (2 * π - π / 3) = -sin (π / 3) := by 
      rw [sin_two_pi_sub]
    rw [h5]
    have h6 : sin (π / 3) = Real.sqrt 3 / 2 := by 
      exact sin_pi_div_three
    rw [h6]
    all_goals linarith
  have h4 : sin (3000 * π / 180) = Real.sqrt 3 / 2 := by
    have h1 : 3000 * π / 180 = (2 * π / 3) + 8 * (2 * π) := by
      nlinarith [pi_pos]
    have h7 : sin (3000 * π / 180) = sin ( (2 * π / 3) + 8 * (2 * π) ) := by
      rw [h1]
    rw [h7]
    have h8 : sin ( (2 * π / 3) + 8 * (2 * π) ) = sin (2 * π / 3) := by
      have h9 : ( (2 * π / 3) + 8 * (2 * π) ) = (2 * π / 3) + 8 * (2 * π) := by 
        ring_nf
      rw [h9]
      have h10 : sin ( (2 * π / 3) + 8 * (2 * π) ) = sin (2 * π / 3) := by 
        have h11 : sin ( (2 * π / 3) + 8 * (2 * π) ) = sin ( (2 * π / 3) + (8 : ℕ) * (2 * π) ) := by 
          ring_nf
        rw [h11]
        rw [Real.sin_add_nat_mul_two_pi]
      linarith [h10]
    rw [h8]
    have h9 : 2 * π / 3 = π - (π / 3) := by 
      linarith [pi_pos]
    rw [h9]
    have h10 : sin (π - (π / 3)) = sin (π / 3) := by
      rw [sin_pi_sub]
    rw [h10]
    have h11 : sin (π / 3) = Real.sqrt 3 / 2 := by 
      exact sin_pi_div_three
    rw [h11]
  rw [h2, h3, h4]
  all_goals linarith