import Mathlib

open Real

theorem calculus_22470 : arcsin (sin (66 * π / 180) - sin (54 * π / 180)) = 6 * π / 180 := by 
  have h1 : sin (66 * π / 180) - sin (54 * π / 180) = sin (6 * π / 180) := by 
    have h2 : sin (66 * π / 180) - sin (54 * π / 180) =
      2 * cos ( (66 * π / 180 + 54 * π / 180) / 2 ) * sin ( (66 * π / 180 - 54 * π / 180) / 2 ) := by 
      rw [sin_sub_sin]
      <;> ring_nf <;> ring
    have h3 : (66 * π / 180 + 54 * π / 180) / 2 = π / 3 := by 
      linarith [Real.pi_pos]
    have h4 : (66 * π / 180 - 54 * π / 180) / 2 = π / 30 := by 
      linarith [Real.pi_pos]
    have h5 : cos (π / 3) = 1 / 2 := by 
      exact cos_pi_div_three
    have h5' : sin (6 * π / 180) = sin (π / 30) := by 
      have h6 : 6 * π / 180 = π / 30 := by 
        linarith [Real.pi_pos]
      rw [h6]
    rw [h2, h3, h4, h5, h5']
    ring
  rw [h1]
  have h1 : arcsin (sin (6 * π / 180)) = 6 * π / 180 := by
    have h2 : -(Real.pi / 2) ≤ 6 * Real.pi / 180 := by 
      linarith [Real.pi_pos]
    have h3 : 6 * Real.pi / 180 ≤ Real.pi / 2 := by 
      linarith [Real.pi_pos]
    rw [arcsin_sin]
    all_goals 
      linarith [Real.pi_pos]
  exact h1