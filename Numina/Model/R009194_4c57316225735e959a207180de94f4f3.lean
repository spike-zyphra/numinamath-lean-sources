import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_146493 {f : ℝ → ℝ} (hf : f = λ x => sin x / (1 + cos x)) :
    f (π / 3) * f (2 * π / 3) = 1 := by 
  have h1 : f (π / 3) = sin (π / 3) / (1 + cos (π / 3)) := by 
    rw [hf]
  have h2 : f (2 * π / 3) = sin (2 * π / 3) / (1 + cos (2 * π / 3)) := by 
    rw [hf]
  rw [h1, h2]
  have h3 : sin (π / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  have h4 : cos (π / 3) = 1 / 2 := Real.cos_pi_div_three
  have h5 : sin (2 * π / 3) = Real.sqrt 3 / 2 := by 
    have h6 : 2 * π / 3 = π - (π / 3) := by 
      ring
    rw [h6]
    rw [Real.sin_pi_sub]
    rw [Real.sin_pi_div_three]
  have h7 : cos (2 * π / 3) = -1 / 2 := by 
    have h8 : 2 * π / 3 = π - (π / 3) := by 
      ring
    rw [h8]
    rw [Real.cos_pi_sub]
    rw [Real.cos_pi_div_three]
    all_goals norm_num
  rw [h3, h4, h5, h7]
  field_simp
  <;> ring_nf <;> norm_num
  <;> ring