import Mathlib

open Real Set
open scoped Real

theorem algebra_5777 : sin π * cosh (2 * π) + I * cos π * sinh (2 * π) =
    I * (exp (-2 * π) - exp (2 * π)) / 2 := by
  have h1 : sin π = 0 := by 
    rw [sin_pi]
  have h2 : cos π = -1 := by 
    rw [cos_pi]
  rw [h1]
  rw [h2]
  simp [sinh_eq, cosh_eq]
  <;> ring_nf <;> simp [exp_neg, mul_add, mul_neg] <;> ring