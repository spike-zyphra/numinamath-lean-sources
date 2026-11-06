import Mathlib

theorem algebra_230294 (z w : ℂ) : Complex.exp z * Complex.exp w = Complex.exp (z + w) := by 
  rw [Complex.exp_add]