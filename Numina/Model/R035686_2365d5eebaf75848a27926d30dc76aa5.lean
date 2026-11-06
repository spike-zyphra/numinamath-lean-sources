import Mathlib
open Complex


theorem algebra_230306 (x : ℝ) : Complex.exp (Complex.I * x) = Real.cos x + Complex.I * Real.sin x := by
  have h1 : Complex.exp (Complex.I * x) = Complex.exp (x * Complex.I) := by 
    rw [show Complex.I * x = x * Complex.I by ring]
  rw [h1]
  simp [Complex.exp_mul_I]
  <;> ring