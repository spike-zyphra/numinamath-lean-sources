import Mathlib

theorem inequalities_65602 (p q : ℝ) (x : ℝ) (hx : x^3 + p * x + q = 0) :
    4 * q * x ≤ p^2 := by 
  have h1 : q = -x^3 - p * x := by linarith
  rw [h1]
  nlinarith [sq_nonneg (x^2 * 2 + p), sq_nonneg (x^2 + p), sq_nonneg (x^2 - p)]