import Mathlib

open Real
open scoped BigOperators

theorem inequalities_213943 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
  (h₃ : a^2 + b^2 = c^2) :
  a^4 + a^2 * b^2 + b^4 ≥ 3 / 4 * c^4 := by
  have h₄ : c^2 = a^2 + b^2 := by linarith
  have h₅ : c^4 = (a^2 + b^2) ^ 2 := by calc
    c^4 = (c^2)^2 := by ring
    _ = (a^2 + b^2)^2 := by rw [h₄]
  rw [h₅]
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a^2 + b^2 - 2 * a * b), sq_nonneg (a^2 - b^2)]