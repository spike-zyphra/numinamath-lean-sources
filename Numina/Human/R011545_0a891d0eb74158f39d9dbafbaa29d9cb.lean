import Mathlib

theorem algebra_1539 (x : ℝ) (h : x^2 - x - 1994 = 1994^2) :
    x = -1994 ∨ x = 1995 := by
  have : (x + 1994) * (x - 1995) = 0 := by linarith
  cases' (mul_eq_zero.mp this) with h₁ h₂
  · left
    linarith
  · right
    linarith