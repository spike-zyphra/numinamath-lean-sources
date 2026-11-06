import Mathlib

theorem algebra_1539 (x : ℝ) (h : x^2 - x - 1994 = 1994^2) :
    x = -1994 ∨ x = 1995 := by
  have h1 : x^2 - x - 1994 - (1994 : ℝ) ^ 2 = 0 := by
    linarith
  have h2 : (x - 1995) * (x + 1994) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case x - 1995 = 0 so x = 1995
    right
    linarith
  · -- Case x + 1994 = 0 so x = -1994
    left
    linarith