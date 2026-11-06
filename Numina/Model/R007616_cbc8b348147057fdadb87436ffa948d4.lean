import Mathlib

theorem algebra_9472 (x : ℝ) (hx : x^2 - 6 * x + 5 = 0) : x = 1 ∨ x = 5 := by
  have h : (x - 1) * (x - 5) = 0 := by
    linarith
  cases' (mul_eq_zero.mp h) with h1 h2
  · left
    linarith
  · right
    linarith