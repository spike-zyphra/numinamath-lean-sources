import Mathlib

theorem algebra_275763 (x y : ℝ) (h : x^2 - y^2 = 0) :
    (x = y ∨ x = -y) := by
  have h1 : (x - y) * (x + y) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp h1) with h2 h3

  · left
    linarith

  · right
    linarith