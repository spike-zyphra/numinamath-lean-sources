import Mathlib

theorem algebra_1637 (a b : ℝ) (h : a > 0) (h' : b > 0) (h1 : 15 * a = 15 * b + 18 * (a - b)) (h2 : 18 * (a - b) = 50 * a) : 10000 / b = 25 := by
  nlinarith