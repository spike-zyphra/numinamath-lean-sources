import Mathlib

theorem algebra_1620 (x y z : ℝ) (h : x^2 + y^2 + z^2 = 3) :
  7 * x + 25 * y + z ≤ 45 := by
  nlinarith [sq_nonneg (x - 7 / 15), sq_nonneg (y - 5 / 3), sq_nonneg (z - 1 / 15)]