import Mathlib

theorem algebra_21380 (x y : ℝ) (h : x^2 + y^2 - 6 = 6 * x + 2 * y) :
    (x - 3)^2 + (y - 1)^2 = 4^2 := by
  have h1 : x^2 + y^2 - 6 * x - 2 * y - 6 = 0 := by linarith [h]
  have h2 : (x - 3) ^ 2 + (y - 1) ^ 2 = 16 := by
    nlinarith [h1]
  linarith [h2]