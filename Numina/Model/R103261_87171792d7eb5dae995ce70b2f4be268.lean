import Mathlib

theorem algebra_237419 (x y : ℝ) (h : x^2 + y^2 + 3 * x * y = 2015) :
    x * y ≤ 403 := by 
  have h1 : (x - y) ^ 2 ≥ 0 := sq_nonneg (x - y)
  nlinarith [sq_nonneg (x - y)]