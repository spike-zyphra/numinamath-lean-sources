import Mathlib

theorem algebra_212142 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h1 : 2 * x * 14 + 2 * y * 14 = 2) (h2 : 4 * x * 28 + 2 * y * 28 = 2) :
    6 * x * 6 + 6 * y * 6 = 5 := by
  nlinarith