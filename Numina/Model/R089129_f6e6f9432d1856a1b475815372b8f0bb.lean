import Mathlib

theorem algebra_249262 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h1 : 5 * x = 3 * y) (h2 : 5 * y = 4 * x) :
    (x - y) / y * 100 = 52 := by
  have h3 : x = 0 := by
    linarith [h1, h2]
  linarith