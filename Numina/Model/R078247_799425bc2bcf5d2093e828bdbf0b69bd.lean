import Mathlib

theorem algebra_123090 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h1 : x * 99 = y * 500) (h2 : (x - y) * 98 = y * 300) :
    x + y = 400 := by
  nlinarith