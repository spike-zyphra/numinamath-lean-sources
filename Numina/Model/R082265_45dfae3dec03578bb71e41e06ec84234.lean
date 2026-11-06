import Mathlib

theorem algebra_176729 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h1 : x + y = 1 / 5) (h2 : x * 2 + y * 3 = 1 / 10) :
    x = 1 / 15 := by
  nlinarith