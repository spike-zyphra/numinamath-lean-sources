import Mathlib

theorem algebra_108007 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x * 16 = y * 20) (h2 : x * 60 = y * 30) :
    x + y = 180 := by
  nlinarith