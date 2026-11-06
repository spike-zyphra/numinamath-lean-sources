import Mathlib

theorem algebra_199589 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x + 300 = y - x) (h2 : y + 500 = x - y) :
    x + y = 400 := by
  linarith