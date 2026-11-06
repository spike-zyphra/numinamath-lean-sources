import Mathlib

theorem algebra_158232 {x y : ℝ} (hx : x ≥ 0) (hy : y ≥ 0)
    (h1 : 1000 * x = 3000 * y) (h2 : 1000 * y = 1500 * x + 2000) :
    y = 360 := by
  linarith