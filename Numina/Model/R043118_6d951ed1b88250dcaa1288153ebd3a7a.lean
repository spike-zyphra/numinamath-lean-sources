import Mathlib

theorem algebra_286523 (x y p : ℝ) (h1 : 3 * x - 2 * y = 4 - p) (h2 : 4 * x - 3 * y = 2 + p) (h3 : x > y) :
    p > 1 := by
  have h4 : x - y > 0 := by linarith
  have h5 : x - y = -2 + 2 * p := by
    linarith [h1, h2]
  linarith [h4, h5]