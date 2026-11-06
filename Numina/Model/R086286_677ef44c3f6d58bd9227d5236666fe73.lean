import Mathlib

theorem algebra_1663 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
  (h1 : 2 * x + 5 * y ≥ 10) (h2 : 3 * x + 4 * y ≥ 12) :
  8 * x + 13 * y ≥ 34 := by
  linarith