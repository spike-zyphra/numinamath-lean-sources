import Mathlib

theorem algebra_167585 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h1 : 204000000 * x = 603000000 * y) (h2 : 1604 * x = 120 * y) :
    6000000 * x = 434000000 * y := by
  linarith