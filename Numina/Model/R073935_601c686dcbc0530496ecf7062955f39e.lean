import Mathlib

theorem algebra_110578 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h1 : 24 * 42 = x * 4 + y * 36) (h2 : 36 * 84 = x * 8 + y * 10) :
    x * 63 = 50 := by
  nlinarith