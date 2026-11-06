import Mathlib

theorem algebra_1345 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h1 : (100 + x) * 15 / 100 = 100 * 15 / 100 + x * 5 / 100) (h2 : (100 + y) * 15 / 100 = 100 * 15 / 100 - y * 5 / 100) :
    x = 50 ∧ y = 50 := by
  have hx_zero : x = 0 := by
    linarith
  have hy_zero : y = 0 := by
    linarith
  linarith [hx, hy, hx_zero, hy_zero]