import Mathlib

theorem inequalities_211029 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h1 : x^2 > x + y) (h2 : x^4 > x^3 + y) : x^3 > x^2 + y := by
  nlinarith [sq_nonneg (x^2 - x - 1), sq_nonneg (x - 1), mul_pos hx (show 0 < x by linarith), sq_nonneg (x^2 - x), sq_nonneg (x^4 - x^3), sq_nonneg (y)]