import Mathlib

theorem algebra_11762 (x y : ℝ) (h : x^2/36 + (y+5)^2/16 = 0) :
    y ≤ -5 := by
  nlinarith [sq_nonneg x, sq_nonneg (y + 5)]