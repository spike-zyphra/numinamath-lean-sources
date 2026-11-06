import Mathlib

open Real

theorem algebra_99380 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : 3 * x + 2 * y = 12) :
    x * y ≤ 6 := by
  have h1 : y = (12 - 3 * x) / 2 := by
    linarith
  rw [h1]
  nlinarith [sq_nonneg (x - 2)]