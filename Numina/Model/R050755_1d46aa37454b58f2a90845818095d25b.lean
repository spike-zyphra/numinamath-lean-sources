import Mathlib

theorem algebra_322021 {x y : ℝ} (hx : x ≥ y) (hy : y ≥ 1) (h : 2 * x ^ 2 - x * y - 5 * x + y + 4 = 0) :
    x + y = 4 := by 
  nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x - y), h, hy, hx]