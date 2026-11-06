import Mathlib

theorem algebra_112433 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x ^ 2 + y ≥ x ^ 3 + y ^ 2) :
    x ^ 2 + y ^ 2 ≤ 2 := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1),
          sq_nonneg (x - y), sq_nonneg (x + y - 2), 
          mul_pos hx hy]