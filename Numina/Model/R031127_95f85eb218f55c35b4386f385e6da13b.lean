import Mathlib

theorem inequalities_108138 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x^3 + y^3 ≤ x^2 + y^2) :
    x * y ≤ 1 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1), 
    mul_pos hx hy, sq_nonneg (x * y - 1), 
    sq_nonneg (x + y - 2), 
    mul_pos hx hy]