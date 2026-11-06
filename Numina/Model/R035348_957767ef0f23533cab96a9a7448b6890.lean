import Mathlib

theorem inequalities_78574 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x^3 + y^4 ≤ x^2 + y^3) : x^3 + y^3 ≤ 2 := by 
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), 
    sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), 
    sq_nonneg (x - y), mul_pos hx hy, 
    sq_nonneg (x^2 - y^2), sq_nonneg (x - 1), sq_nonneg (y - 1)
  ]