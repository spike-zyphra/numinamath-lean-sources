import Mathlib

theorem inequalities_44741 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x ^ 2 + y ^ 3 ≥ x ^ 3 + y ^ 4) : x ^ 3 + y ^ 3 ≤ 2 := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), 
          sq_nonneg (x - y), sq_nonneg (x * y - 1), 
          mul_pos hx hy, mul_self_nonneg (x * y - 1), 
          mul_self_nonneg (x - y), 
          mul_self_nonneg (x^2 - 1), mul_self_nonneg (y^2 - 1)]