import Mathlib

theorem inequalities_276944 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x ^ 5 + y ^ 5 ≥ x ^ 4 * y + x * y ^ 4 := by
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y), sq_nonneg (x + y), 
          sq_nonneg (x * y), sq_nonneg (x ^ 2 + y ^ 2), 
          sq_nonneg (x * (x - y)), sq_nonneg (y * (x - y)), 
          mul_pos hx hy
         ]