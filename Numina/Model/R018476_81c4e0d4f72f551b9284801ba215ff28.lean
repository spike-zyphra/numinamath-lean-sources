import Mathlib

theorem inequalities_75634 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    4 * x ^ 4 + 4 * y ^ 3 + 5 * x ^ 2 + y + 1 ≥ 12 * x * y := by
  nlinarith [sq_nonneg (x ^ 2 - y), sq_nonneg (x - 1), sq_nonneg (y - 1), 
          sq_nonneg (2 * x ^ 2 - 3 * y), sq_nonneg (x ^ 2 - 1), sq_nonneg (y - x), 
          sq_nonneg (y + x), sq_nonneg (2 * x - 1), sq_nonneg (2 * y - 1), 
          sq_nonneg (x ^ 2 - y), 
          mul_pos hx hy, 
          sq_nonneg (4 * x ^ 2 - 3 * y), sq_nonneg (y - 1), 
          sq_nonneg (x - y), sq_nonneg (x - 1/2), sq_nonneg (y - 1/2), 
          mul_pos hx (show 0 < x ^ 2 by nlinarith), 
          mul_pos hx (show 0 < y ^ 2 by nlinarith)]