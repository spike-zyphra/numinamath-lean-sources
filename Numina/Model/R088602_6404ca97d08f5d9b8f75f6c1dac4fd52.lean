import Mathlib

open Real

theorem inequalities_5716 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x ^ 2 + 4) * (y ^ 2 + 4) ≥ 2 * x * (y ^ 2 + 4) + 2 * y * (x ^ 2 + 4) := by 
  nlinarith [sq_nonneg (x * y - 2 * x - 2 * y + 4), 
          sq_nonneg (x - y), 
          sq_nonneg (x * y - 2), 
          sq_nonneg (x * y - 2 * x), 
          sq_nonneg (x * y - 2 * y), 
          mul_pos hx hy, 
          sq_nonneg (x * y), 
          sq_nonneg (x - 1), 
          sq_nonneg (y - 1)]