import Mathlib

theorem inequalities_123591 (x y z : ℝ) (h : x^2 + y^2 + z^2 - 2 * x * y * z = 1) :
    (1 + x) * (1 + y) * (1 + z) ≤ 4 + 4 * x * y * z := by
  nlinarith [sq_nonneg (x + y + z - 1), sq_nonneg (x + y + z + 1), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x + y + z - 2), sq_nonneg (x + y + z - 4*x*y*z), 
          sq_nonneg (x + y + z), sq_nonneg (x + y + z - 4)]