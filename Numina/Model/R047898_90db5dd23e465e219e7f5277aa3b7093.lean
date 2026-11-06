import Mathlib

theorem inequalities_601459 (x y z : ℝ) (h : x * y * z = 1) :
    x ^ 2 + y ^ 2 + z ^ 2 + 3 ≥ 2 * (x * y + y * z + z * x) := by 
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x + y + z - x * y - y * z - z * x),
          sq_nonneg (x * y + y * z + z * x - 1), sq_nonneg (x + y + z - 3),
          sq_nonneg (x * y * z - 1), mul_self_nonneg (x * y - 1), mul_self_nonneg (y * z - 1), mul_self_nonneg (z * x - 1)]