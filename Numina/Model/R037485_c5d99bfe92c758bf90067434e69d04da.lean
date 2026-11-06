import Mathlib

theorem inequalities_598808 (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 2) :
    x + y + z ≤ x * y * z + 2 := by 
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x + y + z - 2), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          h, mul_self_nonneg (x - y), mul_self_nonneg (y - z), mul_self_nonneg (z - x)]