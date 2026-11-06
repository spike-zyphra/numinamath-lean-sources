import Mathlib

theorem algebra_25325 {x y z : ℝ} (h : x + y + z = x * y * z) :
    x * (1 - y^2) * (1 - z^2) + y * (1 - z^2) * (1 - x^2) +
    z * (1 - x^2) * (1 - y^2) = 4 * x * y * z := by 
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), sq_nonneg (x + y + z - x * y * z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x * (y - z)), sq_nonneg (y * (z - x)), sq_nonneg (z * (x - y)), sq_nonneg (x * y * z), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]