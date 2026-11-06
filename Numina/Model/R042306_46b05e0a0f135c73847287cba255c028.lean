import Mathlib

theorem inequalities_65799 (x y z : ℝ) : x^2 * (3 * y^2 + 3 * z^2 - 2 * y * z) ≥ y * z * (2 * x * y + 2 * x * z - y * z) := by 
  nlinarith [sq_nonneg (x * (y - z)), sq_nonneg (y * (x - z)), sq_nonneg (x * y - x * z), sq_nonneg (y - z), sq_nonneg (x * y - z * x), sq_nonneg (y * z - x * y), sq_nonneg (y * z - x * z), sq_nonneg (x - z), sq_nonneg (y * (x - y)), sq_nonneg (z * (x - z)), sq_nonneg ((y - z) * x), sq_nonneg (y * z), sq_nonneg (x * y - x * z), sq_nonneg (x * (y - z)), sq_nonneg (x * y + x * z - y * z)]