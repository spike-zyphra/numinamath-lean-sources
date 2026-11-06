import Mathlib

theorem inequalities_213964 (x y z : ℝ) (h : x + y + z ≥ x * y * z) :
    x^2 + y^2 + z^2 ≥ x * y * z := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          sq_nonneg (x * y * z - 1), sq_nonneg (x * y * z + 3), sq_nonneg (x + y + z - (x * y * z)), sq_nonneg (x + y + z)]