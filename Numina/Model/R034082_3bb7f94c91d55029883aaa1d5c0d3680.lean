import Mathlib

theorem inequalities_212972 (x y z : ℝ) :
    x^4 + y^4 + z^2 + 1 ≥ 2 * x * (x * y^2 - x + z + 1) := by 
  nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x - z), sq_nonneg (x - 1)]