import Mathlib

theorem inequalities_599371 (x y z : ℝ) (h : x^2 + y^2 + z^2 = 9) :
    2 * (x + y + z) - x * y * z ≤ 10 := by
  nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z + 1),
    sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (z - 2),
    sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    sq_nonneg (x + y + z - 3), sq_nonneg (x + y + z + 3)]