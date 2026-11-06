import Mathlib

theorem algebra_214633 {x y : ℝ} (hx : x^3 - 6 * x^2 + 15 * x = 12) (hy : y^3 - 6 * y^2 + 15 * y = 16) : x + y = 4 := by
  have h1 : x^3 - 6 * x^2 + 15 * x + y^3 - 6 * y^2 + 15 * y = 28 := by
    linarith
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 4), sq_nonneg (x - 1), sq_nonneg (y - 3), sq_nonneg (x - 2), sq_nonneg (y - 2)]