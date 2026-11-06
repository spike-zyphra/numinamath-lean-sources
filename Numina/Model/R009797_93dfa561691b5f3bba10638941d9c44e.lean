import Mathlib

theorem algebra_140152 {x y : ℝ} (hx : x^3 - 3 * x^2 + 5 * x - 17 = 0) (hy : y^3 - 3 * y^2 + 5 * y + 11 = 0) : x + y = 2 := by
  have h1 : y = 2 - x := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - y + 2), sq_nonneg (x - 2), sq_nonneg (y), sq_nonneg (x - 2 + y), sq_nonneg (x - y + 2)]
  linarith [h1]