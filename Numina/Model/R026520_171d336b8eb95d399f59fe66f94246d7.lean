import Mathlib

theorem algebra_132051 {x y : ℝ} (h1 : x^3 + x^2 + x * y + x + y + 2 = 0) (h2 : y^3 - y^2 + 3 * y - x = 0) :
    x - y = -1 := by
  have h3 : y = x + 1 := by
    nlinarith [sq_nonneg (x - y + 1), sq_nonneg (y + 1), sq_nonneg (y - 1), sq_nonneg (x + 1), sq_nonneg (x + 1 - y), sq_nonneg ((x * y)), sq_nonneg ((x * (y - x - 1)))]
  linarith