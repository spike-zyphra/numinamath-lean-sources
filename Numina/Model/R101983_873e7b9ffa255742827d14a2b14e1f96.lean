import Mathlib

theorem algebra_10531 {x y : ℝ} (h₁ : (x - 1)^3 + 1997 * (x - 1) = -1) (h₂ : (y - 1)^3 + 1997 * (y - 1) = 1) : x + y = 2 := by
  nlinarith [sq_nonneg ((x - 1) + (y - 1)), sq_nonneg ((x - 1) - (y - 1)), sq_nonneg ((x - 1) - 0), sq_nonneg ((y - 1) - 0), sq_nonneg ((x - 1) - (y - 1)), sq_nonneg ((x - 1) + (y - 1)), sq_nonneg (x - 1 + (y - 1)), sq_nonneg (x - 1 - (y - 1)), sq_nonneg ((x - 1) * (y - 1)), sq_nonneg ((x - 1) - (y - 1)), sq_nonneg ((x - 1) + (y - 1)), sq_nonneg ((x - 1) * (y - 1))]