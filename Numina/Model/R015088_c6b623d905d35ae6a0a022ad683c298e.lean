import Mathlib


theorem algebra_223972 (x y z : ℝ)
    (h₀ : x + 3 * y + 6 * z = 1)
    (h₁ : x * y + 2 * x * z + 6 * y * z = -8)
    (h₂ : x * y * z = 2) :
    x + y + z ≥ -8 / 3 := by
  nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 2 / 3), sq_nonneg (z + 1 / 3), sq_nonneg (y - z), sq_nonneg (y + 2 / 3), sq_nonneg (z + 1 / 3), sq_nonneg (y + 2), sq_nonneg (z + 2 / 3), sq_nonneg (x + 3 * y + 6 * z - 1), sq_nonneg (x * y + 2 * x * z + 6 * y * z + 8), sq_nonneg (x * y * z - 2)]