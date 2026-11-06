import Mathlib

theorem algebra_234981 (x y z : ℝ) (h₀ : 4 * x ^ 2 - 2 * x - 30 * y * z = 25 * y ^ 2 + 5 * y + 12 * x * z)
    (h₁ : 25 * y ^ 2 + 5 * y + 12 * x * z = 9 * z ^ 2 - 3 * z - 20 * x * y) :
    (2 * x + 5 * y) + (3 * z + 5 * y) + (3 * z - 2 * x) ≤ 2 := by
  nlinarith [sq_nonneg (x - 2 * y - z), sq_nonneg (x - (5 * y / 2) - z / 2), sq_nonneg (x - 2 + y), sq_nonneg (y + 1 / 5 - z / 5), sq_nonneg (2 * y - x + z), sq_nonneg (x - z - 2 * y), sq_nonneg (5 * y + 3 * z - 1)]