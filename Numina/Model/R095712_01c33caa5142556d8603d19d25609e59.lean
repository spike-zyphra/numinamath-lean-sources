import Mathlib

theorem algebra_315872 (x y a : ℝ) (h₀ : x + y = a + 1) (h₁ : x * y = a ^ 2 - 7 * a + 16) :
    x ^ 2 + y ^ 2 ≤ 32 := by
  have h2 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
    nlinarith
  rw [h2]
  rw [h₀, h₁]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - (a + 1)), sq_nonneg (a - 3), sq_nonneg (a - 7), sq_nonneg (a - 8), sq_nonneg (x - 4), sq_nonneg (y - 4), sq_nonneg (x - y)]