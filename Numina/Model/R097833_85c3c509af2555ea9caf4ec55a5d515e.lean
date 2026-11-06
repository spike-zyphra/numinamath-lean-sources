import Mathlib

theorem algebra_8927 (a b : ℝ) (h₀ : a + 2 * b + a + 3 * b + a + 4 * b = 0)
    (h₁ : 3 * a + a * b + 4 * b + 3 * b = 0) (h₂ : 5 * a + 8 * b + 6 * b + b * b = 0)
    (h₃ : 0 < b) :
    a + b = 9 := by
  nlinarith [sq_nonneg (a + 3), sq_nonneg (b - 1), sq_nonneg (a + 3 * b), sq_nonneg (b), sq_nonneg (a + 3), sq_nonneg (b * 2), sq_nonneg (a * 2), sq_nonneg ((b - 3) * 2), sq_nonneg ((b - 3) * 2), sq_nonneg (a - 6), sq_nonneg (b - 3), sq_nonneg (a - 6), sq_nonneg (a + 3), sq_nonneg (b - 3)]