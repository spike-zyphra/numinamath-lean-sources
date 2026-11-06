import Mathlib

theorem algebra_4500 :
    ¬∃ x y : ℝ, (2 * x ^ 2 - 1) * (2 * y ^ 2 - 1) = 7 * x * y / 2 ∧ x ^ 2 + y ^ 2 + x * y - 7 * x - 6 * y + 14 = 0 := by
  rintro ⟨x, y, h1, h2⟩
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 3), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (x - 4), sq_nonneg (y - 4), mul_self_nonneg (x - 2), mul_self_nonneg (y - 2), mul_self_nonneg (x + y - 4), mul_self_nonneg (x * y), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x * y), sq_nonneg (x - y)]