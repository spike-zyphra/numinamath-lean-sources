import Mathlib

theorem algebra_157122 (a b : ℝ) :
    ∃ x, (a ^ 2 - b ^ 2) * x ^ 2 + 2 * (a ^ 3 - b ^ 3) * x +
      (a ^ 4 - b ^ 4) = 0 := by
  use (-a - b)
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a + b), sq_nonneg (a - b),
    sq_nonneg (a ^ 2 + a * b + b ^ 2), sq_nonneg (a * b), sq_nonneg (a ^ 2 - b ^ 2),
    sq_nonneg (a ^ 2 + b ^ 2), sq_nonneg (a ^ 4 - b ^ 4)
  ]