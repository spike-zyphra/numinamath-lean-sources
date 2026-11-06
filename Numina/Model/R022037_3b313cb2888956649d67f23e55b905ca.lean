import Mathlib

theorem algebra_219678 :
    ∃ a b c : ℝ, (a * (-1) ^ 2 + b * (-1) + c = 0) ∧
      (∀ x : ℝ, x ≤ a * x ^ 2 + b * x + c ∧ a * x ^ 2 + b * x + c ≤ (1 + x ^ 2) / 2) := by

  use 1 / 4, 1 / 2, 1 / 4
  constructor
  · norm_num
  · intro x
    constructor
    · -- Show that x ≤ (1/4)x^2 + (1/2)x + (1/4)
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x * (x - 1))]
    · -- Show that (1/4)x^2 + (1/2)x + (1/4) ≤ (1 + x^2) / 2
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x * (x - 1))]