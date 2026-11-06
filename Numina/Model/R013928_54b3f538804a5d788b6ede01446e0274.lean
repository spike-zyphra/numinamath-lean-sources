import Mathlib

theorem algebra_289747 (a b c d : ℝ) (h₀ : a + b + c + d = 3) (h₁ : a^2 + 2 * b^2 + 3 * c^2 + 6 * d^2 = 5) :
    1 ≤ a ∧ a ≤ 2 := by

  have h2 : b + c + d = 3 - a := by
    linarith

  have h3 : 2 * b^2 + 3 * c^2 + 6 * d^2 = 5 - a^2 := by 
    nlinarith

  have h8 : (a - 1) * (a - 2) ≤ 0 := by
    nlinarith [sq_nonneg (b - 3 * d), sq_nonneg (c - 2 * d), sq_nonneg (b - 3 * d), sq_nonneg (c - 2 * d), sq_nonneg (a - 1), sq_nonneg (a - 2),
              sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
              sq_nonneg (2 * b - 3 * c), sq_nonneg (b - 3 * d), sq_nonneg (c - 2 * d)]

  constructor
  · -- Prove 1 ≤ a
    nlinarith [h8]

  · -- Prove a ≤ 2
    nlinarith [h8]