import Mathlib

theorem algebra_228646 {a1 a2 b1 b2 : ℝ}
    (h₀ : a1^2 + b1^2 = 1) (h₁ : a2^2 + b2^2 = 1) (h₂ : a1 * a2 + b1 * b2 = 0) :
    a1^2 + a2^2 = 1 ∧ b1^2 + b2^2 = 1 ∧ a1 * b1 + a2 * b2 = 0 := by
  constructor
  · -- Prove that $a_1^2 + a_2^2 = 1$
    nlinarith [sq_nonneg (a1 - a2), sq_nonneg (b1 - b2), sq_nonneg (a1 + a2), sq_nonneg (b1 + b2), h₀, h₁, h₂]
  constructor
  · -- Prove that $b_1^2 + b_2^2 = 1$
    nlinarith [sq_nonneg (a1 - a2), sq_nonneg (b1 - b2), sq_nonneg (a1 + a2), sq_nonneg (b1 + b2), h₀, h₁, h₂]
  · -- Prove that $a_1 * b_1 + a2 * b2 = 0$
    nlinarith [sq_nonneg (a1 - b2), sq_nonneg (a2 - b1), sq_nonneg (a1 + b2), sq_nonneg (a2 + b1), h₀, h₁, h₂]