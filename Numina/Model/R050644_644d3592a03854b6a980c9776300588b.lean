import Mathlib

theorem algebra_600582 (a b c : ℝ) (h₀ : a ≤ b ∧ b ≤ c) (h₁ : a + b + c = 6) (h₂ : a * b + b * c + c * a = 9) :
    0 ≤ a ∧ a ≤ 1 ∧ 1 ≤ b ∧ b ≤ 3 ∧ 3 ≤ c ∧ c ≤ 4 := by
  constructor
  · -- Case 0 ≤ a
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  constructor
  · -- Case a ≤ 1
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  constructor
  · -- Case 1 ≤ b
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  constructor
  · -- Case b ≤ 3
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  constructor
  · -- Case 3 ≤ c
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  · -- Case c ≤ 4
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]