import Mathlib

theorem algebra_603182
(a b c : ℝ)
(h₀ : a ≤ b ∧ b ≤ c)
(h₁ : a + b + c = 6)
(h₂ : a * b + b * c + c * a = 9) :
0 ≤ a ∧ a ≤ 1 ∧ 1 ≤ b ∧ b ≤ 3 ∧ 3 ≤ c ∧ c ≤ 4 := by
  have h3 : a ≤ b := h₀.1
  have h4 : b ≤ c := h₀.2
  constructor
  · -- Proof that 0 ≤ a
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - 0)]
  constructor
  · -- Proof that a ≤ 1
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 3), sq_nonneg (b - 3), sq_nonneg (c - 4)]
  constructor
  · -- Proof that 1 ≤ b
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 3), sq_nonneg (b - 3), sq_nonneg (c - 4)]
  constructor
  · -- Proof that b ≤ 3
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 3), sq_nonneg (b - 3), sq_nonneg (c - 4)]
  constructor
  · -- Proof that 3 ≤ c
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 3), sq_nonneg (b - 3), sq_nonneg (c - 4)]
  · -- Proof that c ≤ 4
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 3), sq_nonneg (b - 3), sq_nonneg (c - 4)]