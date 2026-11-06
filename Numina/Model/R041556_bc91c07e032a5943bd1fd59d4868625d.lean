import Mathlib

theorem inequalities_281083 (a b c d : ℝ) (h₀ : a + b + c + d = 6) (h₁ : a^2 + b^2 + c^2 + d^2 = 12) :
    36 ≤ 4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) ∧
    4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) ≤ 48 := by
  constructor
  · -- Prove the left part: 36 ≤ 4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4)
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), sq_nonneg (d - 1),
      sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2), sq_nonneg (d - 2),
      h₀, h₁]
  · -- Prove the right part: 4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) ≤ 48
    nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2), sq_nonneg (d - 2),
      sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d),
      h₀, h₁]