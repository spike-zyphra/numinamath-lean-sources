import Mathlib

theorem inequalities_600831
    (a b c : ℝ)
    (h₀ : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c)
    (h₁ : a + b + c = 1) :
    a * b + b * c + c * a - 3 * a * b * c ≤ 1 / 4 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2), mul_nonneg h₀.1 h₀.2.1, mul_nonneg h₀.2.1 h₀.2.2, mul_nonneg h₀.1 h₀.2.2]