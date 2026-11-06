import Mathlib

theorem algebra_171629 {a b c d : ℝ}
    (h₀ : a + b + c + d = 3)
    (h₁ : a^2 + b^2 + c^2 + d^2 = 3)
    (h₂ : a * b * c + b * c * d + c * d * a + d * a * b = 1) :
    a * (1 - a)^3 = b * (1 - b)^3 ∧ b * (1 - b)^3 = c * (1 - c)^3 ∧ c * (1 - c)^3 = d * (1 - d)^3 := by
  constructor
  · -- prove a * (1 - a)^3 = b * (1 - b)^3
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - c - d), sq_nonneg (a + b + c + d - 3), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), sq_nonneg (d - 1)]
  constructor
  · -- prove b * (1 - b)^3 = c * (1 - c)^3
    nlinarith [sq_nonneg (b - c), sq_nonneg (a + b - c - d), sq_nonneg (a + b + c + d - 3), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), sq_nonneg (d - 1)]
  · -- prove c * (1 - c)^3 = d * (1 - d)^3
    nlinarith [sq_nonneg (c - d), sq_nonneg (a + b - c - d), sq_nonneg (a + b + c + d - 3), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), sq_nonneg (d - 1)]