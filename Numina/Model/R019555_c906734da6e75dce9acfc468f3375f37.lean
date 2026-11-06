import Mathlib

theorem algebra_117905 {a b c : ℝ} (h₀ : a^2 + b^2 + c^2 = 14) (h₁ : 2*a + 4*b + 6*c = 28) :
    a = 1 ∧ b = 2 ∧ c = 3 := by
  have h2 : (a - 1) ^ 2 + (b - 2) ^ 2 + (c - 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (c - 3)]
  have ha1 : a - 1 = 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (c - 3), h2]
  have hb2 : b - 2 = 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (c - 3), h2]
  have hc3 : c - 3 = 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (c - 3), h2]
  constructor
  · -- Prove a = 1
    linarith
  constructor
  · -- Prove b = 2
    linarith
  · -- Prove c = 3
    linarith