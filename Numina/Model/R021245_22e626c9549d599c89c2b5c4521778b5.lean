import Mathlib

theorem inequalities_135888
    (a b c : ℝ)
    (h₀ : 0 < a)
    (h₁ : 0 < b)
    (h₂ : 0 < c)
    (h₃ : a * b * c = 1) :
    (a + b) * (b + c) * (c + a) ≥ 4 * (a + b + c - 1) := by
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          sq_nonneg (a * b * c - 1),
          mul_pos h₀ h₁, mul_pos h₁ h₂, mul_pos h₂ h₀, h₃]