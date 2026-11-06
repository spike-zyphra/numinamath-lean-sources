import Mathlib

theorem inequalities_173273
    (a b c : ℝ)
    (h₀ : 0 ≤ a)
    (h₁ : 0 ≤ b)
    (h₂ : 0 ≤ c) :
    (a + b) * (a + c) * (b + c) ≥ 8 * a * b * c := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a), 
          mul_nonneg h₀ h₁, mul_nonneg h₁ h₂, mul_nonneg h₀ h₂]