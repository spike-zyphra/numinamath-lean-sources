import Mathlib.Tactic

theorem inequalities_150250
    (a b c d : ℝ)
    (h₀ : 0 < a)
    (h₁ : 0 < b)
    (h₂ : 0 < c)
    (h₃ : 0 < d) :
    ¬(a + b < c + d ∧ (a + b) * (c + d) < a * b + c * d ∧ (a + b) * c * d < a * b * (c + d)) := by
  intro ⟨h₁₂, h₂₃, h₃₁⟩
  nlinarith [mul_pos h₁ h₂, mul_pos h₃ h₀, h₁₂, h₂₃, h₃₁, mul_self_nonneg (a - c),
    mul_self_nonneg (b - d), sq_nonneg (a - d), sq_nonneg (b - c)]