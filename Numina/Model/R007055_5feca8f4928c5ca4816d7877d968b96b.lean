import Mathlib.Tactic

theorem inequalities_150250
    (a b c d : ℝ)
    (h₀ : 0 < a)
    (h₁ : 0 < b)
    (h₂ : 0 < c)
    (h₃ : 0 < d) :
    ¬(a + b < c + d ∧ (a + b) * (c + d) < a * b + c * d ∧ (a + b) * c * d < a * b * (c + d)) := by
  -- Assume that all three inequalities hold
  intro h
  rcases h with ⟨h1, h2, h3⟩
  -- We need to derive a contradiction
  nlinarith [sq_nonneg (a - b), sq_nonneg (c - d), mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₀ h₃, mul_pos h₁ h₂, mul_pos h₁ h₃, mul_pos h₂ h₃]