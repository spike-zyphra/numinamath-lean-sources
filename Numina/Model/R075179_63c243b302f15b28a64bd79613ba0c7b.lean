import Mathlib

theorem algebra_108420 (a : ℝ) (h : ∃ x₁ x₂, x₁^2 + (a^2 - 1)*x₁ + a - 2 = 0 ∧ x₂^2 + (a^2 - 1)*x₂ + a - 2 = 0 ∧ x₁ > 1 ∧ x₂ < 1) :
    a ∈ Set.Ioo (-2) 1 := by 
  rcases h with ⟨x₁, x₂, h₁, h₂, hx₁, hx₂⟩
  have h4 : a^2 + a - 2 < 0 := by
    nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂ - (a^2 - 1)), sq_nonneg (x₁ - 1), sq_nonneg (x₂ - 1)]
  have h5 : a > -2 := by
    nlinarith 
  have h6 : a < 1 := by
    nlinarith 
  exact ⟨h5, h6⟩