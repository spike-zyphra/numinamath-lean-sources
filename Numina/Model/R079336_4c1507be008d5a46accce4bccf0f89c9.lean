import Mathlib

theorem inequalities_599911 (α β γ : ℝ) (h₀ : β * γ ≠ 0) (h₁ : (1 - γ^2) / (β * γ) ≥ 0) :
    10 * (α^2 + β^2 + γ^2 - β * γ^3) ≥ 2 * α * β + 5 * α * γ := by

  have h2 : β * γ > 0 ∨ β * γ < 0 := by 
    by_contra h
    push_neg at h
    have h3 : β * γ = 0 := by linarith
    contradiction

  rcases h2 with h2 | h2
  · -- Case 1: β * γ > 0
    have h3 : 1 - γ^2 ≥ 0 := by
      apply div_nonneg_iff.mp at h₁
      cases h₁ with
      | inl h₁l =>
        nlinarith
      | inr h₁r =>
        nlinarith

    nlinarith [sq_nonneg (α - (β + 5 * γ) / 20), sq_nonneg (β - γ), sq_nonneg (γ^2 - 1), sq_nonneg (β * γ), sq_nonneg (α - β), sq_nonneg (α - γ)]
  · -- Case 2: β * γ < 0
    have h3 : 1 - γ^2 ≤ 0 := by 
      apply div_nonneg_iff.mp at h₁
      cases h₁ with
      | inl h₁l =>
        nlinarith
      | inr h₁r =>
        nlinarith

    nlinarith [sq_nonneg (α - (β + 5 * γ) / 20), sq_nonneg (β - γ), sq_nonneg (γ^2 - 1), sq_nonneg (β * γ), sq_nonneg (α - β), sq_nonneg (α - γ)]