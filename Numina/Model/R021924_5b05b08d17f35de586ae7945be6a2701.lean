import Mathlib

theorem inequalities_320928 (α β γ : ℝ) (h₀ : β * γ ≠ 0) (h₁ : (1 - γ^2) / (β * γ) ≥ 0) :
    10 * (α^2 + β^2 + γ^2 - β * γ^3) ≥ 2 * α * β + 5 * α * γ := by
  have h2 : β * γ > 0 ∨ β * γ < 0 := by
    by_contra h
    push_neg at h
    have h3 : β * γ = 0 := by
      linarith
    contradiction

  rcases h2 with (h2 | h2)
  · -- Case where β * γ > 0
    have h3 : 1 - γ ^ 2 ≥ 0 := by
      have h4 : (1 - γ ^ 2) / (β * γ) ≥ 0 := h₁
      apply div_nonneg_iff.mp at h4
      cases h4
      · -- Case where 1 - γ ^ 2 ≥ 0 and β * γ ≥ 0
        nlinarith
      · -- Case where 1 - γ ^ 2 ≤ 0 and β * γ ≤ 0
        nlinarith
    have h4 : γ ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (α - (β + 5 * γ) / 10), sq_nonneg (β - γ), sq_nonneg (β + γ), sq_nonneg (γ^2 - 1/2), sq_nonneg (β - 1), sq_nonneg (γ - 1), sq_nonneg (γ + 1), sq_nonneg (β * γ), sq_nonneg (α - β), sq_nonneg (α - γ)]
  · -- Case where β * γ < 0
    have h3 : 1 - γ ^ 2 ≤ 0 := by
      have h4 : (1 - γ ^ 2) / (β * γ) ≥ 0 := h₁
      apply div_nonneg_iff.mp at h4
      cases h4
      · -- Case where 1 - γ ^ 2 ≥ 0 and β * γ ≥ 0
        nlinarith
      · -- Case where 1 - γ ^ 2 ≤ 0 and β * γ ≤ 0
        nlinarith
    have h4 : γ ^ 2 ≥ 1 := by nlinarith
    nlinarith [sq_nonneg (α - (β + 5 * γ) / 10), sq_nonneg (β + γ), sq_nonneg (γ^2 - 1), sq_nonneg (β - γ), sq_nonneg (α - γ), sq_nonneg (α - β), sq_nonneg (γ - 1), sq_nonneg (γ + 1), sq_nonneg (β * γ), sq_nonneg (β - γ * 1), sq_nonneg (γ^2 - 1), sq_nonneg (β + γ), sq_nonneg (β + γ * 1)]