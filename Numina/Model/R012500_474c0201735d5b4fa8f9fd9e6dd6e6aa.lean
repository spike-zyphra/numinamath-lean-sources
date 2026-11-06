import Mathlib

open Real Set
open scoped Real

theorem inequalities_103601 (α β γ : ℝ) (h₀ : α ∈ Ioo 0 π)
  (h₁ : β ∈ Ioo 0 π) (h₂ : γ ∈ Ioo 0 π) (h₃ : α + β + γ = π)
  (t : ℝ) :
  cos α + t * (cos β + cos γ) ≤ 1 + t ^ 2 / 2 := by 
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  rcases h₂ with ⟨h₂₁, h₂₂⟩
  have h₄ : γ = π - α - β := by
    linarith [h₃]
  -- Calculate cos γ in terms of α and β.
  have h₅ : cos γ = -cos (α + β) := by 
    rw [h₄]
    have h6 : cos (π - α - β) = -cos (α + β) := by
      have h7 : π - α - β = π - (α + β) := by ring
      rw [h7]
      rw [cos_pi_sub]
    linarith [h6]
  -- Expand cos(α + β) using angle addition.
  have h₇ : cos (α + β) = cos α * cos β - sin α * sin β := by
    rw [cos_add]
  -- Therefore, we can write cos γ as.
  have h₈ : cos γ = - (cos α * cos β - sin α * sin β ) := by 
    rw [h₅, h₇]
  -- Express `cos β + cos γ ` as an algebraic function of angles.
  have h₉ : cos β + cos γ = cos β * (1 - cos α ) + sin α * sin β := by 
    rw [h₈]
    ring
  -- Show that (cos β + cos γ ) ^ 2 ≤ 2 * (1 - cos α ) to ensure discriminant is non-positive.
  have hΔ : (cos β + cos γ ) ^ 2 ≤ 2 * (1 - cos α ) := by
    rw [h₉]
    have h10 : cos α ^ 2 + sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
    have h11 : cos β ^ 2 + sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β
    have h12 : sin α > 0 := by 
      apply Real.sin_pos_of_pos_of_lt_pi
      linarith
      linarith
    have h13 : sin β > 0 := by 
      apply Real.sin_pos_of_pos_of_lt_pi
      linarith
      linarith
    nlinarith [sq_nonneg (cos β - cos α ), sq_nonneg (sin α - sin β ), sq_nonneg (cos β * sin α - sin β * (1 - cos α ) ), sq_nonneg (sin α * cos β - sin β * (1 - cos α ) ), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_sq_add_cos_sq (α + β), Real.sin_sq_add_cos_sq γ, Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, mul_pos h12 h13 ]
  -- Now using the facts above, nlinarith can solve for the original inequality.
  have h14 : cos α + t * (cos β + cos γ ) ≤ 1 + t ^ 2 / 2 := by
    nlinarith [ sq_nonneg (t - (cos β + cos γ ) ), sq_nonneg (t + (cos β + cos γ ) ), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_sq_add_cos_sq γ, Real.sin_sq_add_cos_sq (α + β), Real.sin_pos_of_pos_of_lt_pi h₀₁ h₀₂, Real.sin_pos_of_pos_of_lt_pi h₁₁ h₁₂, hΔ ]
  exact h14