import Mathlib

open Real Set
open scoped Real

theorem inequalities_43287 (α β γ : ℝ)
  (h₀ : α ∈ Icc 0 (π/2)) (h₁ : β ∈ Icc 0 (π/2)) (h₂ : γ ∈ Icc 0 (π/2))
  (h₃ : sin α + sin β + sin γ = 1) (h₄ : sin α * cos (2*α) + sin β * cos (2*β) + sin γ * cos (2*γ) = -1) :
  sin α^2 + sin β^2 + sin γ^2 = 1 := by 
  rcases h₀ with ⟨ha1, ha2⟩
  rcases h₁ with ⟨hb1, hb2⟩
  rcases h₂ with ⟨hc1, hc2⟩
  have h5 : sin α ≥ 0 := by 
    apply sin_nonneg_of_nonneg_of_le_pi 
    all_goals 
      linarith [Real.pi_pos]
  have h6 : sin β ≥ 0 := by 
    apply sin_nonneg_of_nonneg_of_le_pi 
    all_goals 
      linarith [Real.pi_pos]
  have h7 : sin γ ≥ 0 := by 
    apply sin_nonneg_of_nonneg_of_le_pi 
    all_goals 
      linarith [Real.pi_pos]
  have h8 : cos α ≥ 0 := by 
    apply cos_nonneg_of_neg_pi_div_two_le_of_le 
    all_goals 
      linarith [Real.pi_pos]
  have h9 : cos β ≥ 0 := by 
    apply cos_nonneg_of_neg_pi_div_two_le_of_le 
    all_goals 
      linarith [Real.pi_pos]
  have h10 : cos γ ≥ 0 := by 
    apply cos_nonneg_of_neg_pi_div_two_le_of_le 
    all_goals 
      linarith [Real.pi_pos]
  have h11 : sin α ^ 2 + sin β ^ 2 + sin γ ^ 2 = 1 := by 
    have eq1 : sin α * (cos (2 * α) ) + sin β * (cos (2 * β) ) + sin γ * (cos (2 * γ) ) = -1 := by
      linarith [h₄]
    have cos2α : cos (2 * α) = 1 - 2 * sin α ^ 2 := by 
      rw [cos_two_mul, sin_sq]
      <;> ring
    have cos2β : cos (2 * β) = 1 - 2 * sin β ^ 2 := by 
      rw [cos_two_mul, sin_sq]
      <;> ring
    have cos2γ : cos (2 * γ) = 1 - 2 * sin γ ^ 2 := by 
      rw [cos_two_mul, sin_sq]
      <;> ring
    rw [cos2α, cos2β, cos2γ] at eq1
    nlinarith [sq_nonneg (sin α - 1), sq_nonneg (sin β - 1), sq_nonneg (sin γ - 1)]
  linarith [h11]