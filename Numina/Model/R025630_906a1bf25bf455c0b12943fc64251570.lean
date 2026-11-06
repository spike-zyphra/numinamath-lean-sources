import Mathlib

open Real

theorem inequalities_187795 (α β γ : ℝ) (h₀ : α ∈ Set.Ioo 0 (π / 2)) (h₁ : β ∈ Set.Ioo 0 (π / 2))
    (h₂ : γ ∈ Set.Ioo 0 (π / 2)) (h₃ : sin α ^ 2 + sin β ^ 2 + sin γ ^ 2 = 1) :
    1 ≤ sin α ^ 3 / sin β + sin β ^ 3 / sin γ + sin γ ^ 3 / sin α := by
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  rcases h₂ with ⟨h₂₁, h₂₂⟩
  have h4 : sin α > 0 := by 
    apply sin_pos_of_pos_of_lt_pi
    linarith [h₀₁, h₀₂, Real.pi_pos]
    linarith [h₀₁, h₀₂, Real.pi_pos]
  have h5 : sin β > 0 := by 
    apply sin_pos_of_pos_of_lt_pi
    linarith [h₁₁, h₁₂, Real.pi_pos]
    linarith [h₁₁, h₁₂, Real.pi_pos]
  have h6 : sin γ > 0 := by 
    apply sin_pos_of_pos_of_lt_pi
    linarith [h₂₁, h₂₂, Real.pi_pos]
    linarith [h₂₁, h₂₂, Real.pi_pos]
  have h8 : sin α ^ 3 / sin β + sin β ^ 3 / sin γ + sin γ ^ 3 / sin α - 1 ≥ 0 := by 
    have h9 : 0 < sin α * sin β * sin γ := by
      positivity
    have h10 : sin α ^ 3 / sin β + sin β ^ 3 / sin γ + sin γ ^ 3 / sin α - 1 = 
      ( sin α ^ 4 * sin γ + sin β ^ 4 * sin α + sin γ ^ 4 * sin β - sin α * sin β * sin γ ) / ( sin α * sin β * sin γ ) := by
      field_simp
      ring
    rw [h10] at *
    apply div_nonneg
    nlinarith [ sq_nonneg ( sin α ^ 2 - sin β ^ 2 ), sq_nonneg ( sin β ^ 2 - sin γ ^ 2 ), sq_nonneg ( sin γ ^ 2 - sin α ^ 2 ), sq_nonneg ( sin α - sin β ), sq_nonneg ( sin β - sin γ ), sq_nonneg ( sin γ - sin α ), 
      mul_pos h4 h5, mul_pos h5 h6, mul_pos h4 h6, 
      sq_nonneg ( sin α * ( sin α - sin β ) ), sq_nonneg ( sin β * ( sin β - sin γ ) ), sq_nonneg ( sin γ * ( sin γ - sin α ) ) 
    ]
    positivity
  linarith