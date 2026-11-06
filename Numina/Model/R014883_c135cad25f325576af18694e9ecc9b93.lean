import Mathlib

open Real Set
open scoped Real

theorem inequalities_323882 (α β γ : ℝ) (h₀ : α ∈ Ioo 0 (π / 2)) (h₁ : β ∈ Ioo 0 (π / 2))
    (h₂ : γ ∈ Ioo 0 (π / 2)) (h₃ : sin α ^ 2 + sin β ^ 2 + sin γ ^ 2 = 1) :
    1 ≤ sin α ^ 3 / sin β + sin β ^ 3 / sin γ + sin γ ^ 3 / sin α := by
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with  ⟨h₁₁, h₁₂⟩
  rcases h₂ with  ⟨h₂₁, h₂₂⟩
  have h₀₃ : 0 < sin α := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [h₀₁, h₀₂, Real.pi_pos]
  have h₁₃ : 0 < sin β := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [h₁₁, h₁₂, Real.pi_pos]
  have h₂₃ : 0 < sin γ := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [h₂₁, h₂₂, Real.pi_pos]
  have h₅ : sin α ^ 3 / sin β + sin β ^ 3 / sin γ + sin γ ^ 3 / sin α ≥ 1 := by
    have h₆ : sin α ^ 3 / sin β + sin β ^ 3 / sin γ + sin γ ^ 3 / sin α - 1 ≥ 0 := by
      have h₉ : sin α ^ 3 / sin β + sin β ^ 3 / sin γ + sin γ ^ 3 / sin α - 1 =
        (sin α ^ 4 * sin γ + sin β ^ 4 * sin α + sin γ ^ 4 * sin β - (sin α * sin β * sin γ)) / (sin α * sin β * sin γ) := by
        field_simp
        ring
      rw [h₉]
      have h₈ : sin α ^ 4 * sin γ + sin β ^ 4 * sin α + sin γ ^ 4 * sin β - (sin α * sin β * sin γ) ≥ 0 := by
        nlinarith [sq_nonneg (sin α ^ 2 - sin β ^ 2), sq_nonneg (sin β ^ 2 - sin γ ^ 2), sq_nonneg (sin γ ^ 2 - sin α ^ 2),
          sq_nonneg (sin α - sin β), sq_nonneg (sin β - sin γ), sq_nonneg (sin γ - sin α),
          sq_nonneg (sin α * (sin α - sin β)), sq_nonneg (sin α * (sin α - sin γ)), 
          sq_nonneg (sin β * (sin β - sin α)), sq_nonneg (sin β * (sin β - sin γ)), 
          sq_nonneg (sin γ * (sin γ - sin α)), sq_nonneg (sin γ * (sin γ - sin β)), 
          mul_pos h₀₃ h₁₃, mul_pos h₁₃ h₂₃, mul_pos h₀₃ h₂₃, 
          sq_nonneg (sin α * sin β - sin β * sin γ), sq_nonneg (sin β * sin γ - sin γ * sin α), sq_nonneg (sin γ * sin α - sin α * sin β),
          mul_nonneg (show 0 ≤ sin α by linarith) (show 0 ≤ sin β * sin γ by positivity)]
      have h₁₁ : (sin α ^ 4 * sin γ + sin β ^ 4 * sin α + sin γ ^ 4 * sin β - (sin α * sin β * sin γ)) / (sin α * sin β * sin γ) ≥ 0 := by
        apply div_nonneg
        · linarith [h₈]
        all_goals
        positivity
      linarith [h₁₁]
    linarith
  linarith [h₅]