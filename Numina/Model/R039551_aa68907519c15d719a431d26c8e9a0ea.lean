import Mathlib

open Real Set
open scoped Real

theorem inequalities_599166 (α β γ : ℝ) (h₀ : α ∈ Ioo 0 (π / 2)) (h₁ : β ∈ Ioo 0 (π / 2))
    (h₂ : γ ∈ Ioo 0 (π / 2)) (h₃ : cos α ^ 2 + cos β ^ 2 + cos γ ^ 2 = 1) :
    1 / sin α ^ 2 + 1 / sin β ^ 2 + 1 / sin γ ^ 2 ≥ 9 / 2 := by
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  rcases h₂ with ⟨h₂₁, h₂₂⟩
  have h3 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h4 : sin β > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h5 : sin γ > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h6 : sin α ^ 2 + sin β ^ 2 + sin γ ^ 2 = 2 := by
    have h7 : sin α ^ 2 = 1 - cos α ^ 2 := by
      rw [←Real.sin_sq_add_cos_sq α]
      linarith
    have h8 : sin β ^ 2 = 1 - cos β ^ 2 := by
      rw [←Real.sin_sq_add_cos_sq β]
      linarith
    have h9 : sin γ ^ 2 = 1 - cos γ ^ 2 := by
      rw [←Real.sin_sq_add_cos_sq γ]
      linarith
    linarith [h₃, h7, h8, h9]
  have h9 : 0 < sin α ^ 2 := by
    nlinarith [h3, Real.sin_sq_add_cos_sq α]
  have h10 : 0 < sin β ^ 2 := by
    nlinarith [h4, Real.sin_sq_add_cos_sq β]
  have h11 : 0 < sin γ ^ 2 := by
    nlinarith [h5, Real.sin_sq_add_cos_sq γ]
  have h7 : 1 / sin α ^ 2 + 1 / sin β ^ 2 + 1 / sin γ ^ 2 - 9 / 2 ≥ 0 := by
    have h14 : 0 < sin α ^ 2 * sin β ^ 2 * sin γ ^ 2 := by
      positivity
    have h15 : (1 / sin α ^ 2 + 1 / sin β ^ 2 + 1 / sin γ ^ 2 - 9 / 2) =
        (2 * (sin β ^ 2 * sin γ ^ 2 + sin α ^ 2 * sin γ ^ 2 + sin α ^ 2 * sin β ^ 2) - 9 * (sin α ^ 2 * sin β ^ 2 * sin γ ^ 2)) / (2 * sin α ^ 2 * sin β ^ 2 * sin γ ^ 2) := by
      field_simp
      ring
    rw [h15] at *
    apply div_nonneg
    · -- Prove the numerator is non-negative
      nlinarith [sq_nonneg (sin α ^ 2 - sin β ^ 2), sq_nonneg (sin α ^ 2 - sin γ ^ 2), sq_nonneg (sin β ^ 2 - sin γ ^ 2),
        sq_nonneg (sin α ^ 2 + sin β ^ 2 + sin γ ^ 2 - 2), h6, mul_pos h9 h10, mul_pos h9 h11, mul_pos h10 h11]
    · -- Prove the denominator is positive
      positivity
  linarith