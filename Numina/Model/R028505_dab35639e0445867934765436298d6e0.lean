import Mathlib

open Real Set
open scoped Real

theorem algebra_250561 (α β γ : ℝ) (h₀ : α + β + γ = π) (h₁ : α > 0) (h₂ : β > 0) (h₃ : γ > 0)
    (a b c : ℝ) (ha : a = b * sin α / sin β) (hb : b = c * sin β / sin γ) (hc : c = a * sin γ / sin α) :
    a^2 * sin (β - γ) / sin α + b^2 * sin (γ - α) / sin β + c^2 * sin (α - β) / sin γ = 0 := by

  have h4 : sin α ≠ 0 := by
    apply ne_of_gt
    apply sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith [show α < π by linarith [h₀, h₁, h₂, h₃]]

  have h5 : sin β ≠ 0 := by
    apply ne_of_gt
    apply sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith [show β < π by linarith [h₀, h₁, h₂, h₃]]

  have h6 : sin γ ≠ 0 := by
    apply ne_of_gt
    apply sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith [show γ < π by linarith [h₀, h₁, h₂, h₃]]
  have h7 : b = a * sin β / sin α := by
    have h8 : a = b * sin α / sin β := ha
    field_simp [h5] at h8 ⊢
    nlinarith
  have h12 : c = a * sin γ / sin α := by
    have h9 : c = b * sin γ / sin β := by
      have h10 : b = c * sin β / sin γ := hb
      field_simp [h6] at h10 ⊢
      nlinarith
    rw [h9, h7]
    field_simp [h5, h4]
    all_goals ring
  have h13 : sin (β - γ) = sin β * cos γ - cos β * sin γ := by rw [sin_sub]
  have h14 : sin (γ - α) = sin γ * cos α - cos γ * sin α := by rw [sin_sub]
  have h15 : sin (α - β) = sin α * cos β - cos α * sin β := by rw [sin_sub]
  rw [show b = a * sin β / sin α by linarith [h7], show c = a * sin γ / sin α by linarith [h12]]
  rw [h13, h14, h15]
  have h17 : α + β + γ = π := h₀
  have h18 : cos γ = - cos (α + β) := by
    have h19 : γ = π - (α + β) := by linarith
    rw [h19]
    have h20 : cos (π - (α + β)) = - cos (α + β) := by
      rw [cos_pi_sub]
    linarith
  have h21 : cos (α + β) = cos α * cos β - sin α * sin β := by
    rw [cos_add]
  have h22 : cos γ = - cos α * cos β + sin α * sin β := by
    linarith [h18, h21]
  field_simp [h4, h5, h6]
  have h26 : sin α ^ 2 + cos α ^ 2 = 1 := by exact Real.sin_sq_add_cos_sq α
  have h27 : sin β ^ 2 + cos β ^ 2 = 1 := by exact Real.sin_sq_add_cos_sq β
  have h28 : sin γ ^ 2 + cos γ ^ 2 = 1 := by exact Real.sin_sq_add_cos_sq γ
  nlinarith [sq_nonneg (sin α - sin β), sq_nonneg (sin β - sin γ), sq_nonneg (sin γ - sin α), sq_nonneg (cos α - cos β), sq_nonneg (cos β - cos γ), sq_nonneg (cos γ - cos α),
            Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_sq_add_cos_sq γ, h22, Real.sin_sq_add_cos_sq γ]