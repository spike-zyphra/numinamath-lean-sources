import Mathlib

open Real Set
open scoped Real

theorem inequalities_196805 (α β γ : ℝ) (h : α + β + γ = π) (h₁ : α ∈ Ioo 0 π)
  (h₂ : β ∈ Ioo 0 π) (h₃ : γ ∈ Ioo 0 π) :
  sin γ ^ 2 ≥ sin (2 * α) * sin (2 * β) := by
    have hα1 : 0 < α := h₁.left
    have hα2 : α < π := h₁.right
    have hβ1 : 0 < β := h₂.left
    have hβ2 : β < π := h₂.right
    have hγ1 : 0 < γ := h₃.left
    have hγ2 : γ < π := h₃.right
    have h5 : γ = π - (α + β) := by linarith
    have h6 : sin γ = sin (α + β) := by
      rw [h5]
      have h7 : sin (π - (α + β)) = sin (α + β) := by
        rw [sin_pi_sub]
      exact h7
    have h7 : sin γ = sin α * cos β + cos α * sin β := by
      rw [h6]
      rw [sin_add]
    have h8 : sin (2 * α) = 2 * sin α * cos α := by
      rw [sin_two_mul]
    have h9 : sin (2 * β) = 2 * sin β * cos β := by
      rw [sin_two_mul]
    rw [h7, h8, h9]
    nlinarith [sq_nonneg (sin α * cos β - cos α * sin β), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_le_one α, Real.sin_le_one β, Real.sin_le_one γ, mul_pos (show 0 < α from hα1) (show 0 < β from hβ1), mul_pos (show 0 < β from hβ1) (show 0 < γ from hγ1), mul_pos (show 0 < α from hα1) (show 0 < γ from hγ1), Real.sin_pos_of_pos_of_lt_pi hα1 hα2, Real.sin_pos_of_pos_of_lt_pi hβ1 hβ2, Real.sin_pos_of_pos_of_lt_pi hγ1 hγ2, sq_nonneg (sin α - sin β), sq_nonneg (cos α - cos β)]