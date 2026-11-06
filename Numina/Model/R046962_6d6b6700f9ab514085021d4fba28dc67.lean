import Mathlib

open Real Set
open scoped Real

theorem algebra_255500 (θ : ℝ) (h₀ : θ ∈ Ioo π (3 * π / 2)) (h₁ : cos θ = -12 / 13) :
    cos (θ + π / 4) = -7 * sqrt 2 / 26 := by
  rcases h₀ with ⟨h2, h3⟩
  have h4 : sin θ < 0 := by
    have h5 : π < θ := h2
    have h6 : θ < 3 * π / 2 := h3
    have h10 : θ - π > 0 := by linarith
    have h11 : θ - π < π / 2 := by
      linarith [h6, Real.pi_pos]
    have h12 : sin θ = -sin (θ - π) := by
      rw [show θ = π + (θ - π) by ring]
      rw [sin_add, sin_pi, cos_pi]
      ring
    have h13 : sin (θ - π) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith [h11, Real.pi_pos]
    rw [h12]
    linarith
  have h5 : sin θ = -5 / 13 := by
    have h6 : sin θ ^ 2 + cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    rw [h₁] at h6
    have h7 : sin θ < 0 := h4
    have h8 : sin θ = -5 / 13 := by
      nlinarith [h7]
    exact h8
  have h8 : cos (θ + π / 4) = cos θ * cos (π / 4) - sin θ * sin (π / 4) := by
    rw [cos_add]
  rw [h8]
  have h9 : cos (π / 4) = Real.sqrt 2 / 2 := by
    rw [Real.cos_pi_div_four]
  have h10 : sin (π / 4) = Real.sqrt 2 / 2 := by
    rw [Real.sin_pi_div_four]
  rw [h9, h10, h₁, h5]
  field_simp
  ring_nf