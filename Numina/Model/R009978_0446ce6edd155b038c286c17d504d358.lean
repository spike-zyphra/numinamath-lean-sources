import Mathlib

theorem algebra_11087 {φ ψ : ℝ} (h : φ ≠ ψ) (h1 : φ^2 = φ + 1) (h2 : ψ^2 = ψ + 1) :
    (φ - ψ)^2 = 5 := by
  have h3 : φ^2 - ψ^2 = φ - ψ := by linarith
  have h4 : φ^2 - ψ^2 = (φ - ψ) * (φ + ψ) := by ring
  rw [h4] at h3
  have h5 : φ + ψ = 1 := by 
    apply (mul_left_inj' (sub_ne_zero.mpr h)).mp
    linarith
  have h6 : φ * ψ = -1 := by
    have h7 : (φ + ψ)^2 = φ^2 + ψ^2 + 2 * (φ * ψ) := by ring
    have h8 : (φ + ψ)^2 = 1 := by
      rw [h5]
      norm_num
    have h9 : φ^2 + ψ^2 = 3 := by
      nlinarith
      --  nlinarith [h1, h2]
    rw [h8, h9] at h7
    nlinarith
  have h10 : (φ - ψ) ^ 2 = 5 := by
    have h11 : (φ - ψ) ^ 2 = (φ^2 + ψ^2) - 2 * (φ * ψ) := by ring
    rw [h11]
    have h12 : φ^2 + ψ^2 = 3 := by 
      nlinarith
    have h13 : φ * ψ = -1 := h6
    nlinarith [h12, h13]
  exact h10