import Mathlib

theorem algebra_230452 (c z : ℝ) (h₀ : c + z = 400) (h₁ : 50 * 8.8 < c ∧ c < 50 * 9)
    (h₂ : 50 * 7.1 < z ∧ z < 50 * 7.2) :
    c ∈ Set.Ioo 200 400 ∧ z ∈ Set.Ioo 200 400 := by
  norm_num at h₁ h₂
  have h3 : c > 440 := by linarith [h₁.left]
  have h4 : c < 450 := by linarith [h₁.right]
  have h5 : z > 355 := by linarith [h₂.left]
  have h6 : z < 360 := by linarith [h₂.right]
  have h7 : c + z = 400 := h₀
  have h8 : z > 355 := h5
  have h9 : c < 45 := by linarith
  linarith