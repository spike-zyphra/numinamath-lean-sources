import Mathlib

theorem algebra_209862 (d : ℝ) (h₀ : d > 0) (h₁ : 50 / (3 * d) = 12 / d) (h₂ : 50 / (1.5 * d) = 12 / d) :
    d = 130 := by
  have h3 : d ≠ 0 := by linarith
  have h4 : 3 * d ≠ 0 := by positivity
  have h5 : 1.5 * d ≠ 0 := by positivity
  field_simp [h4, h5, h3] at h₁ h₂
  nlinarith [h₀]