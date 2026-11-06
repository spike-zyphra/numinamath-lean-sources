import Mathlib

theorem algebra_286348 (butter sugar : ℝ)
    (h₀ : butter = 25) (h₁ : sugar = 125) (h₂ : 1000 / sugar * butter = x) :
    x = 200 := by
  rw [h₀, h₁] at h₂
  field_simp at h₂
  linarith