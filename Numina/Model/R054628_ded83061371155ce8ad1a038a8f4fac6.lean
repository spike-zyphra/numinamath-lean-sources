import Mathlib

theorem algebra_217675 (b r g : ℕ) (h₀ : b + r + g = 20)
    (h₁ : b = 6 * g) (h₂ : r < b) :
    r = 6 := by
  rw [h₁] at h₀ h₂
  omega