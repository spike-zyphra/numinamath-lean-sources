import Mathlib

theorem algebra_285135 (r b g : ℕ) (h₀ : r + b + g = 14)
    (h₁ : r = 2 * g) (h₂ : b = g / 2) :
    g = 4 := by 
  rw [h₁, h₂] at h₀
  omega