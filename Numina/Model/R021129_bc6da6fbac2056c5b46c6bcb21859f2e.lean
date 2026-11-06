import Mathlib

theorem algebra_260503 (v w t : ℕ) (h₀ : w = 50) (h₁ : t = 75)
    (h₂ : t = 3 * w) :
    w + t = 100 := by 
  rw [h₀] at h₂
  omega