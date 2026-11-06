import Mathlib

theorem algebra_177608 (c r : ℕ) (h₀ : c * 2 + r * 4 = 250) (h₁ : r = c - 53) :
    r = 24 := by 
  rw [h₁] at h₀
  omega