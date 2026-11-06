import Mathlib

theorem algebra_274909 (a b c d : ℕ)
    (h₀ : b = a + 3) (h₁ : c = d - 2)
    (h₂ : a - 5 + b - 5 + c - 5 + d - 5 = 59)
    (h₃ : a + 5 + b + 5 + c + 5 + d + 5 = 97) :
    c = 33 := by
  rw [h₀, h₁] at h₂ h₃
  omega