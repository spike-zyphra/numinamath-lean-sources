import Mathlib

theorem algebra_3478 (a b c d : ℤ) (h₀ : a + b + c = 44) (h₁ : a + b + d = 45)
    (h₂ : a + c + d = 49) (h₃ : b + c + d = 49) (h₄ : a = b) :
    a = 16 := by 
  rw [show b = a by linarith [h₄]] at h₀ h₃
  omega