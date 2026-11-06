import Mathlib

theorem algebra_6851
    (a b : ℝ)
    (h₀ : 0 < a)
    (h₁ : 0 < b)
    (h₂ : a ^ 2 - b ^ 2 = 128)
    (h₃ : a = 8 - b) :
    b - a = -16 := by 
  rw [h₃] at h₂
  nlinarith