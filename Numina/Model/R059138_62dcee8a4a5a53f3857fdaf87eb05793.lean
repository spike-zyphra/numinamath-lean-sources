import Mathlib

theorem algebra_14015 (a b c d : ℝ)
    (h₀ : a^2 = 9) (h₁ : b^2 = 16) (h₂ : c^2 = 36)
    (h₃ : d^2 = a^2 + b^2 + c^2) :
    d^2 = 61 := by 
  rw [h₃, h₀, h₁, h₂]
  norm_num