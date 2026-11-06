import Mathlib

theorem algebra_12127 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 = c^2) (h₄ : a = 40) (h₅ : b = 42) :
    (1/2) * a * b = 840 := by 
  rw [h₄, h₅]
  norm_num