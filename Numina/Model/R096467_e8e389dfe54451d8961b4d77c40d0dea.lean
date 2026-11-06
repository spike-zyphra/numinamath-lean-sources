import Mathlib

theorem algebra_2555 (a b c d e f : ℝ)
    (h₀ : a = 1 / 2) (h₁ : b = 1 / 4) (h₂ : c = 1 / 6)
    (h₃ : d = 1 / 8) (h₄ : e = 1 / 10) (h₅ : f = 1 / 12) :
    (a + b + c + d + e + f) - (d + e) = 1 := by
  rw [h₀, h₁, h₂, h₃, h₄, h₅]
  norm_num