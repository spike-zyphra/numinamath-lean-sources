import Mathlib

theorem algebra_21933 (a b c : ℝ) (h₀ : a = 6) (h₁ : b = 6) (h₂ : a^2 + b^2 = c^2) :
    a * b / 2 = 18 := by
  rw [h₀, h₁]
  norm_num