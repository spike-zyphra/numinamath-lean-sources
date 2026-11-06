import Mathlib

theorem algebra_188419 (d v1 v2 : ℝ) (h₀ : d > 0) (h₁ : v1 > 0) (h₂ : v2 > 0)
    (h₃ : d / v1 = 16 + d / v2) (h₄ : d / v2 = 25 + d / v1) :
    d / v1 = 36 := by
  linarith