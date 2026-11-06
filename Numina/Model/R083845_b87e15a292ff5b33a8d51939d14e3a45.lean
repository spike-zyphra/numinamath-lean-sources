import Mathlib

theorem algebra_272265 (d v1 v2 : ℝ) (h₀ : d > 0) (h₁ : v1 > 0) (h₂ : v2 > 0)
    (h₃ : d / v1 = d / v2 + 42 / 8) (h₄ : d / v1 + 10 / 9 = d / v2 + 45 / 8) :
    d / v2 + 45 / 8 = 9.45 := by 
  linarith