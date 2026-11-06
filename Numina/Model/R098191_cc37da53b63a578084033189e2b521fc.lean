import Mathlib

theorem algebra_195560 (d v1 v2 : ℝ) (h₀ : d > 0) (h₁ : v1 > 0) (h₂ : v2 > 0)
    (h₃ : d / v1 = d / v2 + 16) (h₄ : d / v1 + 9 = d / v2) :
    d / v1 = 28 := by
  linarith