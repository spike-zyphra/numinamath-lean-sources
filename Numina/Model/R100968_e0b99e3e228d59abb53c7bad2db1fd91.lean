import Mathlib

theorem algebra_181062 (d v : ℝ) (h₀ : d > 0) (h₁ : v > 0)
    (h₂ : d / v = 8 - 7) (h₃ : d / v + 20 / 60 = 8 - 7) :
    d / v = 50 := by 
  linarith