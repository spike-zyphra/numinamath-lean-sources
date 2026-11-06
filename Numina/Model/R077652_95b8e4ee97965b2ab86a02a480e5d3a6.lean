import Mathlib

theorem algebra_214243 (d q r : ℝ) (h₀ : d > 0) (h₁ : q > 0) (h₂ : r > 0)
    (h₃ : d / 4 + q / 3 + r / 6 = 1) (h₄ : q / 3 + r / 6 + d / 4 = 8 - 1) :
    d + q + r = 24 := by 
  linarith