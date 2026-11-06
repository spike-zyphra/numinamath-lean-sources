import Mathlib

theorem algebra_285812 (d r l : ℝ) (h₀ : d > 0) (h₁ : r > 0) (h₂ : l > 0)
    (h₃ : r * 10 = l * 12) (h₄ : r * 18 = l * 10) :
    r * 6 = l * 12 := by
  nlinarith