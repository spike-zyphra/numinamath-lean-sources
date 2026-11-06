import Mathlib

theorem algebra_243552 (h t : ℝ) (h₀ : 0 < h) (h₁ : 0 < t)
    (h₂ : h * 100 = t * 75) (h₃ : h * 50 = t * 60) :
    h * 60 = t * 54 := by
  nlinarith