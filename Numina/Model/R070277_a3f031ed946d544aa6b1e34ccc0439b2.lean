import Mathlib

theorem algebra_128561 (d : ℝ) (h₀ : d > 0) (h₁ : (1 / 2) * d = (1 / 3) * (d - 100)) (h₂ : (1 / 3) * d = (1 / 2) * (d - 108)) :
    d = 3750 := by 
  linarith