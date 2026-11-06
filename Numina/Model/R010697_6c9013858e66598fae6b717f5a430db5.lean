import Mathlib

theorem algebra_610976 (x y z w : ℝ) (h₁ : 2 * x + y + z + w = 1) (h₂ : x + 3 * y + z + w = 2) (h₃ : x + y + 4 * z + w = 3) (h₄ : x + y + z + 5 * w = 25) : w = (11:ℝ) / 2 := by 
  linarith