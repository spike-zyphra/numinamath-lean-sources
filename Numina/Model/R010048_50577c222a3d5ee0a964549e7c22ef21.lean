import Mathlib

theorem algebra_21965 (x y z : ℝ) (h₁ : 6 * x + 5 * y - 2 * z = -4) (h₂ : 4 * x + 5 * y + 12 * z = 54) :
    x + y + z = 5 := by 
  linarith