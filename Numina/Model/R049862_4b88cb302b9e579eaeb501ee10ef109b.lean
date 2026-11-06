import Mathlib

theorem algebra_68211 (x y z : ℝ) (h₀ : x + 2 * y + 3 * z = 3 * x + z) (h₁ : 3 * x + z = 6 * y) :
    2 * x + 2 * z = 5 * y := by 
  linarith