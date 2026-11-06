import Mathlib

theorem algebra_236885 (x y : ℝ) (h₀ : x - 2 * y = 1) (h₁ : x ^ 3 - 8 * y ^ 3 - 6 * x * y = 1) :
    (x - 1) / 2 = y := by 
  linarith