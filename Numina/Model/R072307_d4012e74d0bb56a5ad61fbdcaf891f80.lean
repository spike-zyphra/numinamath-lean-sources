import Mathlib

theorem algebra_281810 (T : ℤ) (a b c d : ℤ) (h₀ : a + b + c + d = T) :
    3 * (a + 1 + b + 1 + c + 1 + d + 1) = 3 * T + 12 := by 
  linarith [h₀]