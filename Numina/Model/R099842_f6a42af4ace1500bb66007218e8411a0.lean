import Mathlib

theorem algebra_190229 (a b c : ℝ) (h₀ : (a + b) / 2 = (a + b + c) / 3 + 5)
    (h₁ : (a + c) / 2 = (a + b + c) / 3 - 8) :
    (b + c) / 2 = (a + b + c) / 3 + 3 := by
  linarith