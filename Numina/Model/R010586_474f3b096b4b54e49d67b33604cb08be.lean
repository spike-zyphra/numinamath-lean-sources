import Mathlib

theorem algebra_14048 {a b c : ℝ} (h₀ : a + b + c = 99) (h₁ : a + 6 = b - 6) (h₂ : b - 6 = 5 * c) :
    b = 51 := by 
  linarith