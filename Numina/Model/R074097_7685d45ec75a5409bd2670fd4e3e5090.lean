import Mathlib

theorem algebra_242326 (a b c d x y : ℝ) (h₀ : a + b = 189) (h₁ : a + c = 320)
    (h₂ : a + d = 287) (h₃ : b + c = 264) (h₄ : b + d = x) (h₅ : c + d = y) :
    x + y ≤ 761 := by 
  linarith