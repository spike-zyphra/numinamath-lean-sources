import Mathlib

theorem algebra_10980 {a b c : ℤ} (h₀ : a + b = 29) (h₁ : b + c = 46)
    (h₂ : a + c = 53) : a + b + c = 64 := by 
  linarith