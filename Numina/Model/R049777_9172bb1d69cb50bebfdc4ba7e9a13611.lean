import Mathlib

theorem algebra_282803 {x y : ℤ} (h₀ : x > y) (h₁ : x - y = 2) (h₂ : x + y = 20) :
    x = 11 := by 
  linarith