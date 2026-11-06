import Mathlib

theorem algebra_21022 (x y : ℕ) (h₀ : x * 3 = y * 10) (h₁ : y = 30) :
    x = 100 := by 
  subst h₁ 
  omega