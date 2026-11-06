import Mathlib

theorem algebra_11174 (a b c d : ℕ)
    (h₀ : a + b = c + d) (h₁ : a + d = b + c + 4) (h₂ : c = 5) :
    a = 7 := by
  subst h₂
  omega