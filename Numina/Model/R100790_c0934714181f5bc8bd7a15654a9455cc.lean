import Mathlib

theorem algebra_163052 (a b c : ℕ) (h₀ : a + b + c = 56)
    (h₁ : b + 7 = 2 * (a - 7)) (h₂ : c + 5 = 3 * (b - 5)) :
    a = 15 ∧ b = 14 ∧ c = 27 := by
  omega