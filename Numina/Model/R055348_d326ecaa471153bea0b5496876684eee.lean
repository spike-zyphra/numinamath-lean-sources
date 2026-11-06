import Mathlib

theorem algebra_190143 {a b : ℕ} (h₀ : a > 0) (h₁ : b > 0)
    (h₂ : a * 100 = b * 10 + 9) :
    a + b = 723 := by
  omega