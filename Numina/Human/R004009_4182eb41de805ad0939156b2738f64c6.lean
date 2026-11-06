import Mathlib

theorem my_favorite_theorem (a b c : ℕ) (h₀ : a < 10) (h₁ : b < 10) (h₂ : c < 10) (h₃ : (10 * a + 3) * (20 + b) = 300 + 10 * c + 2)
    : a + b + c = 6 := by
  interval_cases b <;> interval_cases a <;> omega