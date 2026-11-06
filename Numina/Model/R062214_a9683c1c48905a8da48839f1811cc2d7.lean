import Mathlib

theorem number_theory_608196 (a b c d : ℕ) (h₀ : 0 < d) (h₁ : d < c) (h₂ : c < b) (h₃ : b < a)
    (h₄ : a < 10) (h₅ : a > 0) (h₆ : 1000 * a + 100 * b + 10 * c + d - (1000 * d + 100 * c + 10 * b + a) =
    1000 * b + 100 * d + 10 * a + c) :
    b + c + d = 11 := by
  interval_cases a <;> interval_cases b <;> interval_cases c <;> omega