import Mathlib

theorem number_theory_4265 (x : ℕ) (h₀ : 100 ≤ x) (h₁ : x < 1000) (h₂ : 7 * x % 6 = 1) (h₃ : 4 * x % 7 = 6) (h₄ : 7 * x % 13 = 3) :
    x = 565 := by
  interval_cases x <;> omega