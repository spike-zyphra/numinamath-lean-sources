import Mathlib

theorem number_theory_187465 (n : ℕ) (h₀ : 300 < n) (h₁ : n < 400)
    (h₂ : n % 21 = 13) (h₃ : (n + 8) % 15 = 0) : n = 307 := by
  omega