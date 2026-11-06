import Mathlib

theorem number_theory_192425 (m n p : ℕ) (h₀ : m < 10) (h₁ : n < 10) (h₂ : p < 10)
    (h₃ : (m * 100 + n * 10 + p) - (n * 100 + m * 10 + p) = 180) :
    (m * 100 + m * 10 + p) - (n * 100 + n * 10 + p) = 220 := by
  omega