import Mathlib

theorem number_theory_115597 (n : ℕ) (h₀ : n > 0) (h₁ : ∃ k, n = 4 * k) (h₂ : ∃ m, m > 0)
    (h₃ : n = 7 * m) (h₄ : n = 8 * m) (h₅ : n = 9 * m) (h₆ : n = 10 * m) :
    n = 1008 := by 
  omega