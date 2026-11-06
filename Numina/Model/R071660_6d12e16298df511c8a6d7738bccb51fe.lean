import Mathlib

theorem number_theory_210123 (n : ℕ) (h₀ : n % 5 = 1) (h₁ : (n - 1) % 5 = 1)
    (h₂ : (n - 2) % 5 = 1) (h₃ : (n - 3) % 5 = 1) (h₄ : (n - 4) % 5 = 1) :
    n ≥ 3121 := by 
  omega