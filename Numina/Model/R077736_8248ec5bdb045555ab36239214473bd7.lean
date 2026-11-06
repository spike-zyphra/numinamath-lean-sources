import Mathlib

theorem number_theory_7454 (n : ℕ) (h₀ : n % 2 = 1) (h₁ : n % 3 = 1) (h₂ : n % 4 = 1)
    (h₃ : n % 5 = 1) (h₄ : n % 6 = 1) (h₅ : n % 7 = 0) :
    n ≥ 301 := by 
  omega