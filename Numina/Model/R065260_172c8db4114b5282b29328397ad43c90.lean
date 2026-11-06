import Mathlib

theorem number_theory_110250 (n : ℕ) (h₀ : n > 0) (h₁ : n % 3 = 0) (h₂ : n % 4 = 0)
    (h₃ : n % 6 = 0) (h₄ : n - (n / 3) = (n / 4) + 3) :
    n / 6 = 6 := by 
  omega