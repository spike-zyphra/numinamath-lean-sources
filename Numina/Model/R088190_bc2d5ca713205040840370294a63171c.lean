import Mathlib

theorem number_theory_232859 (n : ℕ) (h₀ : n > 0) (h₁ : (n * 7 + 3) > 0)
    (h₂ : (n * 7 + 3) * 10 + 1 = (n * 7 + 3) * 11) :
    n = 129 := by 
  omega