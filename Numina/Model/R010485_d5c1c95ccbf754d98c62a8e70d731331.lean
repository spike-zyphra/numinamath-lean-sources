import Mathlib

theorem number_theory_276758 (n : ℕ) 
    (h₀ : n < 100000) (h₁ : 10000 ≤ n) 
    (h₂ : 10 * n + 1 = 3 * (100000 + n)) :
    n = 42857 := by
  omega