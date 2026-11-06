import Mathlib

theorem number_theory_236110 (n : ℕ) (h₀ : n < 50) (h₁ : n ≠ 0)
    (h₂ : (n / 7) + (n / 3) + (n / 2) = n) :
    n - (n / 7) - (n / 3) - (n / 2) = 18 := by 
  omega -- This tactic is powerful enough to handle arithmetic goals and contradictions.