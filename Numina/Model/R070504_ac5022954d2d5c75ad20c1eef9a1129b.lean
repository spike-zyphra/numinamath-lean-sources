import Mathlib

theorem number_theory_81661 (a b c : ℕ) (_ : 0 < a) (h₀ : 0 < b) (h₁ : 0 < c)
    (h₂ : 29 * a + 30 * b + 31 * c = 366) : 19 * a + 20 * b + 21 * c = 246 := by 
  omega