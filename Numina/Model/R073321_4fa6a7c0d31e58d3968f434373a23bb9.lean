import Mathlib

theorem number_theory_218604 (n : ℕ) (h : n % 35 = 7) :
    n % 15 = 2 ∨ n % 15 = 7 ∨ n % 15 = 12 := by 
  omega