import Mathlib

theorem number_theory_220009 (n : ℕ) (h : n > 0) (h1 : n % 3 = 1) (h2 : (n - 1) % 3 = 1) (h3 : (n - 2) % 3 = 1) :
    n = 79 := by 
  omega