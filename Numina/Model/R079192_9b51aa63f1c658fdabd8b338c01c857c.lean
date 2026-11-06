import Mathlib

theorem number_theory_16511 (n : ℤ) (h : n % 6 = 1) : (n + 2010) % 6 = 1 := by 
  omega -- automatically handle integer arithmetic