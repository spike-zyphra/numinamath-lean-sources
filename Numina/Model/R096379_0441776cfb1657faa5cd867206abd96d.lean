import Mathlib

theorem number_theory_175222 (n : ℕ) (h : n > 0) (h' : 572 ≥ n * (n + 1)) :
    n + 1 ≤ 75 := by 
  nlinarith [sq_nonneg (n : ℕ), sq_nonneg ((23 : ℕ)), sq_nonneg ((75 : ℕ) - (n + 1)), h']