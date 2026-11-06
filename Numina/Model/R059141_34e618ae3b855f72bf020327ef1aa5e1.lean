import Mathlib

theorem number_theory_292250 (l : ℕ) (hl : l = 100) (n : ℕ) (hn : n = 20)
    (h : n * l = 1000) :
    (1000 - n * l) / l ≤ 11 := by 
  subst hn
  subst hl
  omega