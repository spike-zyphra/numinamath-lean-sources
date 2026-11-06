import Mathlib

theorem number_theory_13299 {n : ℕ} (hn : n = 0b100101110010) :
    n % 4 = 2 := by 
  subst hn 
  norm_num