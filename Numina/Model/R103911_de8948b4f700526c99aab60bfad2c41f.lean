import Mathlib

theorem number_theory_192699 (n : ℕ) (h : n = 23) :
    Nat.factorial n = 25852016738884976640000 := by 
  rw [h]
  norm_num [Nat.factorial]