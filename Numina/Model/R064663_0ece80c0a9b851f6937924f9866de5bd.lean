import Mathlib

theorem number_theory_222635 (n : ℕ) (h : n = 2011533) :
    Nat.digits 10 n = [3, 3, 5, 1, 1, 0, 2] := by 
  rw [h]
  all_goals norm_num