import Mathlib

theorem number_theory_231254 :
    ∃ n, (Nat.digits 10 (n^2)).sum = 80 ∨ (Nat.digits 10 (n^2)).sum = 81 := by 
  use 111111111
  norm_num