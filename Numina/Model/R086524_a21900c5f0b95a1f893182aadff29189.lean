import Mathlib

theorem number_theory_14653 {n : ℕ} (hn : n = 199) :
    (Nat.digits 2 n).sum - (Nat.digits 2 n).count 0 = 2 := by 
  subst hn 
  norm_num [Nat.digits, Nat.digitsAux]