import Mathlib

theorem number_theory_108527 :
    ∃ n, n + (Nat.digits 10 n).sum = 1980 ∧
    ∀ n, ∃ m, m = n ∨ m = n + 1 ∧ ∃ k, m = k + (Nat.digits 10 k).sum := by 
  use 1962
  constructor
  · norm_num
  · intro n 
    use n 
    left 
    rfl