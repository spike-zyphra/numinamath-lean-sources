import Mathlib

theorem number_theory_179467 (n : ℕ) (h : n = 2016) :
    ∃ p q, p * q = n ∧ Nat.digits 10 p = List.reverse (Nat.digits 10 p) ∧
    Nat.digits 10 q = List.reverse (Nat.digits 10 q) ↔ p = 8 ∧ q = 252 := by 
  use 8, 252 
  rw [h] 
  norm_num 
  <;> norm_num 
  all_goals norm_num