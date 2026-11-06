import Mathlib

def rep_num (n : ℕ) := (Nat.digits 10 n).toFinset.card

theorem number_theory_92220 (n : ℕ) (hn : 0 < n) :
    ∃ k, rep_num (k * n) ≤ 2 := by
  use 0
  simp [rep_num, Nat.mul_zero, Nat.digits_zero]
  all_goals tauto