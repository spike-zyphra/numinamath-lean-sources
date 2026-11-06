import Mathlib

theorem number_theory_210704 (a b c d e f : ℕ) (hcoprime : ∀ m n, m ≠ n → Nat.Coprime m n) :
    IsLeast {x | ∃ m n, x = m * n ∧ m ≠ n ∧ m ≤ 6 ∧ n ≤ 6} 4 := by 
  exfalso 
  have h1 := hcoprime 2 4 (by norm_num)
  norm_num [Nat.Coprime] at h1
  all_goals try { trivial }