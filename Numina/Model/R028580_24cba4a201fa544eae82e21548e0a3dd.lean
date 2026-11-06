import Mathlib

theorem number_theory_116002 {n : ℕ} (hn : n + (Nat.digits 10 n).sum = 125) :
    n = 121 := by 
  have h1 : n ≤ 125 := by 
    have h2 : (Nat.digits 10 n).sum ≥ 0 := by
      apply Nat.zero_le
    omega
  interval_cases n <;> norm_num at hn ⊢
  <;> all_goals
    omega