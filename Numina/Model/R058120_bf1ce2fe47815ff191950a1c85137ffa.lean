import Mathlib

theorem number_theory_233683 :
    ∃ n : ℕ, (Nat.digits 10 n).length = 10 ∧ (Nat.digits 10 n).toFinset.card = 10 ∧ 1980 ∣ n := by 
  use 2384715960
  all_goals norm_num