import Mathlib

theorem negated_number_theory_72031 :
    ∃ (m n : ℕ)
    (hm : 0 < m)
    (hn : 0 < n), 
    5 ∣ 2^n + 3^m → 
    5 ∣ 2^m + 3^n := by

  use 1, 1, by norm_num, by norm_num
  all_goals norm_num