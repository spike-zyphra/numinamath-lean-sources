import Mathlib

theorem number_theory_95556 : ∃ n : ℕ, 0 < n ∧ 133^5 + 110^5 + 84^5 + 27^5 = n^5 := by
  use 144
  constructor 
  · norm_num 
  · 
    have h1 : 144 ^ 5 = 61917364224 := by 
      norm_num 
    rw [h1]
    all_goals norm_num