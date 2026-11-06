import Mathlib

theorem number_theory_12518 :
    IsLeast {n : ℕ | 0 < n ∧ (5 ^ n) % 3 = (n ^ 5) % 3} 4 := by
  constructor
  · constructor
    · -- Show that 4 is positive: 0 < 4
      norm_num
    · -- Show that 5^4 % 3 = 4^5 % 3
      norm_num
  · -- Show that 4 is the smallest element in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_cong⟩
    by_contra h
    push_neg at h
    have h1 : n < 4 := by linarith
    interval_cases n <;> norm_num at hn_cong <;> all_goals contradiction