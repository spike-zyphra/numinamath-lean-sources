import Mathlib

theorem number_theory_15084 :
    IsLeast {n : ℕ | 0 < n ∧ 18 ∣ n^2 ∧ 640 ∣ n^3} 120 := by
  constructor
  · -- Show 120 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that 120 is the smallest in the set
    intro n hn
    rcases hn with ⟨hn_pos, h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : n < 120 := by linarith
    interval_cases n <;> norm_num at h1 h2 hn_pos