import Mathlib

theorem number_theory_4666 :
  IsLeast {n : ℕ | 0 < n ∧ 145 % n = 4 ∧ 97 % n = 3} 47 := by
  constructor
  · -- Show 47 is in the set
    constructor
    · norm_num -- 0 < 47
    constructor
    · norm_num -- 145 % 47 = 4
    · norm_num -- 97 % 47 = 3
  · -- Show no smaller natural is in the set
    intro n hn
    rcases hn with ⟨hn_pos, h1, h2⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at h1 h2 hn_pos <;> all_goals omega