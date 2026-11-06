import Mathlib

theorem number_theory_5170 : IsLeast {N | 0 < N ∧ N % 7 = 5 ∧ N % 17 = 10} 61 := by
  constructor
  · -- Show 61 is in the set
    constructor
    · norm_num -- 61 > 0
    constructor
    · norm_num -- 61 % 7 = 5
    · norm_num -- 61 % 17 = 10

  · -- Show 61 is the smallest
    intro N hN
    rcases hN with ⟨hN_pos, hN_mod7, hN_mod17⟩
    by_contra h
    push_neg at h
    interval_cases N <;> omega