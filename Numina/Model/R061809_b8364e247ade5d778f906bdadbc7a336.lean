import Mathlib

theorem number_theory_213776 : IsLeast {N : ℕ | 0 < N ∧ N % 7 = 5 ∧ N % 8 = 6 ∧ N % 9 = 7} 502 := by
  constructor
  · -- Show 502 is in the set
    show 0 < 502 ∧ 502 % 7 = 5 ∧ 502 % 8 = 6 ∧ 502 % 9 = 7
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show minimality: there is no smaller element in the set
    intro N
    intro h
    rcases h with ⟨hN_pos, hN_mod_7, hN_mod_8, hN_mod_9⟩
    by_contra h'
    push_neg at h'
    interval_cases N <;> omega