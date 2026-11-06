import Mathlib

theorem number_theory_16840 : IsLeast {n : ℕ | n % 5 = 4 ∧ n % 6 = 5 ∧ n % 7 = 6 ∧ n % 8 = 7 ∧ n % 9 = 8 ∧ n % 10 = 9} 2519 := by
  constructor
  · -- Show 2519 is in the set
    show 2519 % 5 = 4 ∧ 2519 % 6 = 5 ∧ 2519 % 7 = 6 ∧ 2519 % 8 = 7 ∧ 2519 % 9 = 8 ∧ 2519 % 10 = 9
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show there is no smaller element in the set
    intro n hn
    rcases hn with ⟨h5, h6, h7, h8, h9, h10⟩
    by_contra h
    push_neg at h
    have h5' : n % 5 = 4 := h5
    have h6' : n % 6 = 5 := h6
    have h7' : n % 7 = 6 := h7
    have h8' : n % 8 = 7 := h8
    have h9' : n % 9 = 8 := h9
    have h10' : n % 10 = 9 := h10
    have h11 : n < 2519 := h
    interval_cases n <;> omega