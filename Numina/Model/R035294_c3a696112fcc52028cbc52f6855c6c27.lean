import Mathlib

theorem number_theory_5788 : IsLeast {n : ℕ | 0 < n ∧ (n % 5 = 3 ∧ n % 7 = 5 ∧ n % 13 = 11 ∧ n % 17 = 15)} 7733 := by
  constructor
  · -- Show 7733 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that 7733 is the least such number
    intro n hn
    rcases hn with ⟨hn_pos, ⟨h5, h7, h13, h17⟩⟩
    by_contra h
    push_neg at h
    have h1 : n % 5 = 3 := h5
    have h2 : n % 7 = 5 := h7
    have h3 : n % 13 = 11 := h13
    have h4 : n % 17 = 15 := h17
    omega