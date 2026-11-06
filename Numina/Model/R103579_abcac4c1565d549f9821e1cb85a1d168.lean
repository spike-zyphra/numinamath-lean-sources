import Mathlib

theorem number_theory_286311 :
    IsLeast {n | n ≠ 0 ∧ 3 ∣ n / 2 ∧ 4 ∣ n / 3 ∧ 11 ∣ n / 4 ∧ 5 = (n / 2) % 7} 528 := by
  constructor
  · -- Show that 528 is in the set
    constructor
    · norm_num -- n ≠ 0
    constructor
    · norm_num -- 3 divides 528 / 2
    constructor
    · norm_num -- 4 divides 528 / 3
    constructor
    · norm_num -- 11 divides 528 / 4
    · norm_num -- 5 = (528 / 2) % 7

  · -- Show that 528 is minimal
    intro n hn
    rcases hn with ⟨hnne0, h1, h2, h3, h4⟩
    by_contra h
    push_neg at h
    have h5 : n < 528 := by linarith
    interval_cases n <;> norm_num at *
    all_goals contradiction