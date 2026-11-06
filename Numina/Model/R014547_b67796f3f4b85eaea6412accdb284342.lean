import Mathlib

theorem number_theory_167826 :
    IsLeast {n | n % 2 = 1 ∧ n % 3 = 1 ∧ n % 4 = 1 ∧ n % 5 = 1 ∧ n % 6 = 1 ∧ 7 ∣ n} 301 := by
  constructor
  · -- Show 301 is in the set.
    show 301 % 2 = 1 ∧ 301 % 3 = 1 ∧ 301 % 4 = 1 ∧ 301 % 5 = 1 ∧ 301 % 6 = 1 ∧ 7 ∣ 301
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
  · -- Show 301 is the smallest in the set
    intro n hn
    rcases hn with ⟨h1, h2, h3, h4, h5, h6⟩
    by_contra h
    push_neg at h
    have h7 : n < 301 := by linarith
    interval_cases n <;> omega