import Mathlib

theorem number_theory_233190 :
    IsLeast {n | n ≥ 100000 ∧ n % 3 = 0 ∧ n % 7 = 0 ∧ n % 13 = 0} 100191 := by
  constructor
  · -- Show 100191 is in the set
    show 100191 ≥ 100000 ∧ 100191 % 3 = 0 ∧ 100191 % 7 = 0 ∧ 100191 % 13 = 0
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that 100191 is the smallest element in the set
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3, hn4⟩
    omega