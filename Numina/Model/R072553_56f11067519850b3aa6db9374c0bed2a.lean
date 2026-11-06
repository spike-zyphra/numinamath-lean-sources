import Mathlib

theorem number_theory_2476 :
    IsLeast {n | 0 < n ∧ 23 ∣ n ∧ n % 89 = 4} 805 := by
  constructor
  · -- Show that 805 is indeed in our set
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that 805 is the smallest
    intro n hn
    rcases hn with ⟨hn_pos, hn_div, hn_mod⟩
    omega