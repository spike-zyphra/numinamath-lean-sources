import Mathlib

theorem number_theory_221219 :
    IsLeast {n | 0 < n ∧ 111 ∣ n ∧ (n % 10000 = 2004)} 662004 := by
  constructor
  · -- Show 662004 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show there is no smaller element in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_div, hn_mod⟩
    omega