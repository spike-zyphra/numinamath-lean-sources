import Mathlib

theorem algebra_15064 : IsLeast {n | 0 < n ∧ 32 ∣ n} 32 := by
  constructor
  · -- Show 32 is in the set
    constructor
    · norm_num
    · norm_num
  · -- Show there is no smaller element in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    omega