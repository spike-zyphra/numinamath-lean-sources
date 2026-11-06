import Mathlib

theorem number_theory_19288 : IsLeast {n : ℤ | n > 0 ∧ 8 ∣ n ∧ 9 ∣ n - 1 ∧ 10 ∣ n - 2} 352 := by
  constructor
  · -- Show 352 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that 352 is the least such number
    intro n hn
    rcases hn with ⟨hn_pos, h8, h9, h10⟩
    omega