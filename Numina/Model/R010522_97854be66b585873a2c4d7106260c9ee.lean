import Mathlib

theorem algebra_13370 :
    IsGreatest {n | 9 ∣ n ∧ -n > -100} 99 := by
  constructor
  · -- Show that 99 is in the set
    show 99 ∈ {n | 9 ∣ n ∧ -n > -100}
    constructor
    · -- Show 9 divides 99
      norm_num
    · -- Show -99 > -100
      norm_num
  · -- Show that any element in the set is ≤ 99
    intro n hn
    rcases hn with ⟨h9, h_neg⟩
    omega