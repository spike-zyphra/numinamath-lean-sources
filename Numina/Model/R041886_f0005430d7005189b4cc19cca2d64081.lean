import Mathlib

theorem number_theory_23036 :
    IsGreatest {n | n < 1000 ∧ 11 ∣ n} 990 := by
  constructor
  · -- Show 990 is in the set
    constructor
    · norm_num
    · norm_num
  · -- Show there is no greater element in the set
    intro n hn
    rcases hn with ⟨h1, h2⟩
    omega