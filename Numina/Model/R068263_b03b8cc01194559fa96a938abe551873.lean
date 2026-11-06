import Mathlib

theorem number_theory_99985 :
    IsLeast {n | n ≥ 1000 ∧ (Nat.digits 10 n).prod = 512} 1888 := by 
  constructor
  · -- 1888 is in the set
    constructor
    · norm_num
    · norm_num
  · -- no smaller element is in the set
    intro n hn
    rcases hn with ⟨hn1, hprod⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hprod <;> all_goals omega