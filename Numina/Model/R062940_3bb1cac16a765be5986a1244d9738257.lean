import Mathlib

theorem number_theory_11793 : IsLeast {n | (Nat.digits 10 n).length = 3 ∧ (Nat.digits 10 n).prod = 6} 116 := by
  constructor
  · -- Show 116 is in the set
    constructor
    · -- Check length of digits is 3
      norm_num
    · -- Check product of digits is 6
      norm_num
  · -- Now prove minimality
    intro n hn
    have h1 : (Nat.digits 10 n).length = 3 := hn.1
    have h2 : (Nat.digits 10 n).prod = 6 := hn.2
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at h1 h2 <;> all_goals
      all_goals omega