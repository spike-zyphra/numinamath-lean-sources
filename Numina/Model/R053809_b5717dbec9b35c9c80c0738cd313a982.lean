import Mathlib

theorem number_theory_290274 :
    IsLeast {n | (Nat.digits 10 n).length = 2 ∧ 6 ∣ n ∧ ¬4 ∣ n} 18 := by 
  constructor 
  · -- Show 18 is in the set
    constructor 
    · -- Show that the length of digits is 2
      norm_num 
    constructor 
    · -- Show that 6 divides 18
      norm_num 
    · -- Show that 18 is not divisible by 4
      norm_num 
  · -- Show that 18 is the smallest
    intro n hn 
    rcases hn with ⟨h1, h2, h3⟩ 
    by_contra h
    push_neg at h 
    interval_cases n <;> norm_num at h1 h2 h3 <;> all_goals contradiction