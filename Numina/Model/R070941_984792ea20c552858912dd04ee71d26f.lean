import Mathlib

theorem number_theory_185952 :
    IsLeast {n | (Nat.digits 10 (n ^ 2)).contains 7 ∧ (Nat.digits 10 ((n + 1) ^ 2)).contains 7} 26 := by 
  constructor
  · -- Show 26 is in the set
    constructor
    · -- Show 26^2 contains 7
      native_decide
    · -- Show 27^2 contains 7
      native_decide 
  · -- Show no smaller element is in the set
    intro n hn
    rcases hn with ⟨h1, h2⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at h1 h2 <;> all_goals
      contradiction