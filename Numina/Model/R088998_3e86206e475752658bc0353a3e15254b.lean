import Mathlib

theorem number_theory_131303 :
    IsLeast {n | 0 < n ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n) ∧ n % 3 = 2 ∧ n % 4 = 3 ∧ n % 5 = 0} 515 := by
  constructor
  · -- Show 515 is in the set
    constructor
    · norm_num
    constructor
    · native_decide
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show 515 is the smallest
    intro n hn
    rcases hn with ⟨hn_pos, hn_pal, hn_mod3, hn_mod4, hn_mod5⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn_pos hn_pal hn_mod3 hn_mod4 hn_mod5 <;> all_goals contradiction