import Mathlib

theorem number_theory_85971 :
IsLeast {n | 0 < n ∧ 17 ∣ n ∧ (Nat.digits 10 n).sum = 17} 476 := by
  constructor
  · -- Show 476 is in the set.
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show there is no smaller element in the set.
    intro n hn
    rcases hn with ⟨hn_pos, hn_div, hn_sum⟩
    by_contra h
    push_neg at h
    have h1 : n < 476 := by linarith
    have h2 : n % 17 = 0 := by 
      omega 
    interval_cases n <;> norm_num at hn_div hn_sum h2 <;> try { contradiction }