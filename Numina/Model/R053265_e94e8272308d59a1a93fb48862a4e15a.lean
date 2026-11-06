import Mathlib

theorem algebra_16431 :
    IsLeast {n | (Nat.digits 10 n).length = 3 ∧ 2 ∣ n ∧ 5 ∣ n ∧ 7 ∣ n} 140 := by 
  constructor
  · -- Show that 140 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that any element in the set is greater or equal to 140
    intro n hn
    rcases hn with ⟨h1, h2, h3, h4⟩
    by_contra h
    push_neg at h
    have h5 : n < 140 := by omega
    have h6 : n >= 100 := by
      by_contra h
      push_neg at h
      interval_cases n <;> norm_num at h1 ⊢
      all_goals try { contradiction }
      all_goals omega
    interval_cases n <;> norm_num at h1 h2 h3 h4 <;> all_goals omega