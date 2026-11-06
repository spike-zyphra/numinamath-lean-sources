import Mathlib

theorem algebra_15723 : IsLeast {n | 0 < n ∧ (n % 10 = 0 ∧ n % 11 = 0 ∧ n % 12 = 0)} 660 := by
  constructor
  · -- First, let's prove that 660 is in the set
    constructor
    · norm_num
    · -- Now we show that 660 is divisible by 10, 11, and 12
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
  · -- Now, let's prove that 660 is the smallest such number
    intro n hn
    rcases hn with ⟨hn_pos, ⟨hn_10, hn_11, hn_12⟩⟩
    by_contra h
    push_neg at h
    have h1 : n < 660 := by linarith
    interval_cases n <;> norm_num at hn_10 hn_11 hn_12 hn_pos <;> omega