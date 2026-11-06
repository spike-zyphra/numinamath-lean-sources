import Mathlib

theorem algebra_14420 :
    IsLeast {n | 0 < n ∧ 9 ∣ n ∧ ¬n % (Nat.digits 10 n).sum = 0} 99 := by
  constructor
  · -- Show 99 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Show ¬99 % (Nat.digits 10 99).sum = 0
      norm_num
  · -- Show there is no smaller element in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_div, hn_not_lucky⟩
    by_contra h
    push_neg at h
    -- Since n is smaller than 99 and divisible by 9, it must be one of: 9, 18, 27, 36, 45, 54, 63, 72, 81, 90.
    -- Let's verify each one to show they're not bad (they're luck).
    interval_cases n <;> norm_num at hn_div hn_not_lucky
    all_goals
      contradiction