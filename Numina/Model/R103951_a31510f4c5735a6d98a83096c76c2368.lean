import Mathlib

theorem number_theory_15470 :
    IsLeast {n | 0 < n ∧ 25 ∣ n ∧ ∃ k, 0 < k ∧ k * 25 = (Nat.digits 10 n).prod} 525 := by
  constructor
  · -- Show that 525 is in the set
    constructor
    · norm_num -- 0 < 525
    constructor
    · norm_num -- 25 divides 525
    use 2
    constructor
    · norm_num -- 0 < 2
    · -- Show that 2 * 25 = product of digits
      norm_num
  · -- Show that any number n < 525 in the set is invalid
    intro n hn
    rcases hn with ⟨hn_pos, hn_div, ⟨k, hk_pos, hk_mul⟩⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn_div <;> norm_num at hk_mul <;> omega