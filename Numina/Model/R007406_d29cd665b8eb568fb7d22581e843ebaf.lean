import Mathlib

theorem number_theory_13474 :
    IsLeast {n : ℕ | 0 < n ∧ (n ^ 3) % 1000 = 888} 192 := by 
  constructor
  · -- First, show 192 is in the set, which requires showing 0 < 192 and 192^3 % 1000 = 888.
    constructor
    · -- Show 0 < 192
      norm_num
    · -- Show 192^3 % 1000 = 888
      norm_num
  · -- Now, show there is no smaller positive integer in the set.
    intro n hn
    rcases hn with ⟨hn_pos, hn_cube⟩
    by_contra h
    push_neg at h
    -- Since n < 192 by h, we need to show that none of the smaller positive integers satisfies n^3 ≡ 888 mod 1000
    interval_cases n <;> norm_num at hn_cube <;> all_goals omega