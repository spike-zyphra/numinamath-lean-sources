import Mathlib

theorem algebra_10754 : IsLeast {n : ℕ | n > 0 ∧ ∑ i in Finset.range n, (i + 1) > 10 * n} 20 := by
  constructor
  · -- Show that 20 is in the set
    constructor
    · norm_num
    · -- Calculate the sum from 0 to 19 of (i + 1) and show it's greater than 200
      native_decide
  · -- Show that 20 is the least element of the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_sum⟩
    by_contra h
    push_neg at h
    have h1 : n ≤ 19 := by linarith
    interval_cases n <;> norm_num [Finset.sum_range_succ] at hn_sum ⊢ <;> all_goals omega