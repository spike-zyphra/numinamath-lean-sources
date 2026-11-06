import Mathlib

theorem algebra_19224 : IsLeast {n | n > 0 ∧ ∑ i ∈ Finset.range n, (100 * (i + 1)) ≥ 12000} 15 := by
  constructor
  · -- Show that 15 is in the set
    constructor
    · norm_num 
    · norm_num [Finset.sum_range_succ]
  · -- Show that 15 is the least element in the set
    intro n hn
    rcases hn with ⟨hn_pos, hsum⟩
    by_contra h
    push_neg at h 
    have h1 : n ≤ 14 := by omega
    have h2 : ∑ i in Finset.range n, (100 * (i + 1)) < 12000 := by
      interval_cases n <;> norm_num [Finset.sum_range_succ]
    linarith