import Mathlib

theorem algebra_16461 :
IsLeast {n | (∃ k, n = ∑ i ∈ Finset.range 18, (k + i)) ∧ ∃ m, m ^ 2 = n} 225 := by
  constructor
  · -- Show 225 is in the set.
    constructor
    · -- Show that 225 is the sum of 18 consecutive numbers starting from 4.
      use 4
      native_decide
    · -- Show that 225 is a perfect square.
      use 15
      all_goals norm_num
  · -- Show 225 is the least.
    intro n hn
    rcases hn with ⟨⟨k, hk⟩, ⟨m, hm⟩⟩
    have h1 : n = 18 * k + 153 := by
      rw [hk]
      norm_num [Finset.sum_range_succ]
      <;> ring
    by_contra h
    push_neg at h
    have h2 : m ^ 2 < 225 := by
      linarith [h1, hm, h]
    have h3 : m < 15 := by
      nlinarith
    have h4 : m ≥ 0 := by
      by_contra h5
      push_neg at h5
      have h5 : m < 0 := by
        omega
      nlinarith [show m ^ 2 ≥ 0 by nlinarith, hm]
    interval_cases m <;> omega