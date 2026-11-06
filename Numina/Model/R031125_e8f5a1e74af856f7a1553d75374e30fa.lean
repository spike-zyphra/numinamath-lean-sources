import Mathlib

theorem number_theory_177834 :
    IsLeast {n | 0 < n ∧ ∃ k, n^3 = 588 * k} 42 := by
  constructor
  · -- First part: Show 42 is in the set.
    constructor
    · -- Show 42 > 0
      norm_num
    · -- Show there exists k such that 42^3 = 588 * k
      use 126
      all_goals norm_num
  · -- Second part: Show no smaller element is in the set.
    intro n hn
    rcases hn with ⟨hn_pos, ⟨k, hk⟩⟩
    by_contra h
    push_neg at h
    have h1 : n < 42 := h
    have h2 : k > 0 := by
      by_contra h3
      push_neg at h3
      have h4 : 588 * k ≤ 0 := by nlinarith
      have h5 : n^3 ≤ 0 := by linarith [hk, h4]
      have h6 : n > 0 := hn_pos
      have h7 : n^3 > 0 := by positivity
      nlinarith
    have h3 : n ≤ 41 := by
      omega
    interval_cases n <;> omega