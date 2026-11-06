import Mathlib

theorem number_theory_54743 :
    IsLeast {n : ℕ | 0 < n ∧ ∃ k, n^3 + 2 * n^2 = k^2 ∧ Odd k} 7 := by
  constructor
  · -- Show 7 belongs to the set
    constructor
    · norm_num
    · -- Show existence of k
      use 21
      all_goals norm_num
      <;> decide
  · -- Show that 7 is the smallest
    intro n hn
    rcases hn with ⟨hn_pos, k, hk, hk_odd⟩
    by_contra h
    push_neg at h
    have h1 : n < 7 := by
      omega
    interval_cases n <;> try { 
      have h2 : k < 42 := by
        nlinarith
      interval_cases k <;> norm_num [Nat.odd_iff] at hk_odd
      <;> omega
    }