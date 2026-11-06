import Mathlib

theorem number_theory_70926 :
    IsLeast {n : ℕ | 0 < n ∧ ∃ k, k^2 = 2^n + 2^8 + 2^11} 12 := by
  constructor
  · -- Show that 12 is in the set
    constructor
    · norm_num -- Show that 12 is positive
    · use 80 -- There exists k such that k^2 = 2^12 + 2^8 + 2^11
      all_goals norm_num -- Verify the equation
  · -- Show that 12 is the smallest
    intro n hn
    rcases hn with ⟨hn_pos, ⟨k, hk⟩⟩
    by_contra h
    push_neg at h
    have h1 : n < 12 := by linarith
    interval_cases n <;> try { 
      norm_num at hk
      have h3 : k ≤ 80 := by nlinarith
      interval_cases k <;> try { omega }
      all_goals contradiction
    }