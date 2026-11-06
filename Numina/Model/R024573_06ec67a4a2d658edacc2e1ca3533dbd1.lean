import Mathlib

theorem number_theory_55842 :
    IsLeast {n : ℕ | 0 < n ∧ ∃ k, (2010 * n) = k ^ 2} 2010 := by
  constructor
  · -- Show 2010 is in the set.
    constructor
    · norm_num
    · -- Show that there exists k such that 2010 * 2010 = k ^ 2.
      use 2010
      all_goals norm_num
  · -- Show there is no smaller positive integer in the set
    intro n hn
    rcases hn with ⟨hn_pos, ⟨k, hk⟩⟩
    by_contra h
    push_neg at h
    have h2 : (k : ℕ) < 2010 := by
      nlinarith [show 2010 * n < (2010 * 2010 : ℕ) by
        nlinarith
      ]
    have h4 : k ≤ 2009 := by
      omega
    have h6 : k ≥ 1 := by
      by_contra h6
      push_neg at h6
      have h6 : k = 0 := by
        omega
      rw [h6] at hk
      nlinarith
    interval_cases k <;> try { 
      omega 
    }
    <;> try { 
      nlinarith 
    }