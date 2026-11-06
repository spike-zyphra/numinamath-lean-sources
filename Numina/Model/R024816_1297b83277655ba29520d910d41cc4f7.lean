import Mathlib

theorem number_theory_35925 {n : ℕ} (hn : n > 0) :
    IsLeast {n | 0 < n ∧ ∃ k, n + 10 = k^2 ∧ ∃ m, n * 10 = m^2} 90 := by
  constructor
  · -- Show 90 is in the set
    constructor
    · norm_num
    · use 10
      constructor
      · norm_num
      · use 30
        all_goals norm_num
  · -- Show no smaller positive integer is in the set
    intro n hn
    rcases hn with ⟨hn_pos, k, hk_sq, m, hm_sq⟩
    by_contra h
    push_neg at h
    have h1 : k ≤ 9 := by
      nlinarith
    have h2 : m ≤ 29 := by
      nlinarith [show n * 10 < 900 from by nlinarith, sq_nonneg (m : ℕ)]
    interval_cases k <;> try { 
      interval_cases m <;> omega 
    }