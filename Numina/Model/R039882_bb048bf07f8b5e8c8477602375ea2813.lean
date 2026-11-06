import Mathlib

theorem number_theory_19297 :
    IsLeast {n : ℕ | 3 < n ∧ ∃ k, (∑ i ∈ Finset.Icc 1 n, i) ^ 2 = k ^ 4} 8 := by
  constructor
  · -- Show that 8 is in the set
    constructor
    · -- Show that 8 > 3
      norm_num
    · -- Show that there exists a k such that (1 + ... + 8) ^ 2 = k ^ 4
      use 6
      native_decide
  · -- Show that 8 is the least element in the set
    intro n hn
    rcases hn with ⟨hn3, k, hk⟩
    by_contra h
    push_neg at h
    have h1 : n ≤ 7 := by linarith
    interval_cases n <;> try { 
      norm_num [Finset.sum_Icc_succ_top] at hk
      all_goals 
        try { 
          have : k ≤ 7 := by
            by_contra h2
            push_neg at h2
            have h2 : k ^ 4 ≥ 8 ^ 4 := by
              have : k ≥ 8 := by nlinarith
              have : k ^ 4 ≥ 8 ^ 4 := by
                apply Nat.pow_le_pow_of_le_left 
                linarith 
              linarith
            nlinarith
          interval_cases k <;> omega 
        }
    }