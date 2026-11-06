import Mathlib

open Finset

theorem number_theory_41265 : IsLeast {n : ℕ | n > 1 ∧ ∃ k, ∑ i ∈ Icc 1 n, (2 * i - 1) = k ^ 6} 8 := by 
  constructor
  · -- Show that 8 is in the set
    constructor
    · norm_num
    · use 2
      native_decide
  · -- Show that 8 is the smallest
    intro n hn
    rcases hn with ⟨hn1, ⟨k, hk⟩⟩
    by_contra h
    push_neg at h
    interval_cases n <;> try { 
      norm_num [sum_Icc_succ_top, mul_comm] at hk 
      all_goals
        try { 
          have : k ≤ 3 := by
            by_contra h'
            push_neg at h'
            have h1 : k ^ 6 > (3 ^ 6 : ℕ) := by
              have h4 : k ≥ 4 := by omega
              have h5 : k ^ 6 ≥ (4 : ℕ) ^ 6 := by
                apply Nat.pow_le_pow_of_le_left
                all_goals omega
              have h6 : (4 : ℕ) ^ 6 > (3 : ℕ) ^ 6 := by norm_num
              have h7 : k ^ 6 > (3 : ℕ) ^ 6 := by linarith
              linarith
            norm_num at h1
            all_goals omega
          interval_cases k <;> omega
        }
    }