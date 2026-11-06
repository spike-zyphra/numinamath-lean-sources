import Mathlib

theorem number_theory_34191 :
    IsLeast {n | 100 ≤ n ∧ 77 ∣ ∑ i ∈ Finset.range (n + 1), 2 ^ i} 119 := by 
  constructor
  · -- Show 119 is in the set 
    constructor
    · norm_num 
    · native_decide 
  · -- Show that 119 is the minimum 
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    by_contra h
    push_neg at h 
    have h1 : n < 119 := by linarith 
    have h2 : n ≥ 100 := by linarith
    interval_cases n <;> norm_num [Finset.sum_range_succ] at hn2 ⊢