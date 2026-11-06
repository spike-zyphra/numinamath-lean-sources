import Mathlib

theorem number_theory_15183 :
  IsLeast { n:ℕ | 0<n ∧ (∀ i∈(Finset.Icc 1 9), (i ∣ n))} 2520 := by
  constructor 
  · -- Show 2520 is in the set.
    constructor
    · -- 2520 > 0 is true
      norm_num
    · -- Show that 2520 is divisible by i where i ∈ [1, 9]
      intro i hi
      fin_cases hi <;> norm_num
  · -- Show 2520 is the least.
    intro n hn
    rcases hn with ⟨hn_pos, h⟩
    have h1 : 1 ∣ n := h 1 (by norm_num)
    have h2 : 2 ∣ n := h 2 (by norm_num)
    have h3 : 3 ∣ n := h 3 (by norm_num)
    have h4 : 4 ∣ n := h 4 (by norm_num)
    have h5 : 5 ∣ n := h 5 (by norm_num)
    have h6 : 6 ∣ n := h 6 (by norm_num)
    have h7 : 7 ∣ n := h 7 (by norm_num)
    have h8 : 8 ∣ n := h 8 (by norm_num)
    have h9 : 9 ∣ n := h 9 (by norm_num)
    by_contra h'
    push_neg at h'
    interval_cases n <;> norm_num at h1 h2 h3 h4 h5 h6 h7 h8 h9 hn_pos h'