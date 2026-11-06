import Mathlib

theorem number_theory_190857 :
    IsLeast {n | 1 < n ∧ ∀ i ∈ Finset.Icc 2 10, (n % i) = 1} 2521 := by
  constructor
  · -- Show 2521 is in the set.
    constructor
    · norm_num
    · intro i hi
      fin_cases hi <;> norm_num
  · -- Show 2521 is the smallest
    intro n hn
    rcases hn with ⟨hn1, h⟩
    by_contra h'
    push_neg at h'
    have h2 := h 2 (by norm_num)
    have h3 := h 3 (by norm_num)
    have h4 := h 4 (by norm_num)
    have h5 := h 5 (by norm_num)
    have h6 := h 6 (by norm_num)
    have h7 := h 7 (by norm_num)
    have h8 := h 8 (by norm_num)
    have h9 := h 9 (by norm_num)
    have h10 := h 10 (by norm_num)
    interval_cases n <;> omega