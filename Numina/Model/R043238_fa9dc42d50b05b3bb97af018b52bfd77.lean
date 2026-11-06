import Mathlib

theorem number_theory_14384 : IsLeast {x | x % 7 = 0 ∧ ∀ i ∈ Finset.Icc 2 6, x % i = 1} 301 := by
  constructor
  · -- Show 301 is in the set
    constructor
    · norm_num
    · intro i hi
      fin_cases hi <;> norm_num
  · -- Show there's no smaller element in the set
    intro x h
    rcases h with ⟨h7, h⟩
    have h2 := h 2 (by norm_num)
    have h3 := h 3 (by norm_num)
    have h4 := h 4 (by norm_num)
    have h5 := h 5 (by norm_num)
    have h6 := h 6 (by norm_num)
    by_contra h8
    push_neg at h8
    interval_cases x <;> omega