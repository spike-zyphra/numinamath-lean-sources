import Mathlib

theorem number_theory_11864 : IsLeast {n : ℕ | 1 < n ∧ ∀ m ∈ Set.Icc 2 9, n % m = 1} 2521 := by 
  constructor 
  · -- Show 2521 is in the set
    constructor 
    · norm_num 
    · -- Show that for all m in the range 2 ≤ m ≤ 9, 2521 % m = 1
      intro m hm
      have h2 : m ≥ 2 := by 
        have h : m ∈ Set.Icc (2 : ℕ) 9 := hm
        simp at h ⊢ 
        omega 
      have h3 : m ≤ 9 := by 
        have h : m ∈ Set.Icc (2 : ℕ) 9 := hm
        simp at h ⊢ 
        omega
      interval_cases m <;> norm_num
  · -- Show that 2521 is minimal. Assume n is in the set, prove n ≥ 2521
    intro n hn 
    rcases hn with ⟨hn1, h⟩ 
    have h2 := h 2 (by norm_num)
    have h3 := h 3 (by norm_num)
    have h4 := h 4 (by norm_num)
    have h5 := h 5 (by norm_num)
    have h6 := h 6 (by norm_num)
    have h7 := h 7 (by norm_num)
    have h8 := h 8 (by norm_num)
    have h9 := h 9 (by norm_num)
    by_contra h'
    push_neg at h'
    have h10 : n < 2521 := h'
    interval_cases n <;> omega