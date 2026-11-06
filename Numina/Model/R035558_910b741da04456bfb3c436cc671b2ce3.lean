import Mathlib

theorem algebra_11876 :
    IsLeast {n | 0 < n ∧ ∀ i ∈ Finset.range 8, n % (i + 1) = 0} 840 := by
  constructor
  · -- Show 840 is in the set
    constructor
    · norm_num
    · -- Show ∀ i ∈ Finset.range 8, 840 % (i + 1) = 0
      intro i hi
      fin_cases hi <;> norm_num
  · -- Show that 840 is the least
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    have h1 : n % 1 = 0 := by
      apply hn_div 0 
      simp
    have h2 : n % 2 = 0 := by
      apply hn_div 1 
      simp
    have h3 : n % 3 = 0 := by
      apply hn_div 2 
      simp
    have h4 : n % 4 = 0 := by 
      apply hn_div 3 
      simp
    have h5 : n % 5 = 0 := by 
      apply hn_div 4 
      simp
    have h6 : n % 6 = 0 := by 
      apply hn_div 5 
      simp 
    have h7 : n % 7 = 0 := by 
      apply hn_div 6 
      simp
    have h8 : n % 8 = 0 := by 
      apply hn_div 7 
      simp 
    have h9 : n < 840 := h
    interval_cases n <;> omega