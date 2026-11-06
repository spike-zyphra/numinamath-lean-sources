import Mathlib

theorem algebra_20376 : IsLeast {n | ∑ i in Finset.Icc (-25) n, i ≥ 26} 26 := by 
  constructor 
  · -- Show that 26 is in the set 
    native_decide 
  · -- Show that 26 is minimal 
    intro n hn
    have h : ∑ i in Finset.Icc (-25) n, i ≥ 26 := by 
      simpa using hn 
    by_contra h'
    push_neg at h'
    have h1 : n < 26 := h'
    have h3 : n ≤ 25 := by omega 
    have h4 : n ≥ -25 := by 
      by_contra h5 
      push_neg at h5 
      have h5 : n < -25 := by omega 
      have h6 : Finset.Icc (-25) n = ∅ := by 
        apply Finset.Icc_eq_empty_iff.mpr 
        omega 
      rw [h6] at h 
      contradiction 
    interval_cases n <;> try { contradiction }