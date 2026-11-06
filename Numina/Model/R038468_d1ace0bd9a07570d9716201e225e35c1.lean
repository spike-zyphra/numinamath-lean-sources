import Mathlib

theorem other_60977 :
  IsGreatest {N : ℕ | ∑ i ∈ Finset.Icc 1 N, i ≤ 60} 10 := by

  constructor
  · -- Show that 10 is in the set
    show ∑ i in Finset.Icc 1 10, i ≤ 60
    native_decide
  · -- Show that 10 is the greatest in the set
    intro N hN
    have h1 : ∑ i in Finset.Icc 1 N, i ≤ 60 := hN
    by_contra h
    push_neg at h
    have h2 : N ≥ 11 := by
      omega
    have h3 : ∑ i in Finset.Icc 1 N, i > 60 := by
      have h4 : N ≥ 11 := h2
      have h5 : ∑ i in Finset.Icc 1 N, i ≥ ∑ i in Finset.Icc 1 11, i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg 
        · -- Show that Icc 1 11 ⊆ Icc 1 N
          intro i hi
          simp at hi ⊢
          omega
        · -- Show that i ≤ i for i ∈ Icc 1 11
          intro i hi
          simp
      have h6 : ∑ i in Finset.Icc 1 11, i = 66 := by 
        native_decide
      have h7 : ∑ i in Finset.Icc 1 11, i = 66 := h6
      linarith 
    linarith