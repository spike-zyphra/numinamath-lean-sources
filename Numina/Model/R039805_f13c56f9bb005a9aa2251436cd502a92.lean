import Mathlib

theorem algebra_145012 (x : ℕ) (hx : x > 0) (h : ∑ i ∈ Finset.range x, (18 + 4 * i) = 2000) :
    x = 28 := by

  have h1 : x ≤ 28 := by
    by_contra h2 
    push_neg at h2 
    have h2 : x ≥ 29 := by omega
    have h3 : ∑ i in Finset.range x, (18 + 4 * i) ≥ ∑ i in Finset.range 29, (18 + 4 * i) := by 
      apply Finset.sum_le_sum_of_subset_of_nonneg 
      · -- Show that range 29 is a subset of range x 
        intro i hi 
        simp at hi ⊢ 
        omega 
      · -- Show that for i in range 29, the terms are ≤ 
        intro i hi 
        simp 
    have h4 : ∑ i in Finset.range 29, (18 + 4 * i) = 2146 := by 
      norm_num [Finset.sum_range_succ]
    have h9 : ∑ i in Finset.range x, (18 + 4 * i) ≥ 2146 := by 
      linarith [h3, h4]
    linarith 
  have h2 : x ≥ 28 := by 
    by_contra h3 
    push_neg at h3 
    have h3 : x ≤ 27 := by omega
    have h4 : ∑ i in Finset.range x, (18 + 4 * i) ≤ ∑ i in Finset.range 27, (18 + 4 * i) := by 
      apply Finset.sum_le_sum_of_subset_of_nonneg 
      · -- Show that range x is a subset of range 27 
        intro i hi 
        simp at hi ⊢ 
        omega 
      · -- Show that for i in range x, the terms are ≤ 
        intro i hi 
        simp 
    have h5 : ∑ i in Finset.range 27, (18 + 4 * i) = 1890 := by 
      norm_num [Finset.sum_range_succ]
    have h6 : ∑ i in Finset.range x, (18 + 4 * i) ≤ 1890 := by 
      linarith [h4, h5]
    linarith 
  linarith