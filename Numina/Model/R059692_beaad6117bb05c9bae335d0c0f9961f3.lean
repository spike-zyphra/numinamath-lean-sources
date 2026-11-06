import Mathlib

theorem number_theory_247289 (n : ℕ) (h : n > 0) (a : ℕ) (ha : a ∈ Finset.Icc 1 n)
    (h' : ∑ i ∈ Finset.Icc 1 n, i = 228 - a) :
    n = 20 := by 
  have h1 : a ≥ 1 := by 
    have h1 : a ∈ Finset.Icc 1 n := ha
    simp at h1 ⊢ 
    omega 
  have h2 : a ≤ n := by 
    have h2 : a ∈ Finset.Icc 1 n := ha
    simp at h2 ⊢ 
    all_goals omega 
  have h3 : ∑ i ∈ Finset.Icc 1 n, i = 228 - a := h'
  have h4 : n ≤ 20 := by 
    by_contra h5 
    push_neg at h5 
    have h6 : n ≥ 21 := by omega 
    have h7 : ∑ i ∈ Finset.Icc 1 n, i ≥ 231 := by 
      have h8 : n ≥ 21 := h6 
      have h9 : ∑ i ∈ Finset.Icc 1 n, i ≥ ∑ i ∈ Finset.Icc 1 21, i := by 
        apply Finset.sum_le_sum_of_subset_of_nonneg 
        · intro x hx 
          simp at hx ⊢ 
          omega 
        · intro x hx 
          simp at hx ⊢ 
          all_goals omega 
      have h10 : ∑ i ∈ Finset.Icc 1 21, i = 231 := by 
        norm_num [Finset.sum_Icc_succ_top]
      linarith [h9, h10] 
    have h8 : 228 - a ≤ 227 := by 
      omega 
    omega 
  have h5 : n ≥ 20 := by 
    by_contra h6 
    push_neg at h6 
    have h7 : n ≤ 19 := by omega 
    have h8 : ∑ i ∈ Finset.Icc 1 n, i ≤ 190 := by 
      have h9 : n ≤ 19 := h7 
      have h10 : ∑ i ∈ Finset.Icc 1 n, i ≤ ∑ i ∈ Finset.Icc 1 19, i := by 
        apply Finset.sum_le_sum_of_subset_of_nonneg 
        · intro x hx 
          simp at hx ⊢ 
          omega 
        · intro x hx 
          simp at hx ⊢ 
          all_goals omega 
      have h11 : ∑ i ∈ Finset.Icc 1 19, i = 190 := by 
        norm_num [Finset.sum_Icc_succ_top]
      linarith [h10, h11] 
    omega 
  have h12 : n = 20 := by omega 
  exact h12