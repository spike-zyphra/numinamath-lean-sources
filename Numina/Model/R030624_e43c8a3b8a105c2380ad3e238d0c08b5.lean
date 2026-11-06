import Mathlib

theorem algebra_19337 : IsGreatest {n : ℕ | (∑ i in Finset.Icc 1 n, i) ^ 2 < ∑ i in Finset.Icc 1 7, i ^ 3} 6 := by
  constructor
  · -- Show 6 is in the set
    show (∑ i in Finset.Icc 1 6, i) ^ 2 < ∑ i in Finset.Icc 1 7, i ^ 3
    norm_num [Finset.sum_Icc_succ_top]
  · -- Show that if n is in the set, then n ≤ 6
    intro n hn
    have h : (∑ i in Finset.Icc 1 n, i) ^ 2 < ∑ i in Finset.Icc 1 7, i ^ 3 := hn
    by_contra h'
    push_neg at h'
    have h1 : n ≥ 7 := by linarith
    have h2 : (∑ i in Finset.Icc 1 n, i) ≥ 28 := by
      have h2 : n ≥ 7 := by linarith
      have h3 : (∑ i in Finset.Icc 1 n, i) ≥ (∑ i in Finset.Icc 1 7, i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · -- Show {1, 2, ..., 7} ⊆ {1, 2, ..., n}
          intro i hi
          simp at hi ⊢
          omega
        · -- Show that each term is non-decreasing
          intro i hi
          simp
      have h4 : (∑ i in Finset.Icc 1 7, i) = 28 := by
        norm_num [Finset.sum_Icc_succ_top]
      have h5 : (∑ i in Finset.Icc 1 n, i) ≥ 28 := by
        linarith [h3, h4]
      linarith
    -- Compute the right side of the inequality (which is 784)
    have h3 : (∑ i in Finset.Icc 1 n, i) ^ 2 ≥ (∑ i in Finset.Icc 1 7, i ^ 3) := by
      have h4 : (∑ i in Finset.Icc 1 7, i ^ 3) = 784 := by 
        norm_num [Finset.sum_Icc_succ_top]
      nlinarith [h2, h4, sq_nonneg ((∑ i in Finset.Icc 1 n, i : ℕ) - (28 : ℕ))]
    linarith