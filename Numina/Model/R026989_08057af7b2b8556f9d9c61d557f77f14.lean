import Mathlib

theorem number_theory_314898 (n : ℕ) (h : n > 0) (a : ℕ) (ha : a ∈ Finset.Icc 1 n)
    (h' : ∑ i ∈ Finset.Icc 1 n, i = 1986 - a) :
    a = 33 := by
  rw [Finset.mem_Icc] at ha
  rcases ha with ⟨ha1, han⟩
  have h1 : n ≤ 62 := by
    by_contra h2
    push_neg at h2
    have h2' : n ≥ 63 := by omega
    have h3 : ∑ i in Finset.Icc 1 n, i ≥ ∑ i in Finset.Icc 1 63, i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · -- Show that Finset.Icc 1 63 ⊆ Finset.Icc 1 n
        intro i hi
        simp at hi ⊢
        omega
      · -- Show that for i ∈ Finset.Icc 1 63, i ≤ i
        intro i hi
        simp
    have h4 : ∑ i in Finset.Icc 1 63, i = 2016 := by
      norm_num [Finset.sum_Icc_succ_top]
    have h5 : ∑ i in Finset.Icc 1 n, i ≥ 2016 := by
      linarith [h3, h4]
    omega
  have h2 : n ≥ 62 := by
    by_contra h3
    push_neg at h3
    have h4' : n ≤ 61 := by omega
    have h4 : ∑ i in Finset.Icc 1 n, i ≤ ∑ i in Finset.Icc 1 61, i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · -- Show that Finset.Icc 1 n ⊆ Finset.Icc 1 61
        intro i hi
        simp at hi ⊢
        omega
      · -- Show that for i ∈ Finset.Icc 1 n, i ≤ i
        intro i hi
        simp
    have h5 : ∑ i in Finset.Icc 1 61, i = 1891 := by
      norm_num [Finset.sum_Icc_succ_top]
    have h6 : ∑ i in Finset.Icc 1 n, i ≤ 1891 := by
      linarith [h4, h5]
    omega
  have h3 : n = 62 := by
    omega
  have h4 : ∑ i in Finset.Icc 1 n, i = 1953 := by
    rw [h3]
    norm_num [Finset.sum_Icc_succ_top]
  omega