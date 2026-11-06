import Mathlib

theorem algebra_185163 (h : ∑ k ∈ Finset.range T, (6 * (k + 1)) = 468) :
    (∑ k ∈ Finset.range (T / 2), (6 * (k + 1))) / 468 = 7 / 26 := by 
  have h1 : T ≤ 12 := by
    by_contra h2
    push_neg at h2
    have h2' : T ≥ 13 := by omega
    have h2'' : ∑ k in Finset.range T, (6 * (k + 1)) ≥ ∑ k in Finset.range 13, (6 * (k + 1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · -- Show that Finset.range 13 is a subset of Finset.range T
        intro k hk
        simp at hk ⊢
        omega
      · -- Show that each term is non-decreasing
        intro k hk
        simp at *
        all_goals linarith
    have h3 : ∑ k in Finset.range 13, (6 * (k + 1)) = 546 := by
      norm_num [Finset.sum_range_succ]
    have h4 : ∑ k in Finset.range T, (6 * (k + 1)) ≥ 546 := by
      linarith [h2'', h3]
    omega
  have h2 : T ≥ 12 := by
    by_contra h2
    push_neg at h2
    have h2' : T ≤ 11 := by omega
    have h2'' : ∑ k in Finset.range T, (6 * (k + 1)) ≤ ∑ k in Finset.range 11, (6 * (k + 1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · -- Show that Finset.range T is a subset of Finset.range 11
        intro k hk
        simp at hk ⊢
        omega
      · -- Show that each term is non-decreasing
        intro k hk
        simp at *
        all_goals linarith
    have h3 : ∑ k in Finset.range 11, (6 * (k + 1)) = 396 := by
      norm_num [Finset.sum_range_succ]
    have h4 : ∑ k in Finset.range T, (6 * (k + 1)) ≤ 396 := by
      linarith [h2'', h3]
    omega
  have hT : T = 12 := by
    omega
  rw [hT]
  norm_num [Finset.sum_range_succ]
  all_goals linarith