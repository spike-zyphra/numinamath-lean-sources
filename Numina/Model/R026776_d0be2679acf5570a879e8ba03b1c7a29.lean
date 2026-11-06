import Mathlib

theorem number_theory_208015 (m n : ℕ) (hm : m > 0) (hn : n > 0)
    (hsum : ∑ i ∈ Finset.range (2 * 93 * m), (2 * i + 2) + ∑ i ∈ Finset.range n, (2 * i + 1) = 1987) :
    3 * m + 4 * n ≤ 221 := by
  have h1 : m ≥ 1 := by linarith
  have h2 : ∑ i in Finset.range (2 * 93 * m), (2 * i + 2) ≥ 34782 := by
    have h3 : m ≥ 1 := by linarith
    have h4 : 2 * 93 * m ≥ 186 := by 
      omega
    have h5 : ∑ i in Finset.range (2 * 93 * m), (2 * i + 2) ≥ ∑ i in Finset.range 186, (2 * i + 2) := by 
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · -- Show that Finset.range 186 is a subset of Finset.range (2 * 93 * m)
        intro i hi
        simp at hi ⊢
        omega
      · -- Show that each term (2 * i + 2) in the subset is ≤ the term in the superset
        intro i hi
        simp at hi ⊢
        all_goals omega
    have h6 : ∑ i in Finset.range 186, (2 * i + 2) = 34782 := by
      norm_num [Finset.sum_range_succ]
    linarith
  have h3 : ∑ i ∈ Finset.range n, (2 * i + 1) ≥ 1 := by 
    have h4 : n ≥ 1 := by linarith
    have h5 : ∑ i in Finset.range n, (2 * i + 1) ≥ ∑ i in Finset.range 1, (2 * i + 1) := by 
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · -- Show that Finset.range 1 is a subset of Finset.range n
        intro i hi
        simp at hi ⊢
        omega
      · -- Show that each term (2 * i + 1) in the subset is ≤ the term in the superset
        intro i hi
        simp at hi ⊢
        all_goals omega
    have h6 : ∑ i in Finset.range 1, (2 * i + 1) = 1 := by
      norm_num [Finset.sum_range_succ]
    linarith
  have h4 : ∑ i ∈ Finset.range (2 * 93 * m), (2 * i + 2) + ∑ i ∈ Finset.range n, (2 * i + 1) ≥ 34783 := by 
    linarith [h2, h3]
  omega