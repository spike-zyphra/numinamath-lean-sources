import Mathlib

theorem algebra_229275 (n : ℕ) (hn : n > 0) (h : ∑ i ∈ Finset.range n, (50 + 10 * i) = 2900) :
    n = 20 := by

  have h1 : n ≤ 20 := by
    by_contra h1
    push_neg at h1
    have h3 : n ≥ 21 := by omega
    have h2 : ∑ i in Finset.range n, (50 + 10 * i) > 2900 := by
      have h3 : n ≥ 21 := by omega
      have h4 : ∑ i in Finset.range n, (50 + 10 * i) ≥ ∑ i in Finset.range 21, (50 + 10 * i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · -- Show that range 21 is a subset of range n
          intro i hi
          simp at hi ⊢
          omega
        · -- Show that for i in range 21, (50 + 10 * i) ≤ (50 + 10 * i)
          intro i hi
          simp
      have h5 : ∑ i in Finset.range 21, (50 + 10 * i) > 2900 := by
        norm_num [Finset.sum_range_succ]
      linarith
    linarith
  have h2 : n ≥ 20 := by
    by_contra h2
    push_neg at h2
    have h3 : n ≤ 19 := by omega
    have h6 : ∑ i in Finset.range n, (50 + 10 * i) < 2900 := by
      have h3 : n ≤ 19 := by omega
      interval_cases n <;> norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  have eq : n = 20 := by
    omega
  exact_mod_cast eq