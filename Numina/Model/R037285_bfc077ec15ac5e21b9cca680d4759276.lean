import Mathlib

theorem algebra_181755 (n : ℕ) (h : Even n) (h' : ∑ i ∈ Finset.range (n / 2), (2 * i + 2) = 2012 - (2 * n + 2)) :
    n = 58 := by
  have h1 : n ≤ 120 := by
    by_contra h1
    push_neg at h1
    have h2 : n / 2 ≥ 60 := by omega
    have h3 : ∑ i in Finset.range (n / 2), (2 * i + 2) ≥ ∑ i in Finset.range 60, (2 * i + 2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · -- Show that range 60 ⊆ range (n / 2)
        intro i hi
        simp at hi ⊢
        omega
      · -- Show that for i ∈ range 60, (2 * i + 2) ≤ (2 * i + 2)
        intro i hi
        simp at hi ⊢
    have h4 : ∑ i in Finset.range 60, (2 * i + 2) = 3660 := by
      native_decide
    have h5 : (2012 : ℕ) - (2 * n + 2) ≤ 1768 := by
      omega
    omega
  interval_cases n <;> try { contradiction } <;> try { native_decide }