import Mathlib

theorem algebra_233374 (n : ℕ) (h : n > 0) :
    ∑ i ∈ Finset.range n, (i + 1) ≥ 64 ↔ n ≥ 11 := by 
  constructor
  · -- Assume ∑ i ∈ Finset.range n, (i + 1) ≥ 64, prove n ≥ 11
    intro h1
    by_contra h2
    push_neg at h2
    have h3 : n ≤ 10 := by
      omega
    interval_cases n <;> norm_num [Finset.sum_range_succ] at h1 ⊢ <;> omega
  · -- Assume n ≥ 11, prove ∑ i ∈ Finset.range n, (i + 1) ≥ 64
    intro h2
    have h1 : ∑ i in Finset.range n, (i + 1) ≥ ∑ i in Finset.range 11, (i + 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg 
      · -- Show that range 11 is a subset of range n
        intro i hi
        simp only [Finset.mem_range] at hi ⊢
        omega
      · -- Show that each term is non-negative
        intro i hi
        simp
    have h2' : ∑ i in Finset.range 11, (i + 1) = 66 := by 
      norm_num [Finset.sum_range_succ]
    have h3 : ∑ i in Finset.range n, (i + 1) ≥ 66 := by 
      linarith [h1, h2']
    linarith [h3]