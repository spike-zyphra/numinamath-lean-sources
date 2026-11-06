import Mathlib

theorem number_theory_256943 (n : ℕ) (h : n > 0) :
    ∑ i ∈ Finset.range n, (i + 1) = 480 - 15 ↔ n = 30 := by
  constructor
  · -- Assume the sum from i = 0 to n-1 of (i + 1) equals 465, prove n = 30
    intro h1
    have h2 : n ≤ 30 := by
      by_contra h2
      push_neg at h2
      have h3 : n ≥ 31 := by omega
      have h4 : ∑ i in Finset.range n, (i + 1) > 480 - 15 := by
        have h5 : ∑ i in Finset.range 31, (i + 1) > 480 - 15 := by
          norm_num [Finset.sum_range_succ]
        have h6 : ∑ i in Finset.range n, (i + 1) ≥ ∑ i in Finset.range 31, (i + 1) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · -- Show that range 31 ⊆ range n
            intro x hx
            simp at hx ⊢
            all_goals omega
          · -- Show that each term is non-negative
            intro x hx
            simp at hx ⊢
            all_goals omega
        linarith [h5, h6]
      linarith
    interval_cases n <;> try { norm_num [Finset.sum_range_succ] at h1 <;> all_goals trivial }
  · -- Assume n = 30, prove the sum from i = 0 to n-1 of (i + 1) equals 465
    intro h2
    rw [h2]
    norm_num [Finset.sum_range_succ]