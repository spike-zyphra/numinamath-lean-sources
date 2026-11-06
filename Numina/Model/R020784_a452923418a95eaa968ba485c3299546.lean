import Mathlib

theorem number_theory_201151 {n : ℕ} (hn : n > 0) (h : ∃ k, k = n / 2 ∧ ∑ i ∈ Finset.range k, (i + 1) = 74) :
    n = 9 := by 
  rcases h with ⟨k, hk, hsum⟩
  have h1 : k ≤ 13 := by 
    by_contra h
    push_neg at h
    -- Assume k > 13, so the sum from 0 to k-1 must be ≥ sum from 0 to 13
    have h2 : ∑ i in Finset.range k, (i + 1) ≥ ∑ i in Finset.range 14, (i + 1) := by
      have h4 : Finset.range 14 ⊆ Finset.range k := by
        intro i hi
        simp at hi ⊢
        omega
      apply Finset.sum_le_sum_of_subset_of_nonneg h4
      intro i hi
      simp
    -- Calculate the sum from 1 to 14: 105
    have h3 : ∑ i in Finset.range 14, (i + 1) = 105 := by 
      norm_num [Finset.sum_range_succ]
    -- Therefore the sum must be greater or equal to 105
    have h4 : ∑ i in Finset.range k, (i + 1) ≥ 105 := by 
      linarith [h2, h3]
    -- This is contradiction with hsum which tells the sum is 74
    omega
  interval_cases k <;> try { 
    -- Now k is bounded by k ≤ 13.
    -- Let's compute the sum i+1 from i=0 to k-1 for each possible value of k
    -- Then get contradiction
    norm_num [Finset.sum_range_succ] at hsum ⊢
    all_goals omega 
  }