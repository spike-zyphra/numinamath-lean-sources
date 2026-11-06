import Mathlib

theorem number_theory_1215 :
    {n : ℕ | ∃ k, n ≥ 2 ∧ 77 = ∑ i ∈ Finset.range n, (k + i)}.encard = 3 := by
  have h1 : {n : ℕ | ∃ k, n ≥ 2 ∧ 77 = ∑ i ∈ Finset.range n, (k + i)} = {2, 7, 11} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- First, prove the forward direction: if n is in the left side, it's in the right.
      intro h
      rcases h with ⟨k, hn, heq⟩
      have h2 : n ≤ 22 := by
        by_contra h
        push_neg at h
        have h3 : ∑ i in Finset.range n, (k + i) > 77 := by
          have h4 : ∑ i in Finset.range n, (k + i) ≥ ∑ i in Finset.range 23, (k + i) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg 
            · -- Show {0, 1, ..., 22} subset of {0, 1, ..., n-1} when n > 22
              intro i hi 
              simp at hi ⊢ 
              omega 
            · -- Show adder is non-negative
              intro i _ 
              simp 
          have h5 : ∑ i in Finset.range 23, (k + i) > 77 := by 
            norm_num [Finset.sum_range_succ]
            all_goals omega
          linarith [h4, h5]
        linarith 
      interval_cases n <;> norm_num [Finset.sum_range_succ] at heq ⊢
      <;> omega 
    · -- Now the reverse direction: each value in {2,7,11} is in the left side.
      rintro (rfl | rfl | rfl)
      · -- n = 2
        use 38 
        all_goals
          native_decide 
      · -- n = 7
        use 8 
        all_goals
          native_decide 
      · -- n = 11
        use 2 
        all_goals
          native_decide 
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { aesop }