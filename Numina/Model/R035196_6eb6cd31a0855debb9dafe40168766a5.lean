import Mathlib

theorem number_theory_230248 :
    {k : ℕ | k > 0 ∧ (∑ i ∈ Finset.range k, (i + 1)^2) = 2870} = {20} := by
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume k > 0 ∧ (∑ i in Finset.range k, (i + 1) ^ 2) = 2870, prove k = 20
    intro h
    rcases h with ⟨hk_pos, heq⟩
    have h1 : k ≤ 20 := by
      by_contra h2
      push_neg at h2
      have h2' : k ≥ 21 := by omega
      have h3 : (∑ i in Finset.range k, (i + 1) ^ 2) > 2870 := by
        have h4 : k ≥ 21 := h2'
        have h5 : (∑ i in Finset.range k, (i + 1) ^ 2) ≥ (∑ i in Finset.range 21, (i + 1) ^ 2) := by
          have h6 : Finset.range 21 ⊆ Finset.range k := by 
            intro i hi
            simp at hi ⊢
            omega
          apply Finset.sum_le_sum_of_subset_of_nonneg h6
          intro i hi 
          simp 
        have h7 : (∑ i in Finset.range 21, (i + 1) ^ 2) > 2870 := by
          norm_num [Finset.sum_range_succ]
        linarith
      linarith
    have h2 : k ≥ 1 := by omega
    have h1 : k ≤ 20 := h1
    interval_cases k <;> try { norm_num [Finset.sum_range_succ] at heq ⊢ <;> omega }
  · -- Show 20 is in the left side set
    intro heq
    rw [heq]
    constructor
    · -- Show 20 > 0
      norm_num
    · -- Show ∑ i in Finset.range 20, (i + 1) ^ 2 = 2870
      norm_num [Finset.sum_range_succ]