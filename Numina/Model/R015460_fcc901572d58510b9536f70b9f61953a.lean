import Mathlib

theorem number_theory_212454 :
    {(n, k) : ℕ × ℕ | n > 0 ∧ k > 1 ∧ ∑ i ∈ Finset.range k, (n + i) = 455}.ncard = 7 := by
  have h1 : {(n, k) : ℕ × ℕ | n > 0 ∧ k > 1 ∧ ∑ i ∈ Finset.range k, (n + i) = 455} = {(227, 2), (89, 5), (62, 7), (41, 10), (29, 13), (26, 14), (5, 26)} := by
    ext ⟨n, k⟩
    simp
    constructor
    · -- Assume h
      rintro ⟨hn, hk, heq⟩
      have h2 : k ≤ 30 := by
        by_contra h
        push_neg at h
        have h3 : ∑ i in Finset.range k, (n + i) ≥ ∑ i in Finset.range 31, (n + i) := by
          have h4 : Finset.range 31 ⊆ Finset.range k := by
            intro i hi
            simp at hi ⊢
            omega
          apply Finset.sum_le_sum_of_subset_of_nonneg h4
          intro i hi
          simp
        have h4 : ∑ i in Finset.range 31, (n + i) > 455 := by
          norm_num [Finset.sum_range_succ] at *
          all_goals
            omega
        have h5 : ∑ i in Finset.range k, (n + i) > 455 := by
          linarith
        linarith
      interval_cases k <;> try { 
        norm_num [Finset.sum_range_succ] at heq ⊢
        all_goals 
          try { 
            omega 
          } 
          <;> try { 
            tauto 
          }
      }
    · -- Show that (n, k) is in the left side
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (227, 2)
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Verify the sum
          norm_num [Finset.sum_range_succ]
      · -- (89, 5)
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Verify the sum
          norm_num [Finset.sum_range_succ]
      · -- (62, 7)
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Verify the sum
          norm_num [Finset.sum_range_succ]
      · -- (41, 10)
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Verify the sum
          norm_num [Finset.sum_range_succ]
      · -- (29, 13)
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Verify the sum
          norm_num [Finset.sum_range_succ]
      · -- (26, 14)
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Verify the sum
          norm_num [Finset.sum_range_succ]
      · -- (5, 26)
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Verify the sum
          norm_num [Finset.sum_range_succ]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { tauto }