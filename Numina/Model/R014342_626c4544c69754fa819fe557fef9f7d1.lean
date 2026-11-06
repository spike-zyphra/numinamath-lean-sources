import Mathlib

theorem number_theory_305317 :
    {(n, k) : ℕ × ℕ | n > 0 ∧ k > 1 ∧ ∑ i ∈ Finset.range k, (n + i) = 15}.ncard = 3 := by
  have h1 : {(n, k) : ℕ × ℕ | n > 0 ∧ k > 1 ∧ ∑ i ∈ Finset.range k, (n + i) = 15} = {(7, 2), (4, 3), (1, 5)} := by
    ext ⟨n, k⟩
    simp
    constructor
    · rintro ⟨hn, hk, h⟩
      have h2 : k ≤ 10 := by
        by_contra h
        push_neg at h
        have h3 : ∑ i in Finset.range k, (n + i) > 15 := by
          have h4 : k ≥ 11 := by omega
          have h5 : ∑ i in Finset.range k, (n + i) ≥ ∑ i in Finset.range 11, (n + i) := by
            have h6 : Finset.range 11 ⊆ Finset.range k := by
              intro i hi
              simp at hi ⊢
              omega
            apply Finset.sum_le_sum_of_subset_of_nonneg h6
            intro i hi
            simp at hi ⊢
            all_goals omega
          have h7 : ∑ i in Finset.range 11, (n + i) > 15 := by
            norm_num [Finset.sum_range_succ] at *
            all_goals omega
          linarith
        linarith
      interval_cases k <;> try { 
        norm_num [Finset.sum_range_succ] at h 
        all_goals try { 
          omega 
        } 
      }
      <;> try { 
        all_goals try { 
          omega 
        } 
      }
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Show that (7, 2) is in the set
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show that the sum is 15
          norm_num [Finset.sum_range_succ]
      · -- Show that (4, 3) is in the set
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show that the sum is 15
          norm_num [Finset.sum_range_succ]
      · -- Show that (1, 5) is in the set
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show that the sum is 15
          norm_num [Finset.sum_range_succ]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { aesop }