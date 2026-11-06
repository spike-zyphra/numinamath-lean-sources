import Mathlib

theorem number_theory_136923 :
    Set.ncard {i | ∃ k, Odd k ∧ k ≤ 333 ∧ ∑ j in Finset.range i, (27 - j) = k} = 10 := by
  have h1 : {i | ∃ k, Odd k ∧ k ≤ 333 ∧ ∑ j in Finset.range i, (27 - j) = k} = {1, 2, 5, 6, 9, 10, 13, 14, 17, 18} := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume i is in the set
      rintro ⟨k, h_odd, hk_le, h_eq⟩
      have h1 : i ≤ 18 := by
        by_contra h
        push_neg at h
        have h2 : i ≥ 19 := by omega 
        have h3 : ∑ j in Finset.range i, (27 - j) > 333 := by 
          have h4 : i ≥ 19 := h2 
          have h6 : ∑ j in Finset.range 19, (27 - j) = 342 := by 
            norm_num [Finset.sum_range_succ]
          have h7 : ∑ j in Finset.range i, (27 - j) ≥ ∑ j in Finset.range 19, (27 - j) := by 
            apply Finset.sum_le_sum_of_subset_of_nonneg 
            · -- Show that Finset.range 19 is a subset of Finset.range i
              intro j hj 
              simp at hj ⊢ 
              omega 
            · -- Show that each element is less than or equal 
              intro j hj 
              simp at hj ⊢
          linarith [h6, h7] 
        have h5 : k > 333 := by 
          have h9 : k = ∑ j in Finset.range i, (27 - j) := by linarith
          rw [h9] at *
          linarith 
        linarith 
      interval_cases i <;> try { 
        norm_num [Finset.sum_range_succ, Nat.odd_iff] at h_eq h_odd hk_le ⊢ 
        <;> try { 
          omega 
        }
        <;> tauto 
      }
    · -- Assume i is in {1, 2, 5, 6, 9, 10, 13, 14, 17, 18}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- i = 1
        use 27 
        all_goals native_decide 
      · -- i = 2
        use 53 
        all_goals native_decide 
      · -- i = 5
        use 125 
        all_goals native_decide 
      · -- i = 6
        use 147 
        all_goals native_decide 
      · -- i = 9
        use 207 
        all_goals native_decide 
      · -- i = 10
        use 225 
        all_goals native_decide 
      · -- i = 13
        use 273 
        all_goals native_decide 
      · -- i = 14
        use 287 
        all_goals native_decide 
      · -- i = 17
        use 323 
        all_goals native_decide 
      · -- i = 18
        use 333 
        all_goals native_decide 
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try native_decide