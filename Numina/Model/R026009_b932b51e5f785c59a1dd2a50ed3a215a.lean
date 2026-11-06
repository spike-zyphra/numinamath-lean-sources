import Mathlib

theorem number_theory_1195 :
    ∑ᶠ m ∈ {m : ℕ | ∃ k, m > 1 ∧ ∑ i ∈ Finset.range m, (k + i) = 35}, m = 14 := by
  have h1 : {m : ℕ | ∃ k, m > 1 ∧ ∑ i ∈ Finset.range m, (k + i) = 35} = {2, 5, 7} := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First direction: if m is in the set, then m = 2, 5, or 7.
      rintro ⟨k, hm1, heq⟩
      have h2 : m ≤ 10 := by
        by_contra h3
        push_neg at h3
        have h3' : ∑ i in Finset.range m, (k + i) > 35 := by
          have h4 : m ≥ 11 := by omega
          have h5 : ∑ i in Finset.range m, (k + i) ≥ ∑ i in Finset.range 11, (k + i) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (show Finset.range 11 ⊆ Finset.range m by
              intro i hi
              simp at hi ⊢
              omega
            )
            intro i hi
            simp
          have h6 : ∑ i in Finset.range 11, (k + i) ≥ 55 := by
            norm_num [Finset.sum_range_succ]
            all_goals omega
          linarith
        linarith
      interval_cases m <;> try { 
        norm_num [Finset.sum_range_succ] at heq
        all_goals
          omega
      }
      all_goals try tauto
    · -- Second direction: if m = 2, 5, or 7, then m is in the set.
      rintro (rfl | rfl | rfl)
      · -- m=2
        use 17
        all_goals
          native_decide
      · -- m=5
        use 5
        all_goals
          native_decide
      · -- m=7
        use 2
        all_goals
          native_decide
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> try rfl