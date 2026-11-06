import Mathlib

theorem number_theory_265674 :
    {(n, k) : ℕ × ℕ | n > 0 ∧ k ≥ 2 ∧ ∑ i ∈ Finset.range k, (n + i) = 2002}.ncard = 7 := by
  have h1 : {(n, k) : ℕ × ℕ | n > 0 ∧ k ≥ 2 ∧ ∑ i ∈ Finset.range k, (n + i) = 2002} = {(499, 4), (283, 7), (177, 11), (148, 13), (58, 28), (24, 44), (13, 52)} := by
    ext ⟨n, k⟩
    simp
    constructor
    · -- Assume ⟨n, k⟩ is in the left side set
      rintro ⟨hn, hk, heq⟩
      have h2 : k ≤ 90 := by
        by_contra h
        push_neg at h
        have h3 : ∑ i ∈ Finset.range k, (n + i) > 2002 := by
          have h4 : k ≥ 91 := by linarith
          have h5 : n ≥ 1 := by linarith
          have h6 : ∑ i ∈ Finset.range k, (n + i) ≥ ∑ i ∈ Finset.range 91, (n + i) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · -- Show that range 91 is a subset of range k
              intro i hi
              simp at hi ⊢
              omega
            · -- Show that each term (n + i) is ≤ (n + i)
              intro i hi
              simp
          have h7 : ∑ i ∈ Finset.range 91, (n + i) ≥ 2003 := by
            norm_num [Finset.sum_range_succ] at *
            all_goals omega
          linarith
        linarith
      interval_cases k <;> norm_num [Finset.sum_range_succ] at heq ⊢
      <;> omega
    · -- Assume ⟨n, k⟩ is in the right side set
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Finset.sum_range_succ]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { linarith }