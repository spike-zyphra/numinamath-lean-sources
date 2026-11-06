import Mathlib

theorem number_theory_163354 :
    {(n, k) : ℕ × ℕ | n > 1 ∧ k > 0 ∧ ∑ i ∈ Finset.range n, (k + i) = 2004}.ncard = 3 := by
  have h1 : {(n, k) : ℕ × ℕ | n > 1 ∧ k > 0 ∧ ∑ i ∈ Finset.range n, (k + i) = 2004} = {(3, 667), (8, 247), (24, 72)} := by
    ext ⟨n, k⟩
    simp
    constructor
    · -- Assume ⟨n, k⟩ s.t. n>1, k>0 and \sum_{i \in range n} (k + i) = 2004, show (n,k) is in the finite set
      rintro ⟨hn, hk, heq⟩
      have h2 : n ≤ 63 := by
        by_contra h
        push_neg at h
        have h3 : ∑ i in Finset.range n, (k + i) ≥ ∑ i in Finset.range 64, (k + i) := by
          have h4 : Finset.range 64 ⊆ Finset.range n := by
            intro i hi
            simp at hi ⊢
            omega
          apply Finset.sum_le_sum_of_subset_of_nonneg h4
          · intro i hi
            simp at hi ⊢
        have h4 : ∑ i in Finset.range 64, (k + i) > 2004 := by
          norm_num [Finset.sum_range_succ] at *
          all_goals
            omega
        linarith [h3, h4, heq]
      interval_cases n <;> try { 
        norm_num [Finset.sum_range_succ] at heq ⊢ 
        all_goals 
          omega 
      } 
    · -- Now show that (n,k) being in the finite set also satisfies the constraints
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- first case (3, 667)
        constructor
        · norm_num
        constructor
        · norm_num
        · 
          norm_num [Finset.sum_range_succ]
      · -- second case (8, 247)
        constructor
        · norm_num
        constructor
        · norm_num
        · 
          norm_num [Finset.sum_range_succ]
      · -- third case (24, 72)
        constructor
        · norm_num
        constructor
        · norm_num
        · 
          norm_num [Finset.sum_range_succ]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp