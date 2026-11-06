import Mathlib

theorem number_theory_289762 :
    {(n, k) : ℕ × ℕ | n > 0 ∧ k > 1 ∧ ∑ i ∈ Finset.range k, (n + i) = 105}.encard = 7 := by 
  have h1 : {(n, k) : ℕ × ℕ | n > 0 ∧ k > 1 ∧ ∑ i ∈ Finset.range k, (n + i) = 105} = {(52, 2), (34, 3), (19, 5), (15, 6), (12, 7), (6, 10), (1, 14)} := by
    ext ⟨n, k⟩
    simp
    constructor
    · -- Forward: prove that if ⟨n, k⟩ in left, then ⟨n, k⟩ in right
      rintro ⟨hn, hk, heq⟩
      have h2 : k ≤ 21 := by
        by_contra h
        push_neg at h
        have h3 : ∑ i in Finset.range k, (n + i) > 105 := by
          have h4 : k ≥ 22 := by 
            omega
          have h5 : ∑ i in Finset.range k, (n + i) ≥ ∑ i in Finset.range 22, (n + i) := by 
            apply Finset.sum_le_sum_of_subset_of_nonneg (show Finset.range 22 ⊆ Finset.range k by intro i hi; simp at hi ⊢; omega)
            intro i hi
            simp
          have h6 : ∑ i in Finset.range 22, (n + i) > 105 := by 
            norm_num [Finset.sum_range_succ] at *
            omega 
          linarith 
        linarith 
      interval_cases k <;> try { 
        norm_num [Finset.sum_range_succ] at heq 
        all_goals 
          omega 
      }
      all_goals 
        simp_all [Finset.sum_range_succ]
    · -- Backward: prove that if ⟨n, k⟩ in right, then ⟨n, k⟩ in left
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check (52, 2)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Finset.sum_range_succ]
      · -- Check (34, 3)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Finset.sum_range_succ]
      · -- Check (19, 5)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Finset.sum_range_succ]
      · -- Check (15, 6)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Finset.sum_range_succ]
      · -- Check (12, 7)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Finset.sum_range_succ]
      · -- Check (6, 10)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Finset.sum_range_succ]
      · -- Check (1, 14)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Finset.sum_range_succ]
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try { native_decide }