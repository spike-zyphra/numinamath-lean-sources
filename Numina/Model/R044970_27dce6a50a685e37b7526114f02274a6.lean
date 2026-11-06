import Mathlib

theorem number_theory_164938 (n : ℕ) (h₀ : ∃ k, n = ∑ i ∈ Finset.range k, 2 * 10 ^ i) :
    ∃ a b, a^2 + b^2 = n ↔ n = 2 := by
  rcases h₀ with ⟨k, rfl⟩
  by_cases hk0 : k = 0
  · -- k = 0, sum is 0.
    use 1, 0
    norm_num [hk0, Finset.sum_range_succ]
    <;> try { tauto }
    <;> try { omega }
    all_goals norm_num
  · -- k > 0
    by_cases hk1 : k = 1
    · -- k = 1, sum is 2.
      use 1, 1
      norm_num [hk1, Finset.sum_range_succ]
    · -- k > 1
      use 1, 1
      have h3 : k ≥ 2 := by 
        omega
      have h4 : (∑ i in Finset.range k, 2 * 10 ^ i) > 2 := by
        have h5 : k ≥ 2 := by 
          omega
        have h6 : (∑ i in Finset.range k, 2 * 10 ^ i) ≥ (∑ i in Finset.range 2, 2 * 10 ^ i) := by 
          apply Finset.sum_le_sum_of_subset_of_nonneg 
          · -- Show range 2 is subset of range k 
            intro i hi 
            simp at hi ⊢ 
            omega 
          · -- Show each term is ≤ 
            intro i hi 
            simp at hi ⊢ 
            all_goals omega 
        have h7 : (∑ i in Finset.range 2, 2 * 10 ^ i) = 22 := by 
          norm_num [Finset.sum_range_succ]
        have h8 : (∑ i in Finset.range k, 2 * 10 ^ i) ≥ 22 := by 
          linarith [h7, h6]
        omega
      constructor
      · -- Assume 1^2 + 1^2 = (∑ i ∈ Finset.range k, 2 * 10 ^ i), prove (∑ i ∈ Finset.range k, 2 * 10 ^ i) = 2
        intro h_eq
        omega
      · -- Assume (∑ i ∈ Finset.range k, 2 * 10 ^ i) = 2, prove 1^2 + 1^2 = (∑ i ∈ Finset. k, 2 * 10 ^ i)
        intro h_eq
        omega