import Mathlib

theorem number_theory_95914 :
    {(n, k) : ℕ × ℕ | n > 0 ∧ k > 1 ∧ ∑ i ∈ Finset.range k, (n + i) = 345}.ncard = 7 := by
  have h1 : {(n, k) : ℕ × ℕ | n > 0 ∧ k > 1 ∧ ∑ i ∈ Finset.range k, (n + i) = 345} = 
      {(172, 2), (114, 3), (67, 5), (55, 6), (30, 10), (16, 15), (4, 23)} := by
    ext ⟨n, k⟩
    simp
    constructor 
    · -- Assume (n, k) is in the set, so n > 0, k > 1, and the sum is 345.
      rintro ⟨hn, hk, hsum⟩
      have h2 : k ≤ 32 := by 
        by_contra h 
        push_neg at h 
        have h3 : k ≥ 33 := by omega 
        have eq1 : ∑ i in Finset.range k, (n + i) = k * n + k * (k - 1) / 2 := by 
          have h1 : ∀ k : ℕ, ∑ i in Finset.range k, (n + i) = k * n + k * (k - 1) / 2 := by 
            intro k 
            induction k with 
            | zero => 
              simp 
            | succ k ih => 
              rw [Finset.sum_range_succ, ih] 
              cases k with 
              | zero => 
                all_goals simp 
              | succ k => 
                simp [add_assoc] 
                <;> ring_nf <;> omega 
          specialize h1 k 
          simpa using h1 
        rw [eq1] at hsum 
        have h5 : k * n + k * (k - 1) / 2 > 345 := by 
          have h7 : k ≥ 33 := by omega 
          have hn1 : n ≥ 1 := by omega 
          have h7' : k * n + k * (k - 1) / 2 ≥ 33 * 1 + 33 * 32 / 2 := by 
            have hk2 : k ≥ 33 := by omega 
            have hn2 : n ≥ 1 := by omega 
            have h9 : k * n ≥ 33 * 1 := by nlinarith 
            have h10 : k * (k - 1) / 2 ≥ 33 * 32 / 2 := by 
              have : k - 1 ≥ 32 := by omega 
              have hk3 : k ≥ 33 := by omega 
              have : k * (k - 1) ≥ 33 * 32 := by nlinarith 
              omega 
            omega 
          omega 
        omega 
      interval_cases k <;> norm_num [Finset.sum_range_succ] at hsum ⊢
      <;> omega 
    · -- Show that these pairs indeed satisfy the conditions 
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | 
              ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- First pair (172, 2)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Verify sum 
          norm_num [Finset.sum_range_succ]
      · -- Second pair (114, 3)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Verify sum 
          norm_num [Finset.sum_range_succ]
      · -- Third pair (67, 5)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Verify sum 
          norm_num [Finset.sum_range_succ]
      · -- Fourth pair (55, 6)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Verify sum 
          norm_num [Finset.sum_range_succ]
      · -- Fifth pair (30, 10)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Verify sum 
          norm_num [Finset.sum_range_succ]
      · -- Sixth pair (16, 15)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Verify sum 
          norm_num [Finset.sum_range_succ]
      · -- Seventh pair (4, 23)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Verify sum 
          norm_num [Finset.sum_range_succ]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }