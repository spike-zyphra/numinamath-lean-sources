import Mathlib

theorem number_theory_291956 :
    Set.ncard {k : ℕ | k ∈ Finset.Icc 1 10000 ∧ (k % 10 = 1) ∧ ∃ m n, k = 8 ^ m + 5 ^ n} = 5 := by
  have h1 : {k : ℕ | k ∈ Finset.Icc 1 10000 ∧ (k % 10 = 1) ∧ ∃ m n, k = 8 ^ m + 5 ^ n} = 
      {4101, 4121, 4221, 4721, 7221} := by 
    ext k 
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, 
      Set.mem_singleton_iff, and_imp]
    constructor 
    · -- Assume k is in our set 
      rintro ⟨⟨hk1, hk2⟩, h1, ⟨m, n, h2⟩⟩
      have h3 : m < 5 := by 
        by_contra h 
        push_neg at h 
        have h4 : 8 ^ m ≥ 8 ^ 5 := by 
          have h5 : m ≥ 5 := by omega 
          have h6 : 8 ^ m ≥ 8 ^ 5 := by 
            apply Nat.pow_le_pow_of_le_right 
            all_goals norm_num 
            all_goals omega 
          linarith 
        have h5 : 8 ^ m ≥ 32768 := by
          have h7 : 8 ^ 5 = 32768 := by norm_num
          linarith [h4, h7]
        have h7 : k > 10000 := by 
          nlinarith [h2, show 5 ^ n ≥ 0 by positivity, h5] 
        linarith [show k ≤ 10000 by linarith [hk2], h7] 
      have h4 : n < 6 := by 
        by_contra h 
        push_neg at h 
        have h5 : 5 ^ n ≥ 5 ^ 6 := by 
          have h6 : n ≥ 6 := by omega 
          have h7 : 5 ^ n ≥ 5 ^ 6 := by 
            apply Nat.pow_le_pow_of_le_right 
            all_goals norm_num 
            all_goals omega 
          linarith 
        have h6 : 5 ^ n ≥ 15625 := by
          have h8 : 5 ^ 6 = 15625 := by norm_num 
          linarith [h5, h8] 
        -- $k =8^m+5^n$ >0 to contradict
        have h7 : k > 10000 := by 
          nlinarith [h2, show 8 ^ m ≥ 0 by positivity, h6] 
        linarith [show k ≤ 10000 by linarith [hk2], h7] 
      interval_cases n <;> interval_cases m 
      <;> norm_num at h2 
      <;> omega 
      all_goals omega 
    · -- Show k is in our set 
      rintro (rfl | rfl | rfl | rfl | rfl) 
      · -- k =4101 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · use 4, 1 
          all_goals norm_num 
      · -- k =4121 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · use 4, 2 
          all_goals norm_num 
      · -- k =4221 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · use 4, 3 
          all_goals norm_num 
      · -- k =4721 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · use 4, 4 
          all_goals norm_num 
      · -- k =7221 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · use 4, 5 
          all_goals norm_num 
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp