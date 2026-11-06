import Mathlib

theorem number_theory_4128 :
    ∑ᶠ n ∈ {n : ℕ | n > 0 ∧ (Nat.digits 10 (n ^ 3)).length = 3}, n = 35 := by
  have h1 : {n : ℕ | n > 0 ∧ (Nat.digits 10 (n ^ 3)).length = 3} = {5, 6, 7, 8, 9} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume n in {n | n > 0 ∧ (Nat.digits 10 (n ^ 3)).length = 3}, show n in {5,6,7,8,9}
      intro h
      rcases h with ⟨hn_pos, hn_len⟩
      have h2 : n ≤ 9 := by
        by_contra h
        push_neg at h
        have h3 : (n ^ 3) ≥ 1000 := by
          have h3a : n > 9 := h
          have h3b : n ^ 3 ≥ 10 ^ 3 := by
            have : n ≥ 10 := by linarith
            have h4 : n ^ 3 ≥ (10 : ℕ) ^ 3 := by
              apply Nat.pow_le_pow_of_le_left
              linarith
            linarith
          norm_num at h3b ⊢
          linarith
        have h4 : (Nat.digits 10 (n ^ 3)).length > 3 := by
          have h5 : (Nat.digits 10 (n ^ 3)).length = Nat.log 10 (n ^ 3) + 1 := by
            rw [Nat.digits_len]
            all_goals
              omega
          rw [h5]
          have h6 : Nat.log 10 (n ^ 3) ≥ 3 := by
            have h7 : 10 ^ 3 ≤ n ^ 3 := by
              linarith [h3]
            have h8 : Nat.log 10 (n ^ 3) ≥ 3 := by
              apply Nat.le_log_of_pow_le (by linarith)
              linarith
            linarith
          omega
        omega
      have h3 : n ≥ 5 := by
        by_contra h
        push_neg at h
        have h4 : n < 5 := by linarith
        interval_cases n <;> norm_num at hn_pos hn_len <;> norm_num at hn_pos hn_len ⊢
        all_goals omega
      interval_cases n <;> norm_num at hn_pos hn_len ⊢ <;> tauto
    · -- Assume n in {5,6,7,8,9}, show n in {n : ℕ | n > 0 ∧ (Nat.digits 10 (n ^ 3)).length = 3}
      rintro (rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> try { native_decide }
  all_goals try { norm_num }
  <;> tauto