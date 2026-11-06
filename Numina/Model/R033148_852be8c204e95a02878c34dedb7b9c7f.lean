import Mathlib

theorem algebra_15755 : Set.ncard {n : ℕ | n.Prime ∧ (Nat.digits 10 n).length = 2 ∧ (Nat.digits 10 n).Nodup ∧ (Nat.digits 10 n).toFinset ⊆ {2, 7, 8, 9}} = 4 := by
  have h1 : {n : ℕ | n.Prime ∧ (Nat.digits 10 n).length = 2 ∧ (Nat.digits 10 n).Nodup ∧ (Nat.digits 10 n).toFinset ⊆ {2, 7, 8, 9}} = {29, 79, 89, 97} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n is in the left side set
      rintro ⟨h_prime, h_len, h_nodup, h_subset⟩
      have h2 : n ≥ 10 := by
        by_contra h
        push_neg at h
        interval_cases n <;> norm_num at h_len h_prime h_nodup h_subset ⊢ <;> try { contradiction }
      have h3 : n ≤ 99 := by
        by_contra h
        push_neg at h
        have h4 : (Nat.digits 10 n).length > 2 := by
          have h5 : (Nat.digits 10 n).length = Nat.log 10 n + 1 := by
            rw [Nat.digits_len]
            all_goals omega
          rw [h5] at *
          have h6 : Nat.log 10 n ≥ 2 := by
            have h7 : 10 ^ 2 ≤ n := by linarith
            have h8 : Nat.log 10 n ≥ 2 := by
              apply Nat.le_log_of_pow_le (by norm_num) h7
            linarith
          omega
        omega
      interval_cases n <;> norm_num at h_prime h_len h_nodup h_subset ⊢ <;> try { tauto }
    · -- Assume n is in the right side set
      rintro (rfl | rfl | rfl | rfl)
      · -- Check 29
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · native_decide
        · native_decide
      · -- Check 79
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · native_decide
        · native_decide
      · -- Check 89
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · native_decide
        · native_decide
      · -- Check 97
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · native_decide
        · native_decide
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]