import Mathlib

theorem algebra_16448 :
    Set.ncard {n : ℕ | n.Prime ∧ (Nat.digits 10 n).length = 2 ∧ (Nat.digits 10 n).sum = 8} = 3 := by 
  have h1 : {n : ℕ | n.Prime ∧ (Nat.digits 10 n).length = 2 ∧ (Nat.digits 10 n).sum = 8} = {17, 53, 71} := by
    ext n 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor 
    · -- Forward 
      intro h
      rcases h with ⟨h_prime, h1, h2⟩ 
      have h21 : n ≥ 10 := by 
        by_contra h 
        push_neg at h 
        interval_cases n <;> norm_num at h1 h <;> try { contradiction } <;> tauto 
      by_cases h3 : n ≤ 99 
      · -- Use interval_cases
        interval_cases n <;> norm_num at h_prime h1 h2 ⊢ <;> try { contradiction }
        <;> tauto 
      · -- n > 99 
        have h31 : n > 99 := by 
          omega 
        have h32 : (Nat.digits 10 n).length > 2 := by
          have h41 : n > 99 := by linarith
          have h5 : n >= 100 := by linarith
          have h42 : (Nat.digits 10 n).length > 2 := by
            have h71 : Nat.log 10 n >= 2 := by
              have : 10 ^ 2 ≤ n := by linarith
              exact Nat.le_log_of_pow_le (by norm_num) this
            have h61 : (Nat.digits 10 n).length = Nat.log 10 n + 1 := by
              rw [Nat.digits_len]
              all_goals 
                omega 
            omega 
          omega
        exfalso 
        omega 
    · -- Backward 
      rintro (rfl | rfl | rfl)
      · constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num 
      · constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num 
      · constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num 
  rw [h1] 
  norm_num 
  <;> try { native_decide }