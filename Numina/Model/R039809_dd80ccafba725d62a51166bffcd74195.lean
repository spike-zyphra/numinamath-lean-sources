import Mathlib

theorem number_theory_3116 :
    ∑ᶠ n ∈ {n : ℕ | n > 0 ∧ (n + 4) ∣ (n ^ 4 + 102)}, n = 175 + 354 := by
  have h1 : {n : ℕ | n > 0 ∧ (n + 4) ∣ (n ^ 4 + 102)} = {175, 354} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- First, show that if n is in the set, then n ∈ {175, 354}
      rintro ⟨hn_pos, hdiv⟩
      have h7 : n + 4 ∣ (358 : ℕ) := by
        have h1 : n + 4 ∣ n ^ 4 + 102 := hdiv
        have h2 : n + 4 ∣ (n + 4) * (n ^ 3 - 4 * n ^ 2 + 16 * n - 64 : ℕ) := by
          apply dvd_mul_right
        have h8 : (n + 4 : ℕ) ∣ ((n ^ 4 + 102 : ℕ) - (n + 4) * (n ^ 3 - 4 * n ^ 2 + 16 * n - 64 : ℕ)) := by
          apply Nat.dvd_sub'
          · exact h1
          · exact h2
        have h9 : ((n ^ 4 + 102 : ℕ) - (n + 4) * (n ^ 3 - 4 * n ^ 2 + 16 * n - 64 : ℕ) ) = 358 := by 
          cases n with
          | zero => 
            omega
          | succ n => 
            cases n with
            | zero => 
              omega
            | succ n => 
              cases n with
              | zero => 
                omega
              | succ n => 
                cases n with
                | zero => 
                  omega
                | succ n => 
                  simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_add, Nat.add_mul, Nat.mul_sub]
                  <;> ring_nf
                  <;> omega
        rw [h9] at h8
        exact h8
      have h9 : n + 4 ≤ 358 := by
        by_contra h
        push_neg at h
        have h7' : n + 4 ∣ (358 : ℕ) := h7
        have h11 : n + 4 ≤ 358 := by 
          apply Nat.le_of_dvd (by norm_num) h7'
        omega
      -- We have h9 : n + 4 ≤ 358, which implies n ≤ 354.
      have h9 : n ≤ 354 := by 
        omega
      interval_cases n <;> norm_num at hdiv ⊢ <;> tauto
    · -- Assume n = 175 or 354, prove both conditions.
      rintro (rfl | rfl)
      · -- n = 175
        constructor
        · norm_num
        · norm_num
      · -- n = 354
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num