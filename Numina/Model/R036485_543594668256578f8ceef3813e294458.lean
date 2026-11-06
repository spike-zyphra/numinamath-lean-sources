import Mathlib

theorem algebra_4558 :
    ∑ᶠ n ∈ {n : ℕ | 0 < n - 3 ∧ (n ^ 3 + 13) % (n - 3) = 0}, n = 114 := by
  have h1 : {n : ℕ | 0 < n - 3 ∧ (n ^ 3 + 13) % (n - 3) = 0} = {4, 5, 7, 8, 11, 13, 23, 43} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Forward direction: If n in the set, then n in {4, 5, 7, 8, 11, 13, 23, 43}
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : n > 3 := by omega
      have h4 : n - 3 ∣ 40 := by
        have h6 : n - 3 ∣ n ^ 3 + 13 := by
          exact Nat.dvd_of_mod_eq_zero h2
        -- Show that n - 3 divides 40 by using polynomial division insight
        have h7 : n - 3 ∣ 40 := by
          have h10 : n - 3 ∣ (n ^ 3 + 13) := h6
          have h11 : n - 3 ∣ ( (n - 3) * (n ^ 2 + 3 * n + 9) ) := by
            use n ^ 2 + 3 * n + 9
            all_goals ring_nf <;> omega
          have h12 : n - 3 ∣ ( (n ^ 3 + 13) - ( (n - 3) * (n ^ 2 + 3 * n + 9) ) ) := by
            apply Nat.dvd_sub' h10 h11
          have h13 : ((n ^ 3 + 13) - ( (n - 3) * (n ^ 2 + 3 * n + 9) ) ) = 40 := by
            cases n with
            | zero => omega
            | succ n =>
              cases n with
              | zero => omega
              | succ n =>
                cases n with
                | zero => omega
                | succ n =>
                  simp [Nat.succ_eq_add_one, Nat.pow_succ, Nat.mul_add]
                  <;> ring_nf <;> omega
          rw [h13] at h12
          exact h12
        exact h7
      have h5 : n - 3 ≤ 40 := by
        exact Nat.le_of_dvd (by omega) h4
      have h6 : n ≤ 43 := by
        omega
      interval_cases n <;> norm_num at h1 h2 h4 ⊢ <;> omega
    · -- Backward direction: If n in {4, 5, 7, 8, 11, 13, 23, 43}, then n in the set
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
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
  rw [finsum_mem_insert, finsum_mem_insert, finsum_mem_insert, finsum_mem_insert, finsum_mem_insert, finsum_mem_insert, finsum_mem_insert, finsum_mem_singleton]
  all_goals norm_num
  <;> try native_decide