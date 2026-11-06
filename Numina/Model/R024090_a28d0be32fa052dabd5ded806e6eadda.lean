import Mathlib

theorem number_theory_36847 (S : ℕ → ℕ) (hS : ∀ n, S n = n ^ 2 + 20 * n + 12) :
    ∑ᶠ n ∈ {n | 0 < n ∧ ∃ k, S n = k ^ 2}, n = 16 := by
  have h1 : {n | 0 < n ∧ ∃ k, S n = k ^ 2} = {3, 13} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume h_n
      intro h
      rcases h with ⟨hn_pos, ⟨k, hk⟩⟩
      have h2 : S n = n ^ 2 + 20 * n + 12 := hS n
      rw [h2] at hk
      -- Now we need to convert it to difference of square
      have h3 : n ^ 2 + 20 * n + 12 = k ^ 2 := by
        linarith
      have h4 : k ≤ n + 10 := by
        by_contra h
        push_neg at h
        have h5 : k ≥ n + 11 := by
          omega
        have h6 : k ^ 2 ≥ (n + 11) ^ 2 := by
          have h8 : k ≥ n + 11 := h5
          have h9 : k ^ 2 ≥ (n + 11) ^ 2 := by
            apply Nat.pow_le_pow_left
            all_goals omega
          linarith
        nlinarith [h3]
      have h7 : (n + 10 + k : ℤ) * (n + 10 - k : ℤ) = 88 := by
        have eq1 : (n : ℤ) ^ 2 + 20 * (n : ℤ) + 12 = (k : ℤ) ^ 2 := by
          exact_mod_cast h3
        nlinarith [sq_nonneg ((n + 10 : ℤ) - (k : ℤ)), sq_nonneg ((n + 10 : ℤ) + (k : ℤ))]
      have h8 : (n + 10 + k : ℤ) ∣ 88 := by 
        use (n + 10 - k : ℤ)
        linarith [h7]
      have h9 : (n + 10 + k : ℤ) ≤ 88 := by
        apply Int.le_of_dvd (by norm_num) h8
      have h10 : (n + 10 + k : ℤ) ≥ -88 := by
        have h11 : (- (n + 10 + k : ℤ)) ∣ 88 := by 
          exact Int.neg_dvd.2 h8
        have h12 : - (n + 10 + k : ℤ) ≤ 88 := by
          apply Int.le_of_dvd (by norm_num) h11
        omega
      interval_cases h : (n + 10 + k : ℤ) <;> norm_num at h7 h8 <;> try { 
        omega
      }
      <;> try { 
        have h11 : n ≤ 90 := by
          omega
        interval_cases n <;> omega 
      }
    · -- Show that if n ∈ {3, 13}, then n is in left set
      rintro (rfl | rfl)
      · -- Show that 3 is in left
        constructor
        · norm_num
        · use 9
          all_goals norm_num [hS]
      · -- Show that 13 is in left
        constructor
        · norm_num
        · use 21
          all_goals norm_num [hS]
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num