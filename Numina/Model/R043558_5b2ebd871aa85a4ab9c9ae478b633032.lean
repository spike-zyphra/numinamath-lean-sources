import Mathlib

theorem number_theory_98861 :
    Set.ncard {k : ℕ | 0 < k ∧ k < 100 ∧ ∀ n : ℕ, 0 < n → 7 ∣ 2 * 3 ^ (6 * n) + k * 2 ^ (3 * n + 1) - 1} = 14 := by 
  have h1 : {k : ℕ | 0 < k ∧ k < 100 ∧ ∀ n : ℕ, 0 < n → 7 ∣ 2 * 3 ^ (6 * n) + k * 2 ^ (3 * n + 1) - 1} = 
          {k : ℕ | 0 < k ∧ k < 100 ∧ k % 7 = 3} := by
    ext k 
    simp only [Set.mem_setOf_eq]
    constructor
    · -- Assume k is in the left side.
      intro h 
      rcases h with ⟨hk1, hk2, hdiv⟩ 
      have hk3 : k % 7 = 3 := by 
        have h2 := hdiv 1 (by norm_num)
        norm_num at h2 
        omega 
      tauto 
    · -- Assume k is in the right side.
      rintro ⟨hk1, hk2, hk3⟩ 
      have hdiv : ∀ n : ℕ, 0 < n → 7 ∣ 2 * 3 ^ (6 * n) + k * 2 ^ (3 * n + 1) - 1 := by
        intro n hn
        have h1 : (3 ^ (6 * n) ) % 7 = 1 := by
          have h5 : ∀ m : ℕ, (3 : ℕ) ^ (6 * m) % 7 = 1 := by
            intro m 
            induction m with 
            | zero => 
              norm_num 
            | succ m ih => 
              simp [pow_succ, pow_mul] at ih ⊢ 
              all_goals 
                omega 
          specialize h5 n 
          simpa using h5 
        have h2 : (2 ^ (3 * n + 1) ) % 7 = 2 := by 
          have h6 : ∀ m : ℕ, (2 : ℕ) ^ (3 * m + 1) % 7 = 2 := by 
            intro m 
            induction m with 
            | zero => 
              norm_num 
            | succ m ih => 
              simp [pow_succ, pow_mul] at ih ⊢ 
              all_goals 
                omega 
          specialize h6 n 
          simpa using h6 
        have h3 : k % 7 = 3 := hk3 
        have h4 : (2 * 3 ^ (6 * n)) % 7 = 2 := by
          simp [Nat.mul_mod, h1]
        have h5 : (k * 2 ^ (3 * n + 1)) % 7 = 6 := by
          have hk3' : k % 7 = 3 := h3
          have h2' : (2 ^ (3 * n + 1)) % 7 = 2 := h2
          simp [Nat.mul_mod, hk3', h2']
        have h6 : (2 * 3 ^ (6 * n) + k * 2 ^ (3 * n + 1) - 1) % 7 = 0 := by 
          omega 
        exact Nat.dvd_of_mod_eq_zero h6 
      tauto 
  rw [h1] 
  have h2 : {k : ℕ | 0 < k ∧ k < 100 ∧ k % 7 = 3} = 
    Finset.filter (fun (k : ℕ) => k % 7 = 3) (Finset.Icc (0 : ℕ) 99) := by 
    ext k 
    simp 
    <;> omega 
  rw [h2] 
  rw [Set.ncard_coe_Finset]
  native_decide