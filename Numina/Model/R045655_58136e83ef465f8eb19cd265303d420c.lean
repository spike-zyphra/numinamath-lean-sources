import Mathlib

open Nat

theorem number_theory_241242 :
    {n : ℕ | 0 < n ∧ ((n.Prime ∧ (4^n + 1).Prime) ∨
    (n.Prime ∧ (n^2 + 2).Prime) ∨
    ((4^n + 1).Prime ∧ (n^2 + 2).Prime))} = {1, 2, 3} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
    Set.union_singleton]
  constructor
  · -- Assume n ∈ left side, prove n ∈ {1, 2, 3}
    intro h
    rcases h with ⟨hn_pos, h⟩
    rcases h with (h | h | h)
    · -- Case where n and 4^n + 1 are prime
      rcases h with ⟨h_n_prime, h_4n1_prime⟩
      by_cases h1 : n ≤ 3
      · -- n ≤ 3
        interval_cases n <;> norm_num at h_n_prime h_4n1_prime hn_pos ⊢
      · -- n > 3
        have h2 : n > 3 := by linarith
        have h3 : n % 2 = 1 := by
          by_contra h3
          push_neg at h3
          have h4 : n % 2 = 0 := by omega
          have h5 : ¬ n.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ n by omega) (by omega) (by omega)
          contradiction
        have h4 : (4 ^ n + 1) % 5 = 0 := by
          have h5 : ∀ k : ℕ, (4 ^ (2 * k + 1) + 1) % 5 = 0 := by
            intro k
            induction k with
            | zero =>
              norm_num
            | succ k ih =>
              simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
              all_goals
                omega
          have h6 : ∃ k : ℕ, n = 2 * k + 1 := by
            use (n - 1) / 2
            omega
          rcases h6 with ⟨k, hk⟩
          rw [show n = 2 * k + 1 by linarith [hk]]
          apply h5 k
        have h6 : (4 ^ n + 1) % 5 = 0 := h4
        have h7 : (4 ^ n + 1) > 5 := by
          have h7 : n ≥ 4 := by omega
          have h8 : 4 ^ n ≥ 256 := by
            have h4 : n ≥ 4 := by omega
            have h5 : 4 ^ 4 = 256 := by norm_num
            have h6 : 4 ^ n ≥ 4 ^ 4 := by
              apply Nat.pow_le_pow_of_le_right
              · norm_num
              · linarith
            linarith
          linarith
        have h8 : ¬ (4 ^ n + 1).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (4 ^ n + 1) by omega) (by omega) (by omega)
        contradiction
    · -- Case where n and n^2 + 2 are prime
      rcases h with ⟨h_n_prime, h_n22_prime⟩
      by_cases h1 : n ≤ 3
      · -- n ≤ 3
        interval_cases n <;> norm_num at h_n_prime h_n22_prime hn_pos ⊢
      · -- n > 3
        have h2 : n > 3 := by linarith
        have h3 : n % 3 = 1 ∨ n % 3 = 2 := by
          by_contra h3
          push_neg at h3
          have h4 : n % 3 = 0 := by omega
          have h5 : 3 ∣ n := by omega
          have h6 : n > 3 := by omega
          have h7 : ¬ n.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ n by omega) (by omega) (by omega)
          contradiction
        rcases h3 with (h3 | h3)
        · -- n % 3 = 1
          have h4 : (n ^ 2 + 2) % 3 = 0 := by
            simp [Nat.pow_mod, Nat.add_mod, h3]
          have h5 : n ^ 2 + 2 > 3 := by
            nlinarith [show n ≥ 4 by omega]
          have h6 : ¬ (n ^ 2 + 2).Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (n ^ 2 + 2) by omega) (by omega) (by omega)
          contradiction
        · -- n % 3 = 2
          have h4 : (n ^ 2 + 2) % 3 = 0 := by
            simp [Nat.pow_mod, Nat.add_mod, h3]
          have h5 : n ^ 2 + 2 > 3 := by
            nlinarith [show n ≥ 4 by omega]
          have h6 : ¬ (n ^ 2 + 2).Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (n ^ 2 + 2) by omega) (by omega) (by omega)
          contradiction
    · -- Case where 4^n + 1 and n^2 + 2 are prime
      rcases h with ⟨h_4n1_prime, h_n22_prime⟩
      by_cases h1 : n ≤ 3
      · -- n ≤ 3
        interval_cases n <;> norm_num at h_4n1_prime h_n22_prime hn_pos ⊢
      · -- n > 3
        have h2 : n > 3 := by linarith
        have h3 : n % 2 = 0 := by
          by_contra h3
          push_neg at h3
          have h4 : n % 2 = 1 := by omega
          have h5 : (4 ^ n + 1) % 5 = 0 := by
            have h6 : ∀ k : ℕ, (4 ^ (2 * k + 1) + 1) % 5 = 0 := by
              intro k
              induction k with
              | zero =>
                norm_num
              | succ k ih =>
                simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
                all_goals
                  omega
            have h7 : ∃ k : ℕ, n = 2 * k + 1 := by
              use (n - 1) / 2
              omega
            rcases h7 with ⟨k, hk⟩
            rw [show n = 2 * k + 1 by linarith [hk]]
            apply h6 k
          have h6 : (4 ^ n + 1) % 5 = 0 := h5
          have h7 : (4 ^ n + 1) > 5 := by
            have h7 : n ≥ 4 := by omega
            have h8 : 4 ^ n ≥ 256 := by
              have h4 : n ≥ 4 := by omega
              have h5 : 4 ^ 4 = 256 := by norm_num
              have h6 : 4 ^ n ≥ 4 ^ 4 := by
                apply Nat.pow_le_pow_of_le_right
                · norm_num
                · linarith
              linarith
            linarith
          have h8 : ¬ (4 ^ n + 1).Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (4 ^ n + 1) by omega) (by omega) (by omega)
          contradiction
        -- Now n is even
        have h4 : n % 2 = 0 := h3
        have h5 : (n ^ 2 + 2) % 2 = 0 := by
          have h7 : n % 2 = 0 := h4
          simp [Nat.pow_mod, Nat.add_mod, h7]
        have h6 : n ^ 2 + 2 > 2 := by
          nlinarith [show n ≥ 4 by omega]
        have h7 : ¬ (n ^ 2 + 2).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (n ^ 2 + 2) by omega) (by omega) (by omega)
        contradiction
  · -- Assume n ∈ {1, 2, 3}, prove n ∈ left side
    rintro (rfl | rfl | rfl)
    · -- n = 1
      constructor
      · norm_num
      · -- Show the disjunction
        right
        right
        constructor
        · norm_num
        · norm_num
    · -- n = 2
      constructor
      · norm_num
      · -- Show the disjunction
        left
        constructor
        · norm_num
        · norm_num
    · -- n = 3
      constructor
      · norm_num
      · -- Show the disjunction
        right
        left
        constructor
        · norm_num
        · norm_num