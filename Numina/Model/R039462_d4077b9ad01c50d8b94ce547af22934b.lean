import Mathlib

theorem number_theory_246413 (n : ℕ) :
    16 ∣ 12 * n ^ 2 + 8 * n + (-1 : ℤ) ^ n * (9 + (-1 : ℤ) ^ n * 7) * 2 := by
  have h1 : ∀ n : ℕ, (12 * n ^ 2 + 8 * n + (-1 : ℤ) ^ n * (9 + (-1 : ℤ) ^ n * 7) * 2 : ℤ) % 16 = 0 := by
    intro n
    have h2 : (12 * n ^ 2 + 8 * n + (-1 : ℤ) ^ n * (9 + (-1 : ℤ) ^ n * 7) * 2 : ℤ) % 16 = 0 := by
      have h3 : n % 2 = 0 ∨ n % 2 = 1 := by
        omega
      rcases h3 with (h3 | h3)
      · -- n is even
        have h4 : (-1 : ℤ) ^ n = 1 := by
          have h5 : n % 2 = 0 := h3
          have h8 : ∀ k : ℕ, (-1 : ℤ) ^ (2 * k) = 1 := by
            intro k
            induction k with
            | zero => norm_num
            | succ k ih =>
              simp [pow_add, pow_mul, pow_two] at ih ⊢
              all_goals omega
          have h10 : ∃ k, n = 2 * k := by
            refine ⟨n / 2, by omega⟩
          rcases h10 with ⟨k, hk⟩
          rw [hk]
          apply h8 k
        rw [h4]
        have h10 : ((12 * n ^ 2 + 8 * n + (1 : ℤ) * (9 + (1 : ℤ) * 7) * 2 : ℤ) ) % 16 = 0 := by
          have h7 : (n : ℤ) % 2 = 0 := by
            omega
          have h8 : ∃ k : ℕ, n = 2 * k := by
            refine ⟨n / 2, by omega⟩
          rcases h8 with ⟨k, hk⟩
          rw [show (n : ℤ) = 2 * (k : ℤ) by exact_mod_cast hk]
          ring_nf
          omega
        omega
      · -- n is odd
        have h4 : (-1 : ℤ) ^ n = -1 := by
          have h5 : n % 2 = 1 := h3
          have h8 : ∀ k : ℕ, (-1 : ℤ) ^ (2 * k + 1) = -1 := by
            intro k
            induction k with
            | zero => norm_num
            | succ k ih =>
              simp [pow_add, pow_mul, pow_two] at ih ⊢
              all_goals omega
          have h10 : ∃ k, n = 2 * k + 1 := by
            refine ⟨(n - 1) / 2, by omega⟩
          rcases h10 with ⟨k, hk⟩
          rw [hk]
          apply h8 k
        rw [h4]
        have h10 : ((12 * n ^ 2 + 8 * n + (-1 : ℤ) * (9 + (-1 : ℤ) * 7) * 2 : ℤ) ) % 16 = 0 := by
          have h7 : (n : ℤ) % 2 = 1 := by
            omega
          have h8 : ∃ k : ℕ, n = 2 * k + 1 := by
            refine ⟨(n - 1) / 2, by omega⟩
          rcases h8 with ⟨k, hk⟩
          rw [show (n : ℤ) = 2 * (k : ℤ) + 1 by exact_mod_cast hk]
          ring_nf
          omega
        omega
    omega
  have h0 : (12 * n ^ 2 + 8 * n + (-1 : ℤ) ^ n * (9 + (-1 : ℤ) ^ n * 7) * 2 : ℤ) % 16 = 0 := by
    apply h1 n
  exact Int.dvd_of_emod_eq_zero h0