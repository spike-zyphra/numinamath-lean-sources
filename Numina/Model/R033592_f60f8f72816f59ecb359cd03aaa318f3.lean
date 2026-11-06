import Mathlib

theorem number_theory_101825 (n : ℕ) :
    IsSquare (2^n + 3) ↔ n = 0 := by
  constructor
  · -- Assume $2^n + 3$ is a perfect square, prove $n = 0$.
    intro h
    rcases h with ⟨k, hk⟩
    by_cases h1 : n > 0
    · -- n > 0
      by_cases h2 : n ≥ 2
      · -- n ≥ 2
        have h4 : k ≥ 2 := by
          by_contra h'
          push_neg at h'
          have : k < 2 := by omega
          have k0 : k ≤ 1 := by omega
          interval_cases k <;> simp [pow_succ, pow_zero] at hk
          all_goals
            have h2' : n ≥ 2 := h2
            have h5 : (2 : ℕ) ^ n ≥ 4 := by
              have h6 : n ≥ 2 := h2'
              have h7 : (2 : ℕ) ^ n ≥ (2 : ℕ) ^ 2 := by
                apply Nat.pow_le_pow_of_le_right (by norm_num) h6
              have h8 : (2 : ℕ) ^ 2 = 4 := by norm_num
              linarith [h7, h8]
            omega
        have hk_eq : k ^ 2 = 2^n + 3 := by
          nlinarith
        have h5 : (2 ^ n + 3) % 4 = 3 := by
          have h5 : n ≥ 2 := h2
          have h4_eq : n ≥ 2 := h5
          have : (2 ^ n + 3) % 4 = 3 := by
            have h10 : ∀ (m : ℕ), (2 ^ (m + 2) : ℕ) % 4 = 0 := by
              intro m
              induction m with
              | zero =>
                norm_num
              | succ m ih =>
                ring_nf at ih ⊢
                omega
            have h11 : n ≥ 2 := h4_eq
            have h12 : ∃ m, n = m + 2 := by
              refine ⟨n - 2, by omega⟩
            rcases h12 with ⟨m, hm⟩
            rw [hm] at *
            have h13 : (2 ^ (m + 2) : ℕ) % 4 = 0 := h10 m
            omega
          assumption
        have h8 : k ^ 2 % 4 = 3 := by
          omega
        have h9 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by
          omega
        rcases h9 with (h9 | h9 | h9 | h9)
        · -- k ≡ 0 (mod 4)
          have h0 : k ^ 2 % 4 = 0 := by
            simp [Nat.pow_mod, h9]
          omega
        · -- k ≡ 1 (mod 4)
          have h0 : k ^ 2 % 4 = 1 := by
            simp [Nat.pow_mod, h9]
          omega
        · -- k ≡ 2 (mod 4)
          have h0 : k ^ 2 % 4 = 0 := by
            simp [Nat.pow_mod, h9]
          omega
        · -- k ≡ 3 (mod 4)
          have h0 : k ^ 2 % 4 = 1 := by
            simp [Nat.pow_mod, h9]
          omega
      · -- n < 2
        push_neg at h2
        have h3 : n = 0 ∨ n = 1 := by omega
        rcases h3 with (h3 | h3)
        · -- n = 0
          omega
        · -- n = 1
          rw [h3] at hk
          norm_num at hk
          have h2 : k ≤ 2 := by nlinarith [sq_nonneg (k : ℕ), hk]
          interval_cases k <;> omega
    · -- n ≤ 0
      push_neg at h1
      have h3 : n = 0 := by omega
      tauto
  · -- Assume n = 0, prove $2^n + 3$ is a perfect square.
    intro h
    rw [h]
    native_decide