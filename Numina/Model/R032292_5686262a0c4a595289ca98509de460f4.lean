import Mathlib

theorem number_theory_248746 (n : ℕ) :
    Nat.Prime (2^(2^n) + 5) ↔ n = 0 := by
  constructor
  · -- Assume Nat.Prime (2^(2^n) + 5) prove n = 0
    intro h
    by_cases h1 : n > 0
    · -- Assume n > 0
      have h2 : n ≥ 1 := by linarith
      -- Show that $2^{2^n} + 5$ is divisible by 3
      have h3 : (2 : ℕ) ^ (2 ^ n) % 3 = 1 := by
        have h4 : ∀ k : ℕ, (2 : ℕ) ^ (2 ^ (k + 1)) % 3 = 1 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            have h5 : (2 : ℕ) ^ (2 ^ (k + 2)) = ((2 : ℕ) ^ (2 ^ (k + 1))) ^ 2 := by
              ring_nf
            rw [h5]
            simp [Nat.pow_mod, ih]
        have h5 : ∃ k : ℕ, n = k + 1 := by
          refine ⟨n - 1, by omega⟩
        rcases h5 with ⟨k, hk⟩
        have h6 : n = k + 1 := by linarith
        rw [show n = k + 1 by linarith]
        specialize h4 k
        simpa using h4
      have h8 : ((2 : ℕ) ^ (2 ^ n) + 5) % 3 = 0 := by
        omega
      have h10 : (2 : ℕ) ^ (2 ^ n) + 5 > 3 := by
        have h11 : n ≥ 1 := h2
        have h12 : (2 : ℕ) ^ (2 ^ n) ≥ 4 := by
          have h11 : n ≥ 1 := h11
          have h13 : 2 ^ n ≥ 2 := by
            have h11 : n ≥ 1 := h11
            have h14 : 2 ^ n ≥ 2 ^ 1 := by
              apply Nat.pow_le_pow_of_le_right
              all_goals
                omega
            have h15 : 2 ^ 1 = 2 := by norm_num
            have h16 : 2 ^ n ≥ 2 := by
              omega
            linarith
          have h14 : (2 : ℕ) ^ (2 ^ n) ≥ (2 : ℕ) ^ 2 := by
            have h17 : 2 ^ n ≥ 2 := h13
            have h18 : (2 : ℕ) ^ (2 ^ n) ≥ (2 : ℕ) ^ 2 := by
              apply Nat.pow_le_pow_of_le_right
              all_goals
                omega
            linarith
          have h15 : (2 : ℕ) ^ 2 = 4 := by norm_num
          nlinarith [h14, h15]
        omega
      have h12 : ¬Nat.Prime (2^(2^n) + 5) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (2^(2^n) + 5) by omega)
        all_goals
          omega
      contradiction
    · -- n ≤ 0
      have h2 : n = 0 := by linarith
      tauto
  · -- Assume n = 0 prove Nat.Prime (2^(2^n) + 5)
    intro h
    rw [h]
    norm_num