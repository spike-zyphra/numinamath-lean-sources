import Mathlib

theorem number_theory_219972 (n : ℕ) :
    Nat.Prime (2^(2^n) + 5) ↔ n = 0 := by
  constructor
  · -- Assume Nat.Prime (2^(2^n) + 5), prove n = 0
    intro h
    by_cases h1 : n > 0
    · -- Assume n > 0
      have h2 : n ≥ 1 := by omega
      have h3 : n ≥ 1 := h2
      have h4 : ∀ m : ℕ, (2 ^ (2 ^ (m + 1)) : ℕ) % 3 = 1 := by
        intro m
        induction m with
        | zero =>
          norm_num
        | succ m ih =>
          have h1 : (2 ^ (2 ^ (m + 1 + 1)) : ℕ) % 3 = 1 := by
            have h5 : (2 ^ (2 ^ (m + 1 + 1)) : ℕ) = (2 ^ (2 ^ (m + 1))) ^ 2 := by
              ring_nf
            rw [h5]
            simp [Nat.pow_mod, ih]
          exact h1
      have h5 : (2 ^ (2 ^ n) : ℕ) % 3 = 1 := by
        have h6 : ∃ m : ℕ, n = m + 1 := by
          refine ⟨n - 1, by omega⟩
        rcases h6 with ⟨m, hm⟩
        rw [hm]
        have h7 : (2 ^ (2 ^ (m + 1)) : ℕ) % 3 = 1 := by
          apply h4
        exact h7
      have h6 : (2 ^ (2 ^ n) + 5 : ℕ) % 3 = 0 := by
        omega
      have h7 : ¬ Nat.Prime (2 ^ (2 ^ n) + 5) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (2 ^ (2 ^ n) + 5) by omega)
        all_goals
        have h8 : (2 ^ (2 ^ n) + 5 : ℕ) > 3 := by
          have h14 : 2 ^ n ≥ 2 := by
            have h8 : n ≥ 1 := h3
            have h9 : 2 ^ n ≥ 2 ^ 1 := by
              apply Nat.pow_le_pow_of_le_right
              all_goals
                omega
            have h10 : 2 ^ 1 = 2 := by norm_num
            linarith
          have h15 : 2 ^ (2 ^ n) ≥ 4 := by
            have h11 : 2 ^ n ≥ 2 := h14
            have h12 : 2 ^ (2 ^ n) ≥ 2 ^ 2 := by
              apply Nat.pow_le_pow_of_le_right
              all_goals
                omega
            have h13 : 2 ^ 2 = 4 := by norm_num
            linarith
          linarith
        all_goals
          omega
      contradiction
    · -- n ≤ 0, so n = 0
      have h2 : n = 0 := by omega
      tauto
  · -- Assume n = 0, prove Nat.Prime (2^(2^n) + 5)
    intro h
    rw [h]
    norm_num