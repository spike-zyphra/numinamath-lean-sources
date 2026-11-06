import Mathlib

theorem number_theory_122631 (n : ℕ) :
    Nat.Prime (3^(2*n) - 2^n) ↔ n = 1 := by
  constructor
  · -- Forward direction: If it's prime, then n = 1
    intro h
    by_cases h1 : n > 1
    · -- Case where n > 1
      have h2 : n ≥ 2 := by omega
      have h3 : 3 ^ (2 * n) % 7 = 2 ^ n % 7 := by
        have h4 : ∀ k : ℕ, (3 ^ (2 * k) : ℕ) % 7 = (2 ^ k : ℕ) % 7 := by
          intro k
          induction k with
          | zero =>
            simp
          | succ k ih =>
            simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
            all_goals omega
        specialize h4 n
        simpa using h4
      have h4 : (3 ^ (2 * n) - 2 ^ n) % 7 = 0 := by
        have h7 : (3 ^ (2 * n) ) % 7 = (2 ^ n ) % 7 := h3
        have h8 : (3 ^ (2 * n) : ℕ) ≥ (2 ^ n : ℕ) := by
          have h9 : ∀ m : ℕ, 3 ^ (2 * m) ≥ 2 ^ m := by
            intro m
            induction m with
            | zero =>
              all_goals norm_num
            | succ m ih =>
              simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
              all_goals
                nlinarith [show 3 ^ (2 * m) ≥ 0 from by positivity, show 2 ^ m ≥ 0 from by positivity]
          specialize h9 n
          linarith
        omega
      have h7 : (3 ^ (2 * n) - 2 ^ n) % 7 = 0 := h4
      have h9 : 3 ^ (2 * n) - 2 ^ n > 7 := by
        have h10 : ∀ k : ℕ, k ≥ 2 → 3 ^ (2 * k) - 2 ^ k > 7 := by
          intro k hk
          have base : 3 ^ (2 * 2) - 2 ^ 2 > 7 := by
            norm_num
          have step : ∀ (k : ℕ), k ≥ 2 → 3 ^ (2 * k) - 2 ^ k > 7 →
                      3 ^ (2 * (k + 1)) - 2 ^ (k + 1) > 7 := by
            intros k' hk' h'
            have h11 : 3 ^ (2 * (k' + 1)) = 9 * (3 ^ (2 * k')) := by 
              ring_nf
            have h12 : 2 ^ (k' + 1) = 2 * (2 ^ k') := by 
              ring_nf
            rw [h11, h12]
            have h13 : 9 * (3 ^ (2 * k')) > 7 + 2 * (2 ^ k') := by 
              have h14 : 3 ^ (2 * k') - 2 ^ k' > 7 := h'
              omega
            omega
          exact Nat.le_induction base step k hk
        specialize h10 n (by omega)
        simpa using h10
      have h10 : ¬ Nat.Prime (3 ^ (2 * n) - 2 ^ n) := by
        apply Nat.not_prime_of_dvd_of_lt (show 7 ∣ (3 ^ (2 * n) - 2 ^ n) by omega)
        all_goals 
          omega
        all_goals 
          omega
      contradiction
    · -- n ≤ 1
      have h2 : n = 0 ∨ n = 1 := by omega
      rcases h2 with (h2 | h2)
      · -- n = 0
        rw [show n = 0 by omega] at h
        norm_num at h ⊢
        all_goals tauto
      · -- n = 1
        omega
  · -- Backward direction: If n = 1, then it's prime
    intro h
    rw [h]
    norm_num