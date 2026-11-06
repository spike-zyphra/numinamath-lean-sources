import Mathlib

theorem number_theory_245593 (p : ℕ) (hp : p.Prime) :
    (2^p + p^2).Prime ↔ p = 3 := by
  constructor
  · -- Assume (2^p + p^2) is prime, prove p = 3
    intro h
    by_cases hp2 : p > 3
    · -- Assume p > 3
      have hp1 : p % 3 = 1 ∨ p % 3 = 2 := by
        by_contra h
        push_neg at h
        have h2 : p % 3 = 0 := by 
          omega
        have h3 : p % 3 = 0 := h2
        have h4 : ¬ p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
        contradiction
      have h51 : p % 2 = 1 := by
        by_contra h
        push_neg at h
        have h2 : p % 2 = 0 := by 
          omega
        have h4 : ¬ p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
        contradiction
      have h53 : (2 ^ p) % 3 = 2 := by
        have hk : p % 2 = 1 := h51
        have h60 : p = 2 * (p / 2) + 1 := by 
          omega 
        rw [h60] 
        have h61 : ∀ k : ℕ, (2 ^ (2 * k + 1)) % 3 = 2 := by 
          intro k
          induction k with
          | zero => 
            simp 
          | succ k ih =>
            simp [pow_succ, pow_mul, pow_add, Nat.mul_mod, Nat.add_mod] at ih ⊢ 
            all_goals omega 
        specialize h61 (p / 2)
        simpa using h61 
      have h54 : (p^2) % 3 = 1 := by
        rcases hp1 with (h | h)
        · -- case p ≡ 1 [MOD 3]
          have h11 : p % 3 = 1 := h 
          have h12 : (p ^ 2 : ℕ) % 3 = 1 := by
            simp [Nat.pow_mod, h11]
          omega 
        · -- case p ≡ 2 [MOD 3]
          have h11 : p % 3 = 2 := h 
          have h12 : (p ^ 2 : ℕ) % 3 = 1 := by
            simp [Nat.pow_mod, h11]
          omega 
      have h20 : (2 ^ p + p ^ 2) % 3 = 0 := by 
        omega
      have h4 : ¬ (2^p + p^2).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (2^p + p^2) by omega) (by
          have h31 : 3 < 2 ^ p + p ^ 2 := by 
            have h51 : p ≥ 4 := by 
              omega 
            have h52 : 2 ^ p ≥ 16 := by 
              have h53 : p ≥ 4 := h51 
              have h54 : 2 ^ p ≥ 2 ^ 4 := by 
                apply Nat.pow_le_pow_of_le_right 
                norm_num 
                omega 
              have : 2 ^ 4 = 16 := by 
                norm_num 
              omega 
            have h56 : p ^ 2 ≥ 16 := by 
              have h57 : p ≥ 4 := h51 
              have h58 : p ^ 2 ≥ (4 : ℕ) ^ 2 := by 
                apply Nat.pow_le_pow_left 
                all_goals linarith 
              have : (4 : ℕ) ^ 2 = 16 := by 
                norm_num 
              omega 
            omega 
          linarith 
        ) (by
          -- nlinarith
          have h100 : p ≥ 1 := by
            exact Nat.Prime.one_le hp 
          have h101 : 2 ^ p + p ^ 2 > 3 := by
            have h51 : p ≥ 4 := by
              omega
            have h52 : 2 ^ p ≥ 16 := by
              have h53 : p ≥ 4 := h51 
              have h54 : 2 ^ p ≥ 2 ^ 4 := by
                apply Nat.pow_le_pow_of_le_right 
                norm_num 
                omega 
              have : 2 ^ 4 = 16 := by
                norm_num 
              omega 
            have h56 : p ^ 2 ≥ 16 := by
              have h57 : p ≥ 4 := h51 
              have h58 : p ^ 2 ≥ (4 : ℕ) ^ 2 := by
                apply Nat.pow_le_pow_left 
                all_goals linarith 
              have : (4 : ℕ) ^ 2 = 16 := by
                norm_num 
              omega 
            omega 
          linarith 
        )
      contradiction 
    · -- Assume p ≤ 3
      interval_cases p <;> norm_num at hp h ⊢
  · -- Assume p = 3
    intro h
    rw [h]
    norm_num