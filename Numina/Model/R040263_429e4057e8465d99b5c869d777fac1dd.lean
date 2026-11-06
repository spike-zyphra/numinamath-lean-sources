import Mathlib

theorem number_theory_159666 (p : ℕ) (hp : p.Prime) :
    (2^p + p^2).Prime ↔ p = 3 := by 
  constructor 
  · -- Assume $2^p + p^2$ is prime, prove $p = 3$
    intro h
    by_cases h1 : p > 3
    · -- p > 3 
      -- We need to show that $2^p + p^2$ is not prime. We'll show it's divisible by 3.
      -- First, show p must be 1 or 2 mod 3
      have h3 : p % 2 = 1 := by 
        by_contra h4
        push_neg at h4 
        have h4' : p % 2 = 0 := by 
          omega 
        have h5 : ¬p.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) 
          all_goals 
            omega 
        contradiction 
      -- Now, either p ≡ 1 or 2 (mod 3)
      have h4 : p % 3 = 1 ∨ p % 3 = 2 := by
        by_contra h 
        push_neg at h 
        have h3 : p % 3 = 0 := by 
          omega 
        have h4 : ¬p.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) 
          all_goals 
            omega 
        contradiction 
      -- Now, we can compute 2^p + p^2 modulo 3
      -- First, prove that 2^p ≡ 2 (mod 3). Since p is odd, let p = 2k+1.
      -- Then 2^p = 2^(2k+1) = 4^k * 2 ≡ 1^k * 2 ≡ 2 (mod 3).
      have h8 : (2 ^ p) % 3 = 2 := by
        have h9 : p % 2 = 1 := h3 
        have h11 : ∀ (k : ℕ), (2 ^ (2 * k + 1) : ℕ) % 3 = 2 := by 
          intro k 
          induction k with 
          | zero => 
            norm_num 
          | succ k ih => 
            calc
              (2 ^ (2 * (k + 1) + 1) : ℕ) % 3 = (2 ^ (2 * k + 1 + 2) : ℕ) % 3 := by ring_nf 
              _ = (2 ^ (2 * k + 1) * 2 ^ 2) % 3 := by rw [pow_add]
              _ = ((2 ^ (2 * k + 1) % 3) * (2 ^ 2 % 3)) % 3 := by 
                simp [Nat.mul_mod] 
              _ = (2 * (2 ^ 2 % 3)) % 3 := by 
                rw [ih] 
              _ = (2 * 4 % 3) % 3 := by 
                norm_num 
              _ = (2 * 1) % 3 := by 
                norm_num 
              _ = 2 % 3 := by 
                norm_num 
              _ = 2 := by 
                norm_num 
        -- There exists k such that p = 2k+1 
        have h12 : ∃ (k : ℕ), p = 2 * k + 1 := by 
          refine' ⟨(p - 1) / 2, by omega⟩ 
        rcases h12 with ⟨k, hk⟩ 
        rw [hk] 
        have h11' : (2 ^ (2 * k + 1) : ℕ) % 3 = 2 := h11 k 
        omega 
      -- Second, compute p^2 mod 3. For either p ≡ 1 or 2 (mod 3), p^2 ≡ 1 (mod 3).
      have h9 : (p ^ 2) % 3 = 1 := by
        rcases h4 with (h6 | h6)
        · 
          have h7 : p % 3 = 1 := h6 
          simp [Nat.pow_mod, h7] 
        · 
          have h7 : p % 3 = 2 := h6 
          simp [Nat.pow_mod, h7] 
      -- Now, the sum is 0 mod 3
      have h10 : ((2 ^ p + p ^ 2) ) % 3 = 0 := by 
        omega 
      have h11 : ¬ (2^p + p^2).Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ 2^p + p^2 by omega) 
        all_goals 
          have h33 : 2 ^ p + p ^ 2 > 3 := by
            have hp2 : p > 3 := h1 
            have h6 : 2 ^ p > 8 := by 
              have : p ≥ 4 := by linarith 
              have h11 : 2 ^ p ≥ 2 ^ 4 := by 
                apply Nat.pow_le_pow_of_le_right (by norm_num) this 
              norm_num at h11 ⊢ 
              linarith 
            nlinarith [show p^2 ≥ 16 by nlinarith, h6] 
          nlinarith 
      contradiction 
    · -- p ≤ 3 
      have h2 : p = 2 ∨ p = 3 := by 
        interval_cases p <;> norm_num at hp ⊢ <;> tauto 
      rcases h2 with (h2 | h2)
      · -- p = 2 
        rw [h2] at h 
        norm_num at h 
      · -- p = 3 
        tauto 
  · -- Assume p = 3 prove (2^p + p^2).Prime 
    intro h
    rw [h]
    norm_num 
    all_goals norm_num