import Mathlib

theorem number_theory_138 (p : ℕ) (hp₀ : Nat.Prime p) (hp₁ : p > 5) :
    (7 * p ^ 4 + 5) % 336 = 12 := by 
  -- Note that 336 = 3 × 7 × 16. We'll check congruences mod 3, 7, and 16
  have hp2 : p % 2 ≠ 0 := by
    by_contra h
    have h1 : p % 2 = 0 := by omega
    have h2 : p > 2 := by linarith
    have h3 : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by linarith) (by linarith)
    contradiction

  have hp3 : p % 3 ≠ 0 := by
    by_contra h
    have h1 : p % 3 = 0 := by omega
    have h2 : p > 3 := by linarith
    have h3 : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by linarith) (by linarith)
    contradiction

  have hp4 : p % 5 ≠ 0 := by
    by_contra h
    have h1 : p % 5 = 0 := by omega
    have h2 : p > 5 := by linarith
    have h3 : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega) (by linarith) (by linarith)
    contradiction

  -- Compute modulo 3
  have h12 : (7 * p ^ 4 + 5) % 3 = 0 := by
    have h1 : p % 3 = 1 ∨ p % 3 = 2 := by 
      omega
    have hp41 : p ^ 4 % 3 = 1 := by
      rcases h1 with (h1 | h1)
      · 
        simp [Nat.pow_mod, h1]
      · 
        simp [Nat.pow_mod, h1]
    omega

  -- Compute modulo 7
  have h53 : (7 * p ^ 4 + 5) % 7 = 5 := by 
    omega

  -- Compute modulo 16
  have h720 : (7 * p ^ 4 + 5) % 16 = 12 := by
    have h120 : p % 2 = 1 := by 
      omega
    -- p is odd, so p^4 ≡ 1 (mod 16)
    have h160 : p ^ 4 % 16 = 1 := by 
      have h161 : p % 16 = 1 ∨ p % 16 = 3 ∨ p % 16 = 5 ∨ p % 16 = 7 ∨ p % 16 = 9 ∨ p % 16 = 11 ∨ p % 16 = 13 ∨ p % 16 = 15 := by 
        have h1200 : p % 2 = 1 := h120
        have : p % 16 = 1 ∨ p % 16 = 3 ∨ p % 16 = 5 ∨ p % 16 = 7 ∨ p % 16 = 9 ∨ p % 16 = 11 ∨ p % 16 = 13 ∨ p % 16 = 15 := by
          omega
        assumption
      rcases h161 with (h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
    omega

  -- Combine results using Chinese Remainder Theorem
  -- We need x ≡ 0 (mod 3), x ≡ 5 (mod 7), x ≡ 12 (mod 16)
  -- Let x = 12. Check:12 ≡ 0 (mod 3)x
  -- Given equations 7p^4 +5 ≡0 (mod 3) and others
  have h94 : (7 * p ^ 4 + 5) % 3 = 0 := h12
  have h95 : (7 * p ^ 4 + 5) % 7 = 5 := h53
  have h96 : (7 * p ^ 4 + 5) % 336 = 12 := by 
    omega
  exact h96