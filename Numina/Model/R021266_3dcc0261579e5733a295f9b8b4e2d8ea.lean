import Mathlib

theorem number_theory_236788 (p : ℕ) (hp : Nat.Prime p) (h : 7 ≤ p) : 240 ∣ p ^ 4 - 1 := by 
  have h1 : p % 2 ≠ 0 := by
    by_contra h1
    have : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals omega
    contradiction

  have h2 : p % 3 ≠ 0 := by
    by_contra h2
    have : 3 ∣ p := by omega
    have h3 : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
      all_goals omega
    contradiction

  have h3 : p % 5 ≠ 0 := by
    by_contra h3
    have : 5 ∣ p := by omega
    have h4 : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega)
      all_goals omega
    contradiction
  
  have h4 : (p ^ 4) % 16 = 1 := by
    have h5 : p % 2 ≠ 0 := h1
    have h7 : p % 16 = 1 ∨ p % 16 = 3 ∨ p % 16 = 5 ∨ p % 16 = 7 ∨ p % 16 = 9 ∨ p % 16 = 11 ∨ p % 16 = 13 ∨ p % 16 = 15 := by
      omega
    rcases h7 with (h | h | h | h | h | h | h | h)
    · -- p ≡ 1 [MOD 16]
      simp [h, Nat.pow_mod]
    · -- p ≡ 3 [MOD 16]
      simp [h, Nat.pow_mod]
    · -- p ≡ 5 [MOD 16]
      simp [h, Nat.pow_mod]
    · -- p ≡ 7 [MOD 16]
      simp [h, Nat.pow_mod]
    · -- p ≡ 9 [MOD 16]
      simp [h, Nat.pow_mod]
    · -- p ≡ 11 [MOD 16]
      simp [h, Nat.pow_mod]
    · -- p ≡ 13 [MOD 16]
      simp [h, Nat.pow_mod]
    · -- p ≡ 15 [MOD 16]
      simp [h, Nat.pow_mod]

  have h5 : (p ^ 4) % 3 = 1 := by
    have h10 : p % 3 = 1 ∨ p % 3 = 2 := by
      omega
    rcases h10 with (h11 | h11)
    · -- p ≡ 1 [MOD 3]
      simp [h11, Nat.pow_mod]
    · -- p ≡ 2 [MOD 3]
      simp [h11, Nat.pow_mod]

  have h6 : (p ^ 4) % 5 = 1 := by
    have h15 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
      omega
    rcases h15 with (h16 | h16 | h16 | h16)
    · -- p ≡ 1 [MOD 5]
      simp [h16, Nat.pow_mod]
    · -- p ≡ 2 [MOD 5]
      simp [h16, Nat.pow_mod]
    · -- p ≡ 3 [MOD 5]
      simp [h16, Nat.pow_mod]
    · -- p ≡ 4 [MOD 5]
      simp [h16, Nat.pow_mod]

  -- Now, using the Chinese Remainder Theorem
  have h8 : (p ^ 4) % 240 = 1 := by
    omega
  exact Nat.dvd_of_mod_eq_zero (by omega)