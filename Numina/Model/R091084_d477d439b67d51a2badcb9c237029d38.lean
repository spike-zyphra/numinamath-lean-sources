import Mathlib

theorem number_theory_318175 {p : ℕ} (hp : Nat.Prime p) (h : 3 < p) :
    p^2 ≡ 1 [MOD 6] := by
  have h1 : p % 2 ≠ 0 := by
    by_contra h2
    have : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
    contradiction
  have h2 : p % 3 ≠ 0 := by
    by_contra h3
    have : 3 ∣ p := by omega
    have : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt this (by omega) (by omega)
    contradiction
  have h3 : p % 2 = 1 := by
    omega
  -- p ≡1,5 mod 6
  have h4 : p % 3 = 1 ∨ p % 3 = 2 := by
    omega
  have h5 : p ^ 2 % 2 = 1 := by
    simp [Nat.pow_mod, h3]
  have h6 : p ^ 2 % 3 = 1 := by
    rcases h4 with (h7 | h7)
    · -- p ≡1 (mod 3)
      simp [Nat.pow_mod, h7]
    · -- p ≡2 (mod 3)
      simp [Nat.pow_mod, h7]
  -- using the Chinese Remainder, since 2 and 3 are co-prime
  -- so we can derive that p^2 ≡1 mod 6
  have h7 : p ^ 2 % 6 = 1 := by
    omega
  show p^2 ≡ 1 [MOD 6]
  exact h7