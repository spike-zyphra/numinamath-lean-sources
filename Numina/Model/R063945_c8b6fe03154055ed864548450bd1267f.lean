import Mathlib

theorem number_theory_119043 (n : ℕ) : 10 ∣ n^65 - n^13 := by

  have h1 : n^65 % 2 = n^13 % 2 := by
    have h1 : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases h1 with (h1 | h1)
    · -- If n is even, then n ≡ 0 [MOD 2]
      simp [Nat.pow_mod, h1]
    · -- If n is odd, then n ≡ 1 [MOD 2]
      simp [Nat.pow_mod, h1]

  have h2 : n^65 % 5 = n^13 % 5 := by
    have h2 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2)
    · -- n ≡ 0 [MOD 5]
      simp [Nat.pow_mod, h2]
    · -- n ≡ 1 [MOD 5]
      simp [Nat.pow_mod, h2]
    · -- n ≡ 2 [MOD 5]
      simp [Nat.pow_mod, h2]
    · -- n ≡ 3 [MOD 5]
      simp [Nat.pow_mod, h2]
    · -- n ≡ 4 [MOD 5]
      simp [Nat.pow_mod, h2]

  have h3 : (n^65 - n^13) % 2 = 0 := by
    omega

  have h4 : (n^65 - n^13) % 5 = 0 := by
    omega

  -- To conclude divisibility by 10, we need (n^65 - n^13) % 10 = 0
  have h5 : (n^65 - n^13) % 10 = 0 := by
    -- Using Chinese Remainder Theorem like logic.
    omega
  exact Nat.dvd_of_mod_eq_zero h5