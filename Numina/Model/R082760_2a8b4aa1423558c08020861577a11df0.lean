import Mathlib

theorem number_theory_177094 (n : ℕ) (hn : n > 0) :
    30 ∣ n^19 - n^7 := by
  have h1 : n ^ 19 % 2 = n ^ 7 % 2 := by
    have h2 : n % 2 = 0 ∨ n % 2 = 1 := by
      omega
    rcases h2 with (h2 | h2)
    · -- n is even
      simp [Nat.pow_mod, h2]
    · -- n is odd
      simp [Nat.pow_mod, h2]

  have h3 : n ^ 19 % 3 = n ^ 7 % 3 := by
    have h4 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h4 with (h4 | h4 | h4)
    · -- n ≡ 0 (mod 3)
      simp [Nat.pow_mod, h4]
    · -- n ≡ 1 (mod 3)
      simp [Nat.pow_mod, h4]
    · -- n ≡ 2 (mod 3)
      simp [Nat.pow_mod, h4]

  have h5 : n ^ 19 % 5 = n ^ 7 % 5 := by
    have h6 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
      omega
    rcases h6 with (h6 | h6 | h6 | h6 | h6)
    · -- n ≡ 0 (mod 5)
      simp [Nat.pow_mod, h6]
    · -- n ≡ 1 (mod 5)
      simp [Nat.pow_mod, h6]
    · -- n ≡ 2 (mod 5)
      simp [Nat.pow_mod, h6]
    · -- n ≡ 3 (mod 5)
      simp [Nat.pow_mod, h6]
    · -- n ≡ 4 (mod 5)
      simp [Nat.pow_mod, h6]

  have h6 : 2 ∣ n ^ 19 - n ^ 7 := by
    omega

  have h7 : 3 ∣ n ^ 19 - n ^ 7 := by
    omega

  have h8 : 5 ∣ n ^ 19 - n ^ 7 := by
    omega

  have h9 : 30 ∣ n ^ 19 - n ^ 7 := by
    omega
  exact h9