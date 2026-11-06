import Mathlib

theorem number_theory_116256 (n : ℕ) : n^7 ≡ n [MOD 42] := by
  have h1 : n ^ 7 % 2 = n % 2 := by
    have h1 : n % 2 = 0 ∨ n % 2 = 1 := by
      omega
    rcases h1 with (h1 | h1)
    · -- If n % 2 = 0
      simp [Nat.pow_mod, h1]
    · -- If n % 2 = 1
      simp [Nat.pow_mod, h1]
  have h2 : n ^ 7 % 3 = n % 3 := by
    have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h2 with (h2 | h2 | h2)
    · simp [Nat.pow_mod, h2]
    · simp [Nat.pow_mod, h2]
    · simp [Nat.pow_mod, h2]
  have h3 : n ^ 7 % 7 = n % 7 := by
    have h3 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by
      omega
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3)
    · simp [Nat.pow_mod, h3]
    · simp [Nat.pow_mod, h3]
    · simp [Nat.pow_mod, h3]
    · simp [Nat.pow_mod, h3]
    · simp [Nat.pow_mod, h3]
    · simp [Nat.pow_mod, h3]
    · simp [Nat.pow_mod, h3]
  norm_num [Nat.ModEq] at *
  omega