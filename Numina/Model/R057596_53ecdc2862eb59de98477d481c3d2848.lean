import Mathlib

theorem number_theory_203605 (n : ℕ) : 12 ∣ n^4 - n^2 := by
  have h1 : (n ^ 4) % 3 = (n ^ 2) % 3 := by 
    have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by 
      omega
    rcases h2 with (h | h | h)
    · -- Case n % 3 = 0
      simp [Nat.pow_mod, h]
    · -- Case n % 3 = 1
      simp [Nat.pow_mod, h]
    · -- Case n % 3 = 2
      simp [Nat.pow_mod, h]
  have h3 : (n ^ 4 - n ^ 2) % 3 = 0 := by
    omega
  have h4 : (n ^ 4) % 4 = (n ^ 2) % 4 := by
    have h5 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by 
      omega
    rcases h5 with (h | h | h | h)
    · -- Case n % 4 = 0
      simp [Nat.pow_mod, h]
    · -- Case n % 4 = 1
      simp [Nat.pow_mod, h]
    · -- Case n % 4 = 2
      simp [Nat.pow_mod, h]
    · -- Case n % 4 = 3
      simp [Nat.pow_mod, h]
  have h6 : (n ^ 4 - n ^ 2) % 4 = 0 := by
    omega
  have h7 : (n ^ 4 - n ^ 2) % 12 = 0 := by 
    omega
  exact Nat.dvd_of_mod_eq_zero h7