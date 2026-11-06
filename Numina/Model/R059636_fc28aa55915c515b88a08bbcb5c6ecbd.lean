import Mathlib

theorem number_theory_275841 (n : ℕ) (h : Odd n) : 8 ∣ (n ^ 2 - 1) := by
  have h3 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    rcases h with ⟨k, hk⟩
    have : n % 2 = 1 := by omega
    omega
  rcases h3 with (h3 | h3 | h3 | h3)
  · -- n ≡ 1 mod 8
    have h4 : (n ^ 2) % 8 = 1 := by
      simp [Nat.pow_mod, h3]
    have h5 : (n ^ 2 - 1) % 8 = 0 := by 
      omega
    exact Nat.dvd_of_mod_eq_zero h5
  · -- n ≡ 3 mod 8
    have h4 : (n ^ 2) % 8 = 1 := by
      simp [Nat.pow_mod, h3]
    have h5 : (n ^ 2 - 1) % 8 = 0 := by 
      omega
    exact Nat.dvd_of_mod_eq_zero h5
  · -- n ≡ 5 mod 8
    have h4 : (n ^ 2) % 8 = 1 := by
      simp [Nat.pow_mod, h3]
    have h5 : (n ^ 2 - 1) % 8 = 0 := by 
      omega
    exact Nat.dvd_of_mod_eq_zero h5
  · -- n ≡ 7 mod 8
    have h4 : (n ^ 2) % 8 = 1 := by
      simp [Nat.pow_mod, h3]
    have h5 : (n ^ 2 - 1) % 8 = 0 := by 
      omega
    exact Nat.dvd_of_mod_eq_zero h5