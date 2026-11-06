import Mathlib

theorem number_theory_323380 (n : ℕ) (h : ¬ 5 ∣ n) :
    5 ∣ (n ^ 2 + 1) ∨ 5 ∣ (n ^ 2 - 1) := by
  have h1 : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
    omega
  rcases h1 with (h1 | h1 | h1 | h1)
  · -- case n ≡ 1 (mod 5)
    have h2 : (n ^ 2) % 5 = 1 := by
      have : n % 5 = 1 := by omega
      norm_num [Nat.pow_mod, this]
    have h3 : (n ^ 2 - 1) % 5 = 0 := by
      omega
    right
    exact Nat.dvd_of_mod_eq_zero h3
  · -- case n ≡ 2 (mod 5)
    have h2 : (n ^ 2) % 5 = 4 := by
      have : n % 5 = 2 := by omega
      norm_num [Nat.pow_mod, this]
    have h3 : (n ^ 2 + 1) % 5 = 0 := by
      omega
    left
    exact Nat.dvd_of_mod_eq_zero h3
  · -- case n ≡ 3 (mod 5)
    have h2 : (n ^ 2) % 5 = 4 := by
      have : n % 5 = 3 := by omega
      norm_num [Nat.pow_mod, this]
    have h3 : (n ^ 2 + 1) % 5 = 0 := by
      omega
    left
    exact Nat.dvd_of_mod_eq_zero h3
  · -- case n ≡ 4 (mod 5)
    have h2 : (n ^ 2) % 5 = 1 := by
      have : n % 5 = 4 := by omega
      norm_num [Nat.pow_mod, this]
    have h3 : (n ^ 2 - 1) % 5 = 0 := by
      omega
    right
    exact Nat.dvd_of_mod_eq_zero h3