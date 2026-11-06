import Mathlib

theorem number_theory_268366 (n : ℕ) (h : ¬ 7 ∣ n) :
    7 ∣ (n^3 + 1) ∨ 7 ∣ (n^3 - 1) := by
  have h1 : n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by 
    omega
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1)
  · -- case where n ≡ 1
    have h2 : n ^ 3 % 7 = 1 := by
      simp [Nat.pow_mod, h1]
    have : (n ^ 3 - 1) % 7 = 0 := by 
      omega
    right
    exact (Nat.dvd_of_mod_eq_zero this)
  · -- case where n ≡ 2
    have h2 : n ^ 3 % 7 = 1 := by
      simp [Nat.pow_mod, h1]
    have : (n ^ 3 - 1) % 7 = 0 := by 
      omega
    right
    exact (Nat.dvd_of_mod_eq_zero this)
  · -- case where n ≡ 3
    have h2 : n ^ 3 % 7 = 6 := by
      simp [Nat.pow_mod, h1]
    have : (n ^ 3 + 1) % 7 = 0 := by
      omega
    left
    exact (Nat.dvd_of_mod_eq_zero this)
  · -- case where n ≡ 4
    have h2 : n ^ 3 % 7 = 1 := by
      simp [Nat.pow_mod, h1]
    have : (n ^ 3 - 1) % 7 = 0 := by 
      omega
    right
    exact (Nat.dvd_of_mod_eq_zero this)
  · -- case where n ≡ 5
    have h2 : n ^ 3 % 7 = 6 := by
      simp [Nat.pow_mod, h1]
    have : (n ^ 3 + 1) % 7 = 0 := by
      omega
    left
    exact (Nat.dvd_of_mod_eq_zero this)
  · -- case where n ≡ 6
    have h2 : n ^ 3 % 7 = 6 := by
      simp [Nat.pow_mod, h1]
    have : (n ^ 3 + 1) % 7 = 0 := by
      omega
    left
    exact (Nat.dvd_of_mod_eq_zero this)