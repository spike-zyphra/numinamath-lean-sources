import Mathlib

theorem number_theory_311150 (n : ℕ) (hn : n > 0) :
    9 ∣ n^3 + (n+1)^3 + (n+2)^3 := by
  have h1 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by 
    omega
  rcases h1 with (h | h | h | h | h | h | h | h | h)
  · -- Case where n ≡ 0 (mod 9)
    have h2 : (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) % 9 = 0 := by
      simp [Nat.add_mod, Nat.mul_mod, pow_three, h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      all_goals omega
    exact Nat.dvd_of_mod_eq_zero h2
  · -- Case where n ≡ 1 (mod 9)
    have h2 : (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) % 9 = 0 := by
      simp [Nat.add_mod, Nat.mul_mod, pow_three, h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      all_goals omega
    exact Nat.dvd_of_mod_eq_zero h2
  · -- Case where n ≡ 2 (mod 9)
    have h2 : (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) % 9 = 0 := by
      simp [Nat.add_mod, Nat.mul_mod, pow_three, h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      all_goals omega
    exact Nat.dvd_of_mod_eq_zero h2
  · -- Case where n ≡ 3 (mod 9)
    have h2 : (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) % 9 = 0 := by
      simp [Nat.add_mod, Nat.mul_mod, pow_three, h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      all_goals omega
    exact Nat.dvd_of_mod_eq_zero h2
  · -- Case where n ≡ 4 (mod 9)
    have h2 : (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) % 9 = 0 := by
      simp [Nat.add_mod, Nat.mul_mod, pow_three, h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      all_goals omega
    exact Nat.dvd_of_mod_eq_zero h2
  · -- Case where n ≡ 5 (mod 9)
    have h2 : (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) % 9 = 0 := by
      simp [Nat.add_mod, Nat.mul_mod, pow_three, h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      all_goals omega
    exact Nat.dvd_of_mod_eq_zero h2
  · -- Case where n ≡ 6 (mod 9)
    have h2 : (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) % 9 = 0 := by
      simp [Nat.add_mod, Nat.mul_mod, pow_three, h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      all_goals omega
    exact Nat.dvd_of_mod_eq_zero h2
  · -- Case where n ≡ 7 (mod 9)
    have h2 : (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) % 9 = 0 := by
      simp [Nat.add_mod, Nat.mul_mod, pow_three, h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      all_goals omega
    exact Nat.dvd_of_mod_eq_zero h2
  · -- Case where n ≡ 8 (mod 9)
    have h2 : (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) % 9 = 0 := by
      simp [Nat.add_mod, Nat.mul_mod, pow_three, h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      all_goals omega
    exact Nat.dvd_of_mod_eq_zero h2