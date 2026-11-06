import Mathlib

theorem number_theory_173664 (n : ℕ) (h : Even n) : 24 ∣ n * (n + 1) * (n + 2) := by
  have h1 : n % 2 = 0 := by
    rcases h with ⟨k, hk⟩
    omega
  have h2 : (n * (n + 1) * (n + 2)) % 24 = 0 := by
    have h3' : n % 2 = 0 := h1
    have h8 : (n * (n + 1) * (n + 2)) % 8 = 0 := by
      have h4 : n % 8 = 0 ∨ n % 8 = 2 ∨ n % 8 = 4 ∨ n % 8 = 6 := by
        omega
      rcases h4 with (h | h | h | h)
      · -- n ≡ 0 [MOD 8]
        simp [Nat.mul_mod, Nat.add_mod, h] at *
      · -- n ≡ 2 [MOD 8]
        simp [Nat.mul_mod, Nat.add_mod, h] at *
      · -- n ≡ 4 [MOD 8]
        simp [Nat.mul_mod, Nat.add_mod, h] at *
      · -- n ≡ 6 [MOD 8]
        simp [Nat.mul_mod, Nat.add_mod, h] at *
    have h3 : (n * (n + 1) * (n + 2)) % 3 = 0 := by
      have h5 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by 
        omega
      rcases h5 with (h | h | h)
      · -- n ≡ 0 [MOD 3]
        simp [Nat.mul_mod, Nat.add_mod, h] at *
      · -- n ≡ 1 [MOD 3]
        simp [Nat.mul_mod, Nat.add_mod, h] at *
      · -- n ≡ 2 [MOD 3]
        simp [Nat.mul_mod, Nat.add_mod, h] at *
    omega
  exact Nat.dvd_of_mod_eq_zero h2