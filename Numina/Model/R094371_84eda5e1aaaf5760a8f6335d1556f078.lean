import Mathlib

theorem number_theory_176104 (n : ℕ) (hn : Odd n) : 8 ∣ n^2 - 1 := by
  have h1 : n % 2 = 1 := by
    rcases hn with ⟨k, hk⟩
    omega
  have h2 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    have h1' : n % 2 = 1 := h1
    omega
  rcases h2 with (h | h | h | h)
  · -- Case where n % 8 = 1
    simp [Nat.dvd_iff_mod_eq_zero, Nat.sub_mod_eq_zero_of_mod_eq, Nat.pow_mod, h]
  · -- Case where n % 8 = 3
    simp [Nat.dvd_iff_mod_eq_zero, Nat.sub_mod_eq_zero_of_mod_eq, Nat.pow_mod, h]
  · -- Case where n % 8 = 5
    simp [Nat.dvd_iff_mod_eq_zero, Nat.sub_mod_eq_zero_of_mod_eq, Nat.pow_mod, h]
  · -- Case where n % 8 = 7
    simp [Nat.dvd_iff_mod_eq_zero, Nat.sub_mod_eq_zero_of_mod_eq, Nat.pow_mod, h]