import Mathlib

theorem number_theory_198389 (m : ℕ) : 6 ∣ m^3 + 11 * m := by 
  have h1 : m % 6 = 0 ∨ m % 6 = 1 ∨ m % 6 = 2 ∨ m % 6 = 3 ∨ m % 6 = 4 ∨ m % 6 = 5 := by
    omega
  rcases h1 with (h | h | h | h | h | h) <;> simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, pow_succ, h] <;> omega