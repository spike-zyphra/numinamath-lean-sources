import Mathlib

theorem number_theory_84195 (n : ℕ) : 9 ∣ n^3 + (n + 1)^3 + (n + 2)^3 := by
  have h1 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by
    omega
  rcases h1 with (h | h | h | h | h | h | h | h | h) <;> simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, pow_succ, h]
  <;> omega