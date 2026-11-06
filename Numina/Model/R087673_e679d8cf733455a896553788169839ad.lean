import Mathlib

theorem number_theory_127924 (n : ℕ) : 6 ∣ n^3 - 7 * n := by
  have h1 : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by 
    omega
  rcases h1 with (h | h | h | h | h | h) <;> ( 
    simp [Nat.dvd_iff_mod_eq_zero, Nat.sub_mod_eq_zero_of_mod_eq, Nat.mul_mod, Nat.pow_mod, h, Nat.mod_self]
    <;> omega
  )